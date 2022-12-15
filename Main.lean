import Runtime

lf {
  reactor check
    parameters  []
    inputs      []
    outputs     []
    actions     [act : Unit]
    state       [s : Int := 0]
    timers      [
      {
        name   t
        offset 0
        period 0
      }
    ]
    nested      [
      a : ScheduleLogicalAction := []
    ]
    connections []
    reactions   [
      {
        kind          pure
        portSources   []
        portEffects   [a.x]
        actionSources []
        actionEffects [act]
        triggers {
           ports   []
           actions []
           timers  [t]
           meta    []
        }
        body {
          setOutput .a.x 1
          setState .s (-1)
          schedule .act 0 ()
        }
      }
    ]

  reactor ScheduleLogicalAction
    parameters  []
    inputs      [x : Nat]
    outputs     []
    actions     [a : Unit]
    state       []
    timers      []
    nested      []
    connections []
    reactions   [
      {
        kind          pure
        portSources   [x]
        portEffects   []
        actionSources []
        actionEffects [a]
        triggers {
           ports   [x]
           actions []
           timers  []
           meta    []
        }
        body {
          schedule a (Time.of 200 .ms) ()
        }
      },
      {
        kind          impure
        portSources   []
        portEffects   []
        actionSources [a]
        actionEffects []
        triggers {
           ports   []
           actions [a]
           timers  []
           meta    []
        }
        body {
          let elapsedTime <- getLogicalTime
          sorry
        }
      }
    ]
  schedule [

  ]
}
