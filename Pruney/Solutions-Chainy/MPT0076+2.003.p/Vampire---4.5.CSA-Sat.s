%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:41 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   13 (  13 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    0
%              Number of atoms          :   33 (  33 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u59,negated_conjecture,
    ( ~ ( k1_xboole_0 != sK1 )
    | k1_xboole_0 != sK1 )).

tff(u58,negated_conjecture,(
    ~ v1_xboole_0(sK1) )).

tff(u57,axiom,(
    v1_xboole_0(k1_xboole_0) )).

tff(u56,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ r1_tarski(sK1,X0)
          | ~ r1_xboole_0(sK0,X0) )
    | ~ r1_xboole_0(sK0,sK0) )).

tff(u55,negated_conjecture,(
    r1_xboole_0(sK1,sK0) )).

tff(u54,axiom,(
    ! [X1,X0,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) )).

tff(u53,axiom,(
    ! [X1,X0] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) )).

tff(u52,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X1)
      | k1_xboole_0 = X0 ) )).

tff(u51,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | k1_xboole_0 = X0 ) )).

tff(u50,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ r1_tarski(sK1,X0)
          | ~ r1_xboole_0(X0,sK0) )
    | ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | ~ r1_xboole_0(X0,sK0) ) )).

tff(u49,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ r1_tarski(sK1,X0)
          | ~ r1_xboole_0(sK0,X0) )
    | ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | ~ r1_xboole_0(sK0,X0) ) )).

tff(u48,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ r1_tarski(sK1,X0)
          | ~ r1_xboole_0(sK0,X0) )
    | ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | ~ r1_xboole_0(X0,sK0) ) )).

tff(u47,negated_conjecture,(
    r1_tarski(sK1,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:06:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (21420)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.41  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.42  % (21420)# SZS output start Saturation.
% 0.21/0.42  tff(u59,negated_conjecture,
% 0.21/0.42      ((~(k1_xboole_0 != sK1)) | (k1_xboole_0 != sK1))).
% 0.21/0.42  
% 0.21/0.42  tff(u58,negated_conjecture,
% 0.21/0.42      ~v1_xboole_0(sK1)).
% 0.21/0.42  
% 0.21/0.42  tff(u57,axiom,
% 0.21/0.42      v1_xboole_0(k1_xboole_0)).
% 0.21/0.42  
% 0.21/0.42  tff(u56,negated_conjecture,
% 0.21/0.42      ((~(![X0] : ((~r1_tarski(sK1,X0) | ~r1_xboole_0(sK0,X0))))) | ~r1_xboole_0(sK0,sK0))).
% 0.21/0.42  
% 0.21/0.42  tff(u55,negated_conjecture,
% 0.21/0.42      r1_xboole_0(sK1,sK0)).
% 0.21/0.42  
% 0.21/0.42  tff(u54,axiom,
% 0.21/0.42      (![X1, X0, X2] : ((r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))))).
% 0.21/0.42  
% 0.21/0.42  tff(u53,axiom,
% 0.21/0.42      (![X1, X0] : ((r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))))).
% 0.21/0.42  
% 0.21/0.42  tff(u52,axiom,
% 0.21/0.42      (![X1, X0] : ((~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X1) | (k1_xboole_0 = X0))))).
% 0.21/0.42  
% 0.21/0.42  tff(u51,axiom,
% 0.21/0.42      (![X1, X0, X2] : ((~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | ~r1_xboole_0(X1,X2) | (k1_xboole_0 = X0))))).
% 0.21/0.42  
% 0.21/0.42  tff(u50,negated_conjecture,
% 0.21/0.42      ((~(![X0] : ((~r1_tarski(sK1,X0) | ~r1_xboole_0(X0,sK0))))) | (![X0] : ((~r1_tarski(sK1,X0) | ~r1_xboole_0(X0,sK0)))))).
% 0.21/0.42  
% 0.21/0.42  tff(u49,negated_conjecture,
% 0.21/0.42      ((~(![X0] : ((~r1_tarski(sK1,X0) | ~r1_xboole_0(sK0,X0))))) | (![X0] : ((~r1_tarski(sK1,X0) | ~r1_xboole_0(sK0,X0)))))).
% 0.21/0.42  
% 0.21/0.42  tff(u48,negated_conjecture,
% 0.21/0.42      ((~(![X0] : ((~r1_tarski(sK1,X0) | ~r1_xboole_0(sK0,X0))))) | (![X0] : ((~r1_tarski(sK0,X0) | ~r1_xboole_0(X0,sK0)))))).
% 0.21/0.42  
% 0.21/0.42  tff(u47,negated_conjecture,
% 0.21/0.42      r1_tarski(sK1,sK0)).
% 0.21/0.42  
% 0.21/0.42  % (21420)# SZS output end Saturation.
% 0.21/0.42  % (21420)------------------------------
% 0.21/0.42  % (21420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (21420)Termination reason: Satisfiable
% 0.21/0.42  
% 0.21/0.42  % (21420)Memory used [KB]: 10490
% 0.21/0.42  % (21420)Time elapsed: 0.005 s
% 0.21/0.42  % (21420)------------------------------
% 0.21/0.42  % (21420)------------------------------
% 0.21/0.42  % (21419)Success in time 0.062 s
%------------------------------------------------------------------------------
