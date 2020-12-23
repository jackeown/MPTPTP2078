%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:48 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :    6 (   6 expanded)
%              Number of leaves         :    6 (   6 expanded)
%              Depth                    :    0
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    5 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u40,negated_conjecture,
    ( ~ ( k1_xboole_0 != k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0)) )
    | k1_xboole_0 != k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0)) )).

tff(u39,negated_conjecture,
    ( ~ ( k1_xboole_0 != k4_xboole_0(sK0,sK0) )
    | k1_xboole_0 != k4_xboole_0(sK0,sK0) )).

tff(u38,axiom,(
    ! [X1,X0] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) )).

tff(u37,axiom,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 )).

tff(u36,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) )).

tff(u35,negated_conjecture,
    ( ~ ~ r1_tarski(sK0,sK0)
    | ~ r1_tarski(sK0,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:34:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (23304)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.43  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.43  % (23304)# SZS output start Saturation.
% 0.20/0.43  tff(u40,negated_conjecture,
% 0.20/0.43      ((~(k1_xboole_0 != k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0)))) | (k1_xboole_0 != k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0))))).
% 0.20/0.43  
% 0.20/0.43  tff(u39,negated_conjecture,
% 0.20/0.43      ((~(k1_xboole_0 != k4_xboole_0(sK0,sK0))) | (k1_xboole_0 != k4_xboole_0(sK0,sK0)))).
% 0.20/0.43  
% 0.20/0.43  tff(u38,axiom,
% 0.20/0.43      (![X1, X0] : (((k4_xboole_0(X0,X1) != k1_xboole_0) | r1_tarski(X0,X1))))).
% 0.20/0.43  
% 0.20/0.43  tff(u37,axiom,
% 0.20/0.43      (![X0] : ((k2_xboole_0(X0,X0) = X0)))).
% 0.20/0.43  
% 0.20/0.43  tff(u36,axiom,
% 0.20/0.43      (![X1, X0] : ((~r1_tarski(X0,X1) | (k4_xboole_0(X0,X1) = k1_xboole_0))))).
% 0.20/0.43  
% 0.20/0.43  tff(u35,negated_conjecture,
% 0.20/0.43      ((~~r1_tarski(sK0,sK0)) | ~r1_tarski(sK0,sK0))).
% 0.20/0.43  
% 0.20/0.43  % (23304)# SZS output end Saturation.
% 0.20/0.43  % (23304)------------------------------
% 0.20/0.43  % (23304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (23304)Termination reason: Satisfiable
% 0.20/0.43  
% 0.20/0.43  % (23304)Memory used [KB]: 6012
% 0.20/0.43  % (23304)Time elapsed: 0.003 s
% 0.20/0.43  % (23304)------------------------------
% 0.20/0.43  % (23304)------------------------------
% 0.20/0.43  % (23297)Success in time 0.076 s
%------------------------------------------------------------------------------
