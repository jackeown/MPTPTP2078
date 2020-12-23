%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:11 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :    4 (   4 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    0
%              Number of atoms          :   12 (  12 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    8 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u35,negated_conjecture,
    ( ~ ( sK0 != k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) )
    | sK0 != k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) )).

tff(u34,axiom,
    ( ~ ! [X1,X0] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)
    | ! [X1,X0] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) )).

tff(u33,axiom,
    ( ~ ! [X1,X0,X2] :
          ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
          | r1_tarski(X0,X1) )
    | ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
        | r1_tarski(X0,X1) ) )).

tff(u32,axiom,
    ( ~ ! [X1,X0] :
          ( ~ r1_tarski(X0,X1)
          | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 )
    | ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:00:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (5618)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.42  % (5619)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.42  % (5619)# SZS output start Saturation.
% 0.21/0.42  tff(u35,negated_conjecture,
% 0.21/0.42      ((~(sK0 != k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)))) | (sK0 != k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))))).
% 0.21/0.42  
% 0.21/0.42  tff(u34,axiom,
% 0.21/0.42      ((~(![X1, X0] : ((k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1))))) | (![X1, X0] : ((k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)))))).
% 0.21/0.42  
% 0.21/0.42  tff(u33,axiom,
% 0.21/0.42      ((~(![X1, X0, X2] : ((~r1_tarski(X0,k3_xboole_0(X1,X2)) | r1_tarski(X0,X1))))) | (![X1, X0, X2] : ((~r1_tarski(X0,k3_xboole_0(X1,X2)) | r1_tarski(X0,X1)))))).
% 0.21/0.42  
% 0.21/0.42  tff(u32,axiom,
% 0.21/0.42      ((~(![X1, X0] : ((~r1_tarski(X0,X1) | (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1))))) | (![X1, X0] : ((~r1_tarski(X0,X1) | (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)))))).
% 0.21/0.42  
% 0.21/0.42  % (5619)# SZS output end Saturation.
% 0.21/0.42  % (5619)------------------------------
% 0.21/0.42  % (5619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (5619)Termination reason: Satisfiable
% 0.21/0.42  
% 0.21/0.42  % (5619)Memory used [KB]: 10490
% 0.21/0.42  % (5619)Time elapsed: 0.004 s
% 0.21/0.42  % (5619)------------------------------
% 0.21/0.42  % (5619)------------------------------
% 0.21/0.42  % (5613)Success in time 0.061 s
%------------------------------------------------------------------------------
