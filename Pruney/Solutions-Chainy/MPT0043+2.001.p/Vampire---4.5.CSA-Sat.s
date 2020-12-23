%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:49 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :    7 (   7 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    0
%              Number of atoms          :   24 (  24 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u57,axiom,
    ( ~ ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u56,negated_conjecture,
    ( ~ ~ r1_tarski(k4_xboole_0(sK0,sK1),sK0)
    | ~ r1_tarski(k4_xboole_0(sK0,sK1),sK0) )).

tff(u55,negated_conjecture,
    ( ~ ~ r1_tarski(sK0,sK0)
    | ~ r1_tarski(sK0,sK0) )).

tff(u54,axiom,
    ( ~ ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ! [X0] : r1_tarski(k1_xboole_0,X0) )).

tff(u53,axiom,
    ( ~ ! [X1,X3,X0,X2] :
          ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
          | ~ r1_tarski(X2,X3)
          | ~ r1_tarski(X0,X1) )
    | ! [X1,X3,X0,X2] :
        ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X0,X1) ) )).

tff(u52,axiom,
    ( ~ ! [X1,X0,X2] :
          ( r1_tarski(k4_xboole_0(X1,X2),X0)
          | ~ r1_tarski(X1,X0) )
    | ! [X1,X0,X2] :
        ( r1_tarski(k4_xboole_0(X1,X2),X0)
        | ~ r1_tarski(X1,X0) ) )).

tff(u51,axiom,
    ( ~ ! [X1,X0,X2] :
          ( r1_tarski(X0,k4_xboole_0(X1,X2))
          | ~ r1_tarski(X2,k1_xboole_0)
          | ~ r1_tarski(X0,X1) )
    | ! [X1,X0,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
        | ~ r1_tarski(X2,k1_xboole_0)
        | ~ r1_tarski(X0,X1) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:58:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (4115)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.42  % (4118)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.22/0.43  % (4119)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.43  % (4110)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.43  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.43  % (4119)# SZS output start Saturation.
% 0.22/0.43  tff(u57,axiom,
% 0.22/0.43      ((~(![X0] : ((k4_xboole_0(X0,k1_xboole_0) = X0)))) | (![X0] : ((k4_xboole_0(X0,k1_xboole_0) = X0))))).
% 0.22/0.43  
% 0.22/0.43  tff(u56,negated_conjecture,
% 0.22/0.43      ((~~r1_tarski(k4_xboole_0(sK0,sK1),sK0)) | ~r1_tarski(k4_xboole_0(sK0,sK1),sK0))).
% 0.22/0.43  
% 0.22/0.43  tff(u55,negated_conjecture,
% 0.22/0.43      ((~~r1_tarski(sK0,sK0)) | ~r1_tarski(sK0,sK0))).
% 0.22/0.43  
% 0.22/0.43  tff(u54,axiom,
% 0.22/0.43      ((~(![X0] : (r1_tarski(k1_xboole_0,X0)))) | (![X0] : (r1_tarski(k1_xboole_0,X0))))).
% 0.22/0.43  
% 0.22/0.43  tff(u53,axiom,
% 0.22/0.43      ((~(![X1, X3, X0, X2] : ((r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))))) | (![X1, X3, X0, X2] : ((r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))))).
% 0.22/0.43  
% 0.22/0.43  tff(u52,axiom,
% 0.22/0.43      ((~(![X1, X0, X2] : ((r1_tarski(k4_xboole_0(X1,X2),X0) | ~r1_tarski(X1,X0))))) | (![X1, X0, X2] : ((r1_tarski(k4_xboole_0(X1,X2),X0) | ~r1_tarski(X1,X0)))))).
% 0.22/0.43  
% 0.22/0.43  tff(u51,axiom,
% 0.22/0.43      ((~(![X1, X0, X2] : ((r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_tarski(X2,k1_xboole_0) | ~r1_tarski(X0,X1))))) | (![X1, X0, X2] : ((r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_tarski(X2,k1_xboole_0) | ~r1_tarski(X0,X1)))))).
% 0.22/0.43  
% 0.22/0.43  % (4119)# SZS output end Saturation.
% 0.22/0.43  % (4119)------------------------------
% 0.22/0.43  % (4119)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (4119)Termination reason: Satisfiable
% 0.22/0.43  
% 0.22/0.43  % (4119)Memory used [KB]: 6012
% 0.22/0.43  % (4119)Time elapsed: 0.004 s
% 0.22/0.43  % (4119)------------------------------
% 0.22/0.43  % (4119)------------------------------
% 0.22/0.44  % (4108)Success in time 0.074 s
%------------------------------------------------------------------------------
