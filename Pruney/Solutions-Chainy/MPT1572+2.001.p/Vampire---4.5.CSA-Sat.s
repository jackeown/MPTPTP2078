%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:19 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   13 (  13 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    0
%              Number of atoms          :   26 (  26 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    5 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u61,negated_conjecture,
    ( ~ sP1(sK4,sK3)
    | ~ r1_yellow_0(sK3,sK4) )).

tff(u60,axiom,(
    ! [X1,X0] :
      ( ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) )).

tff(u59,axiom,(
    ! [X1,X0] :
      ( r1_yellow_0(X1,k3_xboole_0(X0,u1_struct_0(X1)))
      | ~ sP1(X0,X1) ) )).

tff(u58,negated_conjecture,
    ( ~ ~ r2_yellow_0(sK3,sK4)
    | ~ r2_yellow_0(sK3,sK4) )).

tff(u57,negated_conjecture,
    ( ~ ~ r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)))
    | ~ r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) )).

tff(u56,axiom,(
    ! [X1,X0] :
      ( ~ r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
      | ~ sP2(X0,X1) ) )).

tff(u55,negated_conjecture,
    ( ~ ~ sP0(sK3,sK4)
    | ~ sP0(sK3,sK4) )).

tff(u54,axiom,(
    ! [X1,X0] :
      ( ~ sP0(X0,X1)
      | r1_yellow_0(X0,X1) ) )).

tff(u53,axiom,(
    ! [X1,X0] :
      ( ~ sP1(X1,X0)
      | ~ sP0(X0,X1) ) )).

tff(u52,axiom,(
    ! [X1,X0] :
      ( ~ sP1(X0,X1)
      | ~ r1_yellow_0(X1,X0) ) )).

tff(u51,negated_conjecture,
    ( ~ sP1(sK4,sK3)
    | sP1(sK4,sK3) )).

tff(u50,negated_conjecture,
    ( ~ ~ sP2(sK3,sK4)
    | ~ sP2(sK3,sK4) )).

tff(u49,axiom,(
    ! [X1,X0] :
      ( ~ sP2(X0,X1)
      | r2_yellow_0(X0,X1) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n003.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:23:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (13675)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.22/0.48  % (13666)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.22/0.48  % (13663)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.22/0.48  % (13663)Refutation not found, incomplete strategy% (13663)------------------------------
% 0.22/0.48  % (13663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (13663)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (13663)Memory used [KB]: 5245
% 0.22/0.48  % (13663)Time elapsed: 0.070 s
% 0.22/0.48  % (13663)------------------------------
% 0.22/0.48  % (13663)------------------------------
% 0.22/0.49  % (13670)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.22/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.49  % (13670)# SZS output start Saturation.
% 0.22/0.49  tff(u61,negated_conjecture,
% 0.22/0.49      ((~sP1(sK4,sK3)) | ~r1_yellow_0(sK3,sK4))).
% 0.22/0.49  
% 0.22/0.49  tff(u60,axiom,
% 0.22/0.49      (![X1, X0] : ((~r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) | ~sP0(X0,X1))))).
% 0.22/0.49  
% 0.22/0.49  tff(u59,axiom,
% 0.22/0.49      (![X1, X0] : ((r1_yellow_0(X1,k3_xboole_0(X0,u1_struct_0(X1))) | ~sP1(X0,X1))))).
% 0.22/0.49  
% 0.22/0.49  tff(u58,negated_conjecture,
% 0.22/0.49      ((~~r2_yellow_0(sK3,sK4)) | ~r2_yellow_0(sK3,sK4))).
% 0.22/0.49  
% 0.22/0.49  tff(u57,negated_conjecture,
% 0.22/0.49      ((~~r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)))) | ~r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))))).
% 0.22/0.49  
% 0.22/0.49  tff(u56,axiom,
% 0.22/0.49      (![X1, X0] : ((~r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) | ~sP2(X0,X1))))).
% 0.22/0.49  
% 0.22/0.49  tff(u55,negated_conjecture,
% 0.22/0.49      ((~~sP0(sK3,sK4)) | ~sP0(sK3,sK4))).
% 0.22/0.49  
% 0.22/0.49  tff(u54,axiom,
% 0.22/0.49      (![X1, X0] : ((~sP0(X0,X1) | r1_yellow_0(X0,X1))))).
% 0.22/0.49  
% 0.22/0.49  tff(u53,axiom,
% 0.22/0.49      (![X1, X0] : ((~sP1(X1,X0) | ~sP0(X0,X1))))).
% 0.22/0.49  
% 0.22/0.49  tff(u52,axiom,
% 0.22/0.49      (![X1, X0] : ((~sP1(X0,X1) | ~r1_yellow_0(X1,X0))))).
% 0.22/0.49  
% 0.22/0.49  tff(u51,negated_conjecture,
% 0.22/0.49      ((~sP1(sK4,sK3)) | sP1(sK4,sK3))).
% 0.22/0.49  
% 0.22/0.49  tff(u50,negated_conjecture,
% 0.22/0.49      ((~~sP2(sK3,sK4)) | ~sP2(sK3,sK4))).
% 0.22/0.49  
% 0.22/0.49  tff(u49,axiom,
% 0.22/0.49      (![X1, X0] : ((~sP2(X0,X1) | r2_yellow_0(X0,X1))))).
% 0.22/0.49  
% 0.22/0.49  % (13670)# SZS output end Saturation.
% 0.22/0.49  % (13670)------------------------------
% 0.22/0.49  % (13670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (13670)Termination reason: Satisfiable
% 0.22/0.49  
% 0.22/0.49  % (13670)Memory used [KB]: 5373
% 0.22/0.49  % (13670)Time elapsed: 0.074 s
% 0.22/0.49  % (13670)------------------------------
% 0.22/0.49  % (13670)------------------------------
% 0.22/0.49  % (13661)Success in time 0.127 s
%------------------------------------------------------------------------------
