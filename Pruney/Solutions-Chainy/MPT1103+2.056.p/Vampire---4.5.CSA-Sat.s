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
% DateTime   : Thu Dec  3 13:08:41 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   30 (  30 expanded)
%              Number of leaves         :   30 (  30 expanded)
%              Depth                    :    0
%              Number of atoms          :   42 (  42 expanded)
%              Number of equality atoms :   29 (  29 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u213,negated_conjecture,
    ( ~ ( k2_struct_0(sK0) != sK1 )
    | k2_struct_0(sK0) != sK1 )).

tff(u212,axiom,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 )).

tff(u211,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,k7_subset_1(X0,X0,X1)) = k7_subset_1(X0,X0,k3_xboole_0(X0,X1)) )).

tff(u210,axiom,(
    ! [X3,X2] : k7_subset_1(X2,X2,k7_subset_1(X2,X2,X3)) = k3_xboole_0(X2,X3) )).

tff(u209,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k7_subset_1(X0,X0,k3_xboole_0(X0,X1))) )).

tff(u208,negated_conjecture,(
    ! [X1] : k3_xboole_0(sK1,X1) = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(sK1,sK1,X1)) )).

tff(u207,negated_conjecture,(
    ! [X1] : k3_xboole_0(sK1,X1) = k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,X1)) )).

tff(u206,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u205,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X1,X1,X2) )).

tff(u204,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

tff(u203,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) )).

tff(u202,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

tff(u201,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u200,axiom,(
    ! [X1] : k1_xboole_0 = k7_subset_1(X1,X1,X1) )).

tff(u199,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u198,axiom,(
    ! [X0] : k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

tff(u197,negated_conjecture,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

tff(u196,negated_conjecture,(
    u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

tff(u195,negated_conjecture,(
    sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )).

tff(u194,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) )).

tff(u193,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) )).

tff(u192,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) )).

tff(u191,negated_conjecture,
    ( ~ ~ r1_tarski(k2_struct_0(sK0),sK1)
    | ~ r1_tarski(k2_struct_0(sK0),sK1) )).

tff(u190,axiom,(
    ! [X1] : r1_tarski(X1,X1) )).

tff(u189,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
      | ~ l1_struct_0(X0) ) )).

tff(u188,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) ) )).

tff(u187,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u186,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

tff(u185,axiom,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0))) ) )).

tff(u184,negated_conjecture,(
    l1_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:43:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.43  % (27560)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.45  % (27552)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.47  % (27568)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.48  % (27568)Refutation not found, incomplete strategy% (27568)------------------------------
% 0.20/0.48  % (27568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (27568)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (27568)Memory used [KB]: 10618
% 0.20/0.49  % (27568)Time elapsed: 0.097 s
% 0.20/0.49  % (27568)------------------------------
% 0.20/0.49  % (27568)------------------------------
% 0.20/0.51  % (27558)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (27557)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (27556)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (27555)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (27554)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (27564)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.54  % (27575)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.54  % (27558)# SZS output start Saturation.
% 0.20/0.54  tff(u213,negated_conjecture,
% 0.20/0.54      ((~(k2_struct_0(sK0) != sK1)) | (k2_struct_0(sK0) != sK1))).
% 0.20/0.54  
% 0.20/0.54  tff(u212,axiom,
% 0.20/0.54      (![X0] : ((k3_xboole_0(X0,X0) = X0)))).
% 0.20/0.54  
% 0.20/0.54  tff(u211,axiom,
% 0.20/0.54      (![X1, X0] : ((k3_xboole_0(X0,k7_subset_1(X0,X0,X1)) = k7_subset_1(X0,X0,k3_xboole_0(X0,X1)))))).
% 0.20/0.54  
% 0.20/0.54  tff(u210,axiom,
% 0.20/0.54      (![X3, X2] : ((k7_subset_1(X2,X2,k7_subset_1(X2,X2,X3)) = k3_xboole_0(X2,X3))))).
% 0.20/0.54  
% 0.20/0.54  tff(u209,axiom,
% 0.20/0.54      (![X1, X0] : ((k3_xboole_0(X0,X1) = k5_xboole_0(X0,k7_subset_1(X0,X0,k3_xboole_0(X0,X1))))))).
% 0.20/0.54  
% 0.20/0.54  tff(u208,negated_conjecture,
% 0.20/0.54      (![X1] : ((k3_xboole_0(sK1,X1) = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(sK1,sK1,X1)))))).
% 0.20/0.54  
% 0.20/0.54  tff(u207,negated_conjecture,
% 0.20/0.54      (![X1] : ((k3_xboole_0(sK1,X1) = k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,X1)))))).
% 0.20/0.54  
% 0.20/0.54  tff(u206,axiom,
% 0.20/0.54      (![X0] : ((k5_xboole_0(X0,k1_xboole_0) = X0)))).
% 0.20/0.54  
% 0.20/0.54  tff(u205,axiom,
% 0.20/0.54      (![X1, X2] : ((k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X1,X1,X2))))).
% 0.20/0.54  
% 0.20/0.54  tff(u204,axiom,
% 0.20/0.54      (![X0] : ((k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0))))).
% 0.20/0.54  
% 0.20/0.54  tff(u203,axiom,
% 0.20/0.54      (![X0] : ((k1_xboole_0 = k5_xboole_0(X0,X0))))).
% 0.20/0.54  
% 0.20/0.54  tff(u202,negated_conjecture,
% 0.20/0.54      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)))).
% 0.20/0.54  
% 0.20/0.54  tff(u201,negated_conjecture,
% 0.20/0.54      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 0.20/0.54  
% 0.20/0.54  tff(u200,axiom,
% 0.20/0.54      (![X1] : ((k1_xboole_0 = k7_subset_1(X1,X1,X1))))).
% 0.20/0.54  
% 0.20/0.54  tff(u199,axiom,
% 0.20/0.54      (![X0] : ((k2_subset_1(X0) = X0)))).
% 0.20/0.54  
% 0.20/0.54  tff(u198,axiom,
% 0.20/0.54      (![X0] : ((k7_subset_1(X0,X0,k1_xboole_0) = X0)))).
% 0.20/0.54  
% 0.20/0.54  tff(u197,negated_conjecture,
% 0.20/0.54      (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0))))).
% 0.20/0.54  
% 0.20/0.54  tff(u196,negated_conjecture,
% 0.20/0.54      (u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))))).
% 0.20/0.54  
% 0.20/0.54  tff(u195,negated_conjecture,
% 0.20/0.54      (sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0))).
% 0.20/0.54  
% 0.20/0.54  tff(u194,negated_conjecture,
% 0.20/0.54      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)))).
% 0.20/0.54  
% 0.20/0.54  tff(u193,axiom,
% 0.20/0.54      (![X1, X0] : ((~r1_tarski(X1,X0) | (X0 = X1) | ~r1_tarski(X0,X1))))).
% 0.20/0.54  
% 0.20/0.54  tff(u192,axiom,
% 0.20/0.54      (![X1, X0] : ((~r1_tarski(X0,X1) | (k3_xboole_0(X0,X1) = X0))))).
% 0.20/0.54  
% 0.20/0.54  tff(u191,negated_conjecture,
% 0.20/0.54      ((~~r1_tarski(k2_struct_0(sK0),sK1)) | ~r1_tarski(k2_struct_0(sK0),sK1))).
% 0.20/0.54  
% 0.20/0.54  tff(u190,axiom,
% 0.20/0.54      (![X1] : (r1_tarski(X1,X1)))).
% 0.20/0.54  
% 0.20/0.54  tff(u189,axiom,
% 0.20/0.54      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1) | ~l1_struct_0(X0))))).
% 0.20/0.54  
% 0.20/0.54  tff(u188,axiom,
% 0.20/0.54      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)))))).
% 0.20/0.54  
% 0.20/0.54  tff(u187,negated_conjecture,
% 0.20/0.54      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.54  
% 0.20/0.54  tff(u186,axiom,
% 0.20/0.54      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 0.20/0.54  
% 0.20/0.54  tff(u185,axiom,
% 0.20/0.54      (![X0] : ((~l1_struct_0(X0) | (u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0)))))))).
% 0.20/0.54  
% 0.20/0.54  tff(u184,negated_conjecture,
% 0.20/0.54      l1_struct_0(sK0)).
% 0.20/0.54  
% 0.20/0.54  % (27558)# SZS output end Saturation.
% 0.20/0.54  % (27558)------------------------------
% 0.20/0.54  % (27558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (27558)Termination reason: Satisfiable
% 0.20/0.54  
% 0.20/0.54  % (27558)Memory used [KB]: 10746
% 0.20/0.54  % (27558)Time elapsed: 0.130 s
% 0.20/0.54  % (27558)------------------------------
% 0.20/0.54  % (27558)------------------------------
% 0.20/0.54  % (27551)Success in time 0.176 s
%------------------------------------------------------------------------------
