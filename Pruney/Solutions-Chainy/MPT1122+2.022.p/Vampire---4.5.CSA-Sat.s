%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:20 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   30 (  30 expanded)
%              Number of leaves         :   30 (  30 expanded)
%              Depth                    :    0
%              Number of atoms          :   72 (  72 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u131,negated_conjecture,
    ( ~ ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

tff(u130,axiom,(
    ! [X1,X0] :
      ( k2_pre_topc(X0,X1) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) )).

tff(u129,negated_conjecture,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

tff(u128,axiom,(
    ! [X1,X0,X2] : k7_subset_1(X0,k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X1),X2) )).

tff(u127,negated_conjecture,
    ( sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))
    | sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

tff(u126,negated_conjecture,(
    ! [X0] : k4_xboole_0(u1_struct_0(sK0),X0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0))) )).

tff(u125,axiom,(
    ! [X1,X3,X2] :
      ( ~ r1_tarski(X2,X1)
      | k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) )).

tff(u124,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X1,u1_struct_0(X0))
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
      | ~ l1_struct_0(X0) ) )).

tff(u123,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X1,u1_struct_0(X0))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) )).

tff(u122,negated_conjecture,
    ( ~ ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),u1_struct_0(sK0)) )).

tff(u121,negated_conjecture,(
    ! [X0] :
      ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),u1_struct_0(sK0))
      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),sK0)
      | ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0) ) )).

tff(u120,negated_conjecture,(
    ! [X0] :
      ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),u1_struct_0(sK0))
      | ~ v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),sK0)
      | v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0) ) )).

tff(u119,axiom,(
    ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) )).

tff(u118,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) )).

tff(u117,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) )).

tff(u116,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) )).

tff(u115,negated_conjecture,
    ( ~ ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u114,negated_conjecture,(
    ! [X1] :
      ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X1)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X1),sK0)
      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X1)),sK0) ) )).

tff(u113,negated_conjecture,(
    ! [X0] :
      ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0)
      | ~ v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),sK0) ) )).

tff(u112,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u111,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) )).

tff(u110,axiom,(
    ! [X1,X0] :
      ( ~ l1_pre_topc(X0)
      | k4_xboole_0(u1_struct_0(X0),X1) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k4_xboole_0(u1_struct_0(X0),X1))) ) )).

tff(u109,negated_conjecture,(
    l1_pre_topc(sK0) )).

tff(u108,negated_conjecture,
    ( ~ ~ v4_pre_topc(sK1,sK0)
    | ~ v4_pre_topc(sK1,sK0) )).

tff(u107,axiom,(
    ! [X1,X0] :
      ( ~ v4_pre_topc(k4_xboole_0(u1_struct_0(X0),X1),X0)
      | k4_xboole_0(u1_struct_0(X0),X1) = k2_pre_topc(X0,k4_xboole_0(u1_struct_0(X0),X1))
      | ~ l1_pre_topc(X0) ) )).

tff(u106,axiom,(
    ! [X1,X0] :
      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) )).

tff(u105,negated_conjecture,
    ( ~ v3_pre_topc(sK1,sK0)
    | v3_pre_topc(sK1,sK0) )).

tff(u104,axiom,(
    ! [X1,X0] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0) ) )).

tff(u103,axiom,(
    ! [X1,X0] :
      ( ~ l1_struct_0(X0)
      | k4_xboole_0(u1_struct_0(X0),X1) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k4_xboole_0(u1_struct_0(X0),X1))) ) )).

tff(u102,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:01:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (9534)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (9555)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.51  % (9533)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (9545)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (9543)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.51  % (9540)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (9540)Refutation not found, incomplete strategy% (9540)------------------------------
% 0.21/0.51  % (9540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (9540)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (9540)Memory used [KB]: 6140
% 0.21/0.51  % (9540)Time elapsed: 0.073 s
% 0.21/0.51  % (9540)------------------------------
% 0.21/0.51  % (9540)------------------------------
% 0.21/0.51  % (9543)Refutation not found, incomplete strategy% (9543)------------------------------
% 0.21/0.51  % (9543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (9543)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (9543)Memory used [KB]: 10618
% 0.21/0.51  % (9543)Time elapsed: 0.076 s
% 0.21/0.51  % (9543)------------------------------
% 0.21/0.51  % (9543)------------------------------
% 0.21/0.52  % (9550)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.52  % (9537)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.52  % (9550)Refutation not found, incomplete strategy% (9550)------------------------------
% 0.21/0.52  % (9550)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (9550)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (9550)Memory used [KB]: 1663
% 0.21/0.52  % (9550)Time elapsed: 0.106 s
% 0.21/0.52  % (9550)------------------------------
% 0.21/0.52  % (9550)------------------------------
% 0.21/0.52  % (9547)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.53  % (9541)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.53  % (9541)Refutation not found, incomplete strategy% (9541)------------------------------
% 0.21/0.53  % (9541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (9541)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (9541)Memory used [KB]: 10618
% 0.21/0.53  % (9541)Time elapsed: 0.111 s
% 0.21/0.53  % (9541)------------------------------
% 0.21/0.53  % (9541)------------------------------
% 0.21/0.53  % (9546)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.54  % (9545)# SZS output start Saturation.
% 0.21/0.54  tff(u131,negated_conjecture,
% 0.21/0.54      ((~(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))) | (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u130,axiom,
% 0.21/0.54      (![X1, X0] : (((k2_pre_topc(X0,X1) != X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v4_pre_topc(X1,X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u129,negated_conjecture,
% 0.21/0.54      (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u128,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((k7_subset_1(X0,k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X1),X2))))).
% 0.21/0.54  
% 0.21/0.54  tff(u127,negated_conjecture,
% 0.21/0.54      ((~(sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))) | (sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u126,negated_conjecture,
% 0.21/0.54      (![X0] : ((k4_xboole_0(u1_struct_0(sK0),X0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0))))))).
% 0.21/0.54  
% 0.21/0.54  tff(u125,axiom,
% 0.21/0.54      (![X1, X3, X2] : ((~r1_tarski(X2,X1) | (k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u124,axiom,
% 0.21/0.54      (![X1, X0] : ((~r1_tarski(X1,u1_struct_0(X0)) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1) | ~l1_struct_0(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u123,axiom,
% 0.21/0.54      (![X1, X0] : ((~r1_tarski(X1,u1_struct_0(X0)) | ~v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) = X1) | ~l1_pre_topc(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u122,negated_conjecture,
% 0.21/0.54      ((~~m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),u1_struct_0(sK0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u121,negated_conjecture,
% 0.21/0.54      (![X0] : ((~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),u1_struct_0(sK0)) | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),sK0) | ~v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u120,negated_conjecture,
% 0.21/0.54      (![X0] : ((~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),u1_struct_0(sK0)) | ~v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),sK0) | v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u119,axiom,
% 0.21/0.54      (![X1, X0] : (r1_tarski(k4_xboole_0(X0,X1),X0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u118,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u117,axiom,
% 0.21/0.54      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u116,axiom,
% 0.21/0.54      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) = X1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u115,negated_conjecture,
% 0.21/0.54      ((~~m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u114,negated_conjecture,
% 0.21/0.54      (![X1] : ((~m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X1),sK0) | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X1)),sK0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u113,negated_conjecture,
% 0.21/0.54      (![X0] : ((~m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0) | ~v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),sK0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u112,negated_conjecture,
% 0.21/0.54      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u111,axiom,
% 0.21/0.54      (![X1, X0] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u110,axiom,
% 0.21/0.54      (![X1, X0] : ((~l1_pre_topc(X0) | (k4_xboole_0(u1_struct_0(X0),X1) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k4_xboole_0(u1_struct_0(X0),X1)))))))).
% 0.21/0.54  
% 0.21/0.54  tff(u109,negated_conjecture,
% 0.21/0.54      l1_pre_topc(sK0)).
% 0.21/0.54  
% 0.21/0.54  tff(u108,negated_conjecture,
% 0.21/0.54      ((~~v4_pre_topc(sK1,sK0)) | ~v4_pre_topc(sK1,sK0))).
% 0.21/0.54  
% 0.21/0.54  tff(u107,axiom,
% 0.21/0.54      (![X1, X0] : ((~v4_pre_topc(k4_xboole_0(u1_struct_0(X0),X1),X0) | (k4_xboole_0(u1_struct_0(X0),X1) = k2_pre_topc(X0,k4_xboole_0(u1_struct_0(X0),X1))) | ~l1_pre_topc(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u106,axiom,
% 0.21/0.54      (![X1, X0] : ((~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v4_pre_topc(X1,X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u105,negated_conjecture,
% 0.21/0.54      ((~v3_pre_topc(sK1,sK0)) | v3_pre_topc(sK1,sK0))).
% 0.21/0.54  
% 0.21/0.54  tff(u104,axiom,
% 0.21/0.54      (![X1, X0] : ((v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u103,axiom,
% 0.21/0.54      (![X1, X0] : ((~l1_struct_0(X0) | (k4_xboole_0(u1_struct_0(X0),X1) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k4_xboole_0(u1_struct_0(X0),X1)))))))).
% 0.21/0.54  
% 0.21/0.54  tff(u102,axiom,
% 0.21/0.54      (![X0] : ((l1_struct_0(X0) | ~l1_pre_topc(X0))))).
% 0.21/0.54  
% 0.21/0.54  % (9545)# SZS output end Saturation.
% 0.21/0.54  % (9545)------------------------------
% 0.21/0.54  % (9545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (9545)Termination reason: Satisfiable
% 0.21/0.54  
% 0.21/0.54  % (9545)Memory used [KB]: 10618
% 0.21/0.54  % (9545)Time elapsed: 0.127 s
% 0.21/0.54  % (9545)------------------------------
% 0.21/0.54  % (9545)------------------------------
% 0.21/0.54  % (9532)Success in time 0.172 s
%------------------------------------------------------------------------------
