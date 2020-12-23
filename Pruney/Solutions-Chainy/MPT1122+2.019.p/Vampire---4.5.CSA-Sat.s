%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:20 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   41 (  41 expanded)
%              Number of leaves         :   41 (  41 expanded)
%              Depth                    :    0
%              Number of atoms          :   91 (  91 expanded)
%              Number of equality atoms :   23 (  23 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u170,negated_conjecture,
    ( ~ ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

tff(u169,axiom,(
    ! [X1,X0] :
      ( k2_pre_topc(X0,X1) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) )).

tff(u168,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2) )).

tff(u167,negated_conjecture,(
    ! [X0] : k4_xboole_0(u1_struct_0(sK0),X0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0))) )).

tff(u166,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u165,negated_conjecture,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

tff(u164,axiom,(
    ! [X1,X0,X2] : k7_subset_1(X0,k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X1),X2) )).

tff(u163,negated_conjecture,(
    u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

tff(u162,negated_conjecture,
    ( sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))
    | sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

tff(u161,axiom,(
    ! [X3,X5,X4] :
      ( ~ r1_tarski(X4,X3)
      | k7_subset_1(X3,X4,X5) = k4_xboole_0(X4,X5) ) )).

tff(u160,axiom,(
    ! [X1,X2] :
      ( ~ r1_tarski(X2,u1_struct_0(X1))
      | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2
      | ~ l1_struct_0(X1) ) )).

tff(u159,axiom,(
    ! [X1,X2] :
      ( ~ r1_tarski(X2,u1_struct_0(X1))
      | ~ v4_pre_topc(X2,X1)
      | k2_pre_topc(X1,X2) = X2
      | ~ l1_pre_topc(X1) ) )).

tff(u158,negated_conjecture,
    ( ~ ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),u1_struct_0(sK0)) )).

tff(u157,negated_conjecture,
    ( ~ ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) )).

tff(u156,negated_conjecture,(
    ! [X0] :
      ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),u1_struct_0(sK0))
      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),sK0)
      | ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0) ) )).

tff(u155,negated_conjecture,(
    ! [X0] :
      ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),u1_struct_0(sK0))
      | ~ v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),sK0)
      | v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0) ) )).

tff(u154,axiom,(
    ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) )).

tff(u153,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) )).

tff(u152,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) )).

tff(u151,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) )).

tff(u150,negated_conjecture,
    ( ~ ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u149,negated_conjecture,
    ( ~ ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u148,negated_conjecture,(
    ! [X1] :
      ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X1)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X1),sK0)
      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X1)),sK0) ) )).

tff(u147,negated_conjecture,(
    ! [X0] :
      ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0)
      | ~ v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),sK0) ) )).

tff(u146,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u145,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

tff(u144,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) )).

tff(u143,axiom,(
    ! [X1,X0] :
      ( ~ l1_pre_topc(X0)
      | k4_xboole_0(u1_struct_0(X0),X1) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k4_xboole_0(u1_struct_0(X0),X1))) ) )).

tff(u142,axiom,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0))) ) )).

tff(u141,negated_conjecture,(
    l1_pre_topc(sK0) )).

tff(u140,axiom,(
    ! [X1,X0] :
      ( ~ v4_pre_topc(k4_xboole_0(u1_struct_0(X0),X1),X0)
      | k4_xboole_0(u1_struct_0(X0),X1) = k2_pre_topc(X0,k4_xboole_0(u1_struct_0(X0),X1))
      | ~ l1_pre_topc(X0) ) )).

tff(u139,negated_conjecture,
    ( ~ ~ v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),sK0)
    | ~ v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),sK0) )).

tff(u138,axiom,(
    ! [X0] :
      ( ~ v4_pre_topc(u1_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_pre_topc(X0,u1_struct_0(X0)) ) )).

tff(u137,negated_conjecture,
    ( ~ ~ v4_pre_topc(sK1,sK0)
    | ~ v4_pre_topc(sK1,sK0) )).

tff(u136,axiom,(
    ! [X1,X0] :
      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) )).

tff(u135,negated_conjecture,
    ( ~ ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ v3_pre_topc(u1_struct_0(sK0),sK0) )).

tff(u134,negated_conjecture,
    ( ~ v3_pre_topc(sK1,sK0)
    | v3_pre_topc(sK1,sK0) )).

tff(u133,axiom,(
    ! [X1,X0] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0) ) )).

tff(u132,axiom,(
    ! [X1,X0] :
      ( ~ l1_struct_0(X0)
      | k4_xboole_0(u1_struct_0(X0),X1) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k4_xboole_0(u1_struct_0(X0),X1))) ) )).

tff(u131,axiom,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0))) ) )).

tff(u130,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:31:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (30348)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.50  % (30362)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.50  % (30361)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.50  % (30358)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.50  % (30344)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.50  % (30366)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.50  % (30346)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.50  % (30345)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.51  % (30351)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (30356)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.51  % (30360)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.51  % (30365)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.51  % (30364)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.51  % (30354)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.51  % (30349)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.51  % (30363)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.51  % (30353)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.51  % (30350)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.51  % (30347)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.51  % (30347)Refutation not found, incomplete strategy% (30347)------------------------------
% 0.22/0.51  % (30347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (30347)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (30347)Memory used [KB]: 10618
% 0.22/0.51  % (30347)Time elapsed: 0.092 s
% 0.22/0.51  % (30347)------------------------------
% 0.22/0.51  % (30347)------------------------------
% 0.22/0.51  % (30355)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.52  % (30351)Refutation not found, incomplete strategy% (30351)------------------------------
% 0.22/0.52  % (30351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (30351)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (30351)Memory used [KB]: 6140
% 0.22/0.52  % (30351)Time elapsed: 0.104 s
% 0.22/0.52  % (30351)------------------------------
% 0.22/0.52  % (30351)------------------------------
% 0.22/0.52  % (30363)Refutation not found, incomplete strategy% (30363)------------------------------
% 0.22/0.52  % (30363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (30363)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (30363)Memory used [KB]: 6140
% 0.22/0.52  % (30363)Time elapsed: 0.108 s
% 0.22/0.52  % (30363)------------------------------
% 0.22/0.52  % (30363)------------------------------
% 0.22/0.52  % (30367)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.52  % (30352)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.52  % (30354)Refutation not found, incomplete strategy% (30354)------------------------------
% 0.22/0.52  % (30354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (30354)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (30354)Memory used [KB]: 10618
% 0.22/0.52  % (30354)Time elapsed: 0.108 s
% 0.22/0.52  % (30354)------------------------------
% 0.22/0.52  % (30354)------------------------------
% 0.22/0.52  % (30359)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.52  % (30365)Refutation not found, incomplete strategy% (30365)------------------------------
% 0.22/0.52  % (30365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (30365)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (30365)Memory used [KB]: 1663
% 0.22/0.52  % (30365)Time elapsed: 0.109 s
% 0.22/0.52  % (30365)------------------------------
% 0.22/0.52  % (30365)------------------------------
% 0.22/0.52  % (30352)Refutation not found, incomplete strategy% (30352)------------------------------
% 0.22/0.52  % (30352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (30352)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (30352)Memory used [KB]: 10618
% 0.22/0.52  % (30352)Time elapsed: 0.107 s
% 0.22/0.52  % (30352)------------------------------
% 0.22/0.52  % (30352)------------------------------
% 0.22/0.52  % (30357)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.52  % (30355)Refutation not found, incomplete strategy% (30355)------------------------------
% 0.22/0.52  % (30355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (30355)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (30355)Memory used [KB]: 1663
% 0.22/0.52  % (30355)Time elapsed: 0.110 s
% 0.22/0.52  % (30355)------------------------------
% 0.22/0.52  % (30355)------------------------------
% 0.22/0.52  % (30364)Refutation not found, incomplete strategy% (30364)------------------------------
% 0.22/0.52  % (30364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (30364)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (30364)Memory used [KB]: 6140
% 0.22/0.52  % (30364)Time elapsed: 0.109 s
% 0.22/0.52  % (30364)------------------------------
% 0.22/0.52  % (30364)------------------------------
% 0.22/0.52  % (30367)Refutation not found, incomplete strategy% (30367)------------------------------
% 0.22/0.52  % (30367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (30367)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (30367)Memory used [KB]: 10618
% 0.22/0.52  % (30367)Time elapsed: 0.106 s
% 0.22/0.52  % (30367)------------------------------
% 0.22/0.52  % (30367)------------------------------
% 0.22/0.52  % (30360)Refutation not found, incomplete strategy% (30360)------------------------------
% 0.22/0.52  % (30360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (30360)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (30360)Memory used [KB]: 1663
% 0.22/0.52  % (30360)Time elapsed: 0.108 s
% 0.22/0.52  % (30360)------------------------------
% 0.22/0.52  % (30360)------------------------------
% 0.22/0.52  % (30361)Refutation not found, incomplete strategy% (30361)------------------------------
% 0.22/0.52  % (30361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (30361)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (30361)Memory used [KB]: 1663
% 0.22/0.52  % (30361)Time elapsed: 0.106 s
% 0.22/0.52  % (30361)------------------------------
% 0.22/0.52  % (30361)------------------------------
% 0.22/0.52  % (30356)# SZS output start Saturation.
% 0.22/0.52  tff(u170,negated_conjecture,
% 0.22/0.52      ((~(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))) | (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))))).
% 0.22/0.52  
% 0.22/0.52  tff(u169,axiom,
% 0.22/0.52      (![X1, X0] : (((k2_pre_topc(X0,X1) != X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v4_pre_topc(X1,X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u168,axiom,
% 0.22/0.52      (![X1, X2] : ((k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2))))).
% 0.22/0.52  
% 0.22/0.52  tff(u167,negated_conjecture,
% 0.22/0.52      (![X0] : ((k4_xboole_0(u1_struct_0(sK0),X0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0))))))).
% 0.22/0.52  
% 0.22/0.52  tff(u166,axiom,
% 0.22/0.52      (![X0] : ((k2_subset_1(X0) = X0)))).
% 0.22/0.52  
% 0.22/0.52  tff(u165,negated_conjecture,
% 0.22/0.52      (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u164,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((k7_subset_1(X0,k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X1),X2))))).
% 0.22/0.52  
% 0.22/0.52  tff(u163,negated_conjecture,
% 0.22/0.52      (u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u162,negated_conjecture,
% 0.22/0.52      ((~(sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))) | (sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))))).
% 0.22/0.52  
% 0.22/0.52  tff(u161,axiom,
% 0.22/0.52      (![X3, X5, X4] : ((~r1_tarski(X4,X3) | (k7_subset_1(X3,X4,X5) = k4_xboole_0(X4,X5)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u160,axiom,
% 0.22/0.52      (![X1, X2] : ((~r1_tarski(X2,u1_struct_0(X1)) | (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2) | ~l1_struct_0(X1))))).
% 0.22/0.52  
% 0.22/0.52  tff(u159,axiom,
% 0.22/0.52      (![X1, X2] : ((~r1_tarski(X2,u1_struct_0(X1)) | ~v4_pre_topc(X2,X1) | (k2_pre_topc(X1,X2) = X2) | ~l1_pre_topc(X1))))).
% 0.22/0.52  
% 0.22/0.52  tff(u158,negated_conjecture,
% 0.22/0.52      ((~~m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),u1_struct_0(sK0)))).
% 0.22/0.52  
% 0.22/0.52  tff(u157,negated_conjecture,
% 0.22/0.52      ((~~m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)))).
% 0.22/0.52  
% 0.22/0.52  tff(u156,negated_conjecture,
% 0.22/0.52      (![X0] : ((~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),u1_struct_0(sK0)) | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),sK0) | ~v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u155,negated_conjecture,
% 0.22/0.52      (![X0] : ((~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),u1_struct_0(sK0)) | ~v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),sK0) | v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u154,axiom,
% 0.22/0.52      (![X1, X0] : (r1_tarski(k4_xboole_0(X0,X1),X0)))).
% 0.22/0.52  
% 0.22/0.52  tff(u153,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u152,axiom,
% 0.22/0.52      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))))).
% 0.22/0.52  
% 0.22/0.52  tff(u151,axiom,
% 0.22/0.52      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) = X1))))).
% 0.22/0.52  
% 0.22/0.52  tff(u150,negated_conjecture,
% 0.22/0.52      ((~~m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u149,negated_conjecture,
% 0.22/0.52      ((~~m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u148,negated_conjecture,
% 0.22/0.52      (![X1] : ((~m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X1),sK0) | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X1)),sK0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u147,negated_conjecture,
% 0.22/0.52      (![X0] : ((~m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0) | ~v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),sK0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u146,negated_conjecture,
% 0.22/0.52      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.52  
% 0.22/0.52  tff(u145,axiom,
% 0.22/0.52      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u144,axiom,
% 0.22/0.52      (![X1, X0] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))))).
% 0.22/0.52  
% 0.22/0.52  tff(u143,axiom,
% 0.22/0.52      (![X1, X0] : ((~l1_pre_topc(X0) | (k4_xboole_0(u1_struct_0(X0),X1) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k4_xboole_0(u1_struct_0(X0),X1)))))))).
% 0.22/0.52  
% 0.22/0.52  tff(u142,axiom,
% 0.22/0.52      (![X0] : ((~l1_pre_topc(X0) | (u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0)))))))).
% 0.22/0.52  
% 0.22/0.52  tff(u141,negated_conjecture,
% 0.22/0.52      l1_pre_topc(sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u140,axiom,
% 0.22/0.52      (![X1, X0] : ((~v4_pre_topc(k4_xboole_0(u1_struct_0(X0),X1),X0) | (k4_xboole_0(u1_struct_0(X0),X1) = k2_pre_topc(X0,k4_xboole_0(u1_struct_0(X0),X1))) | ~l1_pre_topc(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u139,negated_conjecture,
% 0.22/0.52      ((~~v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),sK0)) | ~v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),sK0))).
% 0.22/0.52  
% 0.22/0.52  tff(u138,axiom,
% 0.22/0.52      (![X0] : ((~v4_pre_topc(u1_struct_0(X0),X0) | ~l1_pre_topc(X0) | (u1_struct_0(X0) = k2_pre_topc(X0,u1_struct_0(X0))))))).
% 0.22/0.52  
% 0.22/0.52  tff(u137,negated_conjecture,
% 0.22/0.52      ((~~v4_pre_topc(sK1,sK0)) | ~v4_pre_topc(sK1,sK0))).
% 0.22/0.52  
% 0.22/0.52  tff(u136,axiom,
% 0.22/0.52      (![X1, X0] : ((~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v4_pre_topc(X1,X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u135,negated_conjecture,
% 0.22/0.52      ((~~v3_pre_topc(u1_struct_0(sK0),sK0)) | ~v3_pre_topc(u1_struct_0(sK0),sK0))).
% 0.22/0.52  
% 0.22/0.52  tff(u134,negated_conjecture,
% 0.22/0.52      ((~v3_pre_topc(sK1,sK0)) | v3_pre_topc(sK1,sK0))).
% 0.22/0.52  
% 0.22/0.52  tff(u133,axiom,
% 0.22/0.52      (![X1, X0] : ((v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u132,axiom,
% 0.22/0.52      (![X1, X0] : ((~l1_struct_0(X0) | (k4_xboole_0(u1_struct_0(X0),X1) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k4_xboole_0(u1_struct_0(X0),X1)))))))).
% 0.22/0.52  
% 0.22/0.52  tff(u131,axiom,
% 0.22/0.52      (![X0] : ((~l1_struct_0(X0) | (u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0)))))))).
% 0.22/0.52  
% 0.22/0.52  tff(u130,axiom,
% 0.22/0.52      (![X0] : ((l1_struct_0(X0) | ~l1_pre_topc(X0))))).
% 0.22/0.52  
% 0.22/0.52  % (30356)# SZS output end Saturation.
% 0.22/0.52  % (30356)------------------------------
% 0.22/0.52  % (30356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (30356)Termination reason: Satisfiable
% 0.22/0.52  
% 0.22/0.52  % (30356)Memory used [KB]: 10618
% 0.22/0.52  % (30356)Time elapsed: 0.103 s
% 0.22/0.52  % (30356)------------------------------
% 0.22/0.52  % (30356)------------------------------
% 0.22/0.52  % (30343)Success in time 0.16 s
%------------------------------------------------------------------------------
