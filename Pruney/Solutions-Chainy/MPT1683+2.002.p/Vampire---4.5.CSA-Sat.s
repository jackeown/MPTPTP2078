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
% DateTime   : Thu Dec  3 13:17:19 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   35 (  35 expanded)
%              Number of leaves         :   35 (  35 expanded)
%              Depth                    :    0
%              Number of atoms          :  131 ( 131 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u160,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u159,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) )).

tff(u158,negated_conjecture,(
    ~ v1_xboole_0(sK1) )).

tff(u157,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u156,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u155,axiom,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | k7_domain_1(u1_struct_0(X0),sK3(X0),sK2(X0)) = k2_tarski(sK3(X0),sK2(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_lattice3(X0) ) )).

tff(u154,axiom,(
    ! [X1] :
      ( v1_xboole_0(u1_struct_0(X1))
      | k7_domain_1(u1_struct_0(X1),sK2(X1),sK3(X1)) = k2_tarski(sK2(X1),sK3(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | v2_lattice3(X1) ) )).

tff(u153,axiom,(
    ! [X1] :
      ( v1_xboole_0(u1_struct_0(X1))
      | k7_domain_1(u1_struct_0(X1),sK2(X1),sK2(X1)) = k2_tarski(sK2(X1),sK2(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | v2_lattice3(X1) ) )).

tff(u152,axiom,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | k7_domain_1(u1_struct_0(X0),sK3(X0),sK3(X0)) = k2_tarski(sK3(X0),sK3(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_lattice3(X0) ) )).

tff(u151,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u150,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | k7_domain_1(X1,X0,X0) = k2_tarski(X0,X0) ) )).

tff(u149,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) ) )).

tff(u148,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k12_lattice3(X0,X1,X2) ) )).

tff(u147,axiom,(
    ! [X1,X2] :
      ( ~ m1_subset_1(X1,u1_struct_0(X2))
      | v1_xboole_0(u1_struct_0(X2))
      | k7_domain_1(u1_struct_0(X2),X1,sK3(X2)) = k2_tarski(X1,sK3(X2))
      | ~ l1_orders_2(X2)
      | ~ v5_orders_2(X2)
      | v2_lattice3(X2) ) )).

tff(u146,axiom,(
    ! [X3,X4] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | v1_xboole_0(u1_struct_0(X4))
      | k7_domain_1(u1_struct_0(X4),X3,sK2(X4)) = k2_tarski(X3,sK2(X4))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4)
      | v2_lattice3(X4) ) )).

tff(u145,axiom,(
    ! [X1,X2] :
      ( ~ m1_subset_1(X1,u1_struct_0(X2))
      | v1_xboole_0(u1_struct_0(X2))
      | k7_domain_1(u1_struct_0(X2),sK3(X2),X1) = k2_tarski(sK3(X2),X1)
      | ~ l1_orders_2(X2)
      | ~ v5_orders_2(X2)
      | v2_lattice3(X2) ) )).

tff(u144,axiom,(
    ! [X3,X4] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | v1_xboole_0(u1_struct_0(X4))
      | k7_domain_1(u1_struct_0(X4),sK2(X4),X3) = k2_tarski(sK2(X4),X3)
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4)
      | v2_lattice3(X4) ) )).

tff(u143,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v5_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ l1_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X0,X0)) = k12_lattice3(X1,X0,X0) ) )).

tff(u142,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u141,axiom,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_lattice3(X0) ) )).

tff(u140,axiom,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_lattice3(X0) ) )).

tff(u139,axiom,(
    ! [X0] :
      ( ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v2_struct_0(X0) ) )).

tff(u138,negated_conjecture,(
    v2_lattice3(sK0) )).

tff(u137,axiom,(
    ! [X0] :
      ( v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | k7_domain_1(u1_struct_0(X0),sK3(X0),sK2(X0)) = k2_tarski(sK3(X0),sK2(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u136,axiom,(
    ! [X0] :
      ( v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | k2_tarski(sK2(X0),sK3(X0)) = k7_domain_1(u1_struct_0(X0),sK2(X0),sK3(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u135,axiom,(
    ! [X0] :
      ( v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | k7_domain_1(u1_struct_0(X0),sK2(X0),sK2(X0)) = k2_tarski(sK2(X0),sK2(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u134,axiom,(
    ! [X0] :
      ( v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | k7_domain_1(u1_struct_0(X0),sK3(X0),sK3(X0)) = k2_tarski(sK3(X0),sK3(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u133,negated_conjecture,
    ( ~ v5_yellow_0(k5_yellow_0(sK0,sK1),sK0)
    | v5_yellow_0(k5_yellow_0(sK0,sK1),sK0) )).

tff(u132,axiom,(
    ! [X0] :
      ( ~ r2_yellow_0(X0,k2_tarski(sK2(X0),sK3(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_lattice3(X0) ) )).

tff(u131,axiom,(
    ! [X1,X0,X2] :
      ( r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0) ) )).

tff(u130,negated_conjecture,(
    v5_orders_2(sK0) )).

tff(u129,negated_conjecture,(
    v3_orders_2(sK0) )).

tff(u128,negated_conjecture,(
    v4_orders_2(sK0) )).

tff(u127,negated_conjecture,(
    v13_waybel_0(sK1,sK0) )).

tff(u126,negated_conjecture,
    ( ~ ~ v2_waybel_0(sK1,sK0)
    | ~ v2_waybel_0(sK1,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:42:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (25617)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.49  % (25628)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.49  % (25627)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.50  % (25614)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.50  % (25616)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (25620)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.50  % (25617)Refutation not found, incomplete strategy% (25617)------------------------------
% 0.21/0.50  % (25617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (25617)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (25617)Memory used [KB]: 10618
% 0.21/0.50  % (25617)Time elapsed: 0.084 s
% 0.21/0.50  % (25617)------------------------------
% 0.21/0.50  % (25617)------------------------------
% 0.21/0.50  % (25616)Refutation not found, incomplete strategy% (25616)------------------------------
% 0.21/0.50  % (25616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (25619)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (25620)Refutation not found, incomplete strategy% (25620)------------------------------
% 0.21/0.50  % (25620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (25630)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.50  % (25618)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (25615)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.50  % (25637)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.50  % (25627)# SZS output start Saturation.
% 0.21/0.50  tff(u160,negated_conjecture,
% 0.21/0.50      ~v2_struct_0(sK0)).
% 0.21/0.50  
% 0.21/0.50  tff(u159,axiom,
% 0.21/0.50      (![X0] : ((l1_struct_0(X0) | ~l1_orders_2(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u158,negated_conjecture,
% 0.21/0.50      ~v1_xboole_0(sK1)).
% 0.21/0.50  
% 0.21/0.50  tff(u157,axiom,
% 0.21/0.50      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u156,negated_conjecture,
% 0.21/0.50      ((~v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u155,axiom,
% 0.21/0.50      (![X0] : ((v1_xboole_0(u1_struct_0(X0)) | (k7_domain_1(u1_struct_0(X0),sK3(X0),sK2(X0)) = k2_tarski(sK3(X0),sK2(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | v2_lattice3(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u154,axiom,
% 0.21/0.50      (![X1] : ((v1_xboole_0(u1_struct_0(X1)) | (k7_domain_1(u1_struct_0(X1),sK2(X1),sK3(X1)) = k2_tarski(sK2(X1),sK3(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | v2_lattice3(X1))))).
% 0.21/0.50  
% 0.21/0.50  tff(u153,axiom,
% 0.21/0.50      (![X1] : ((v1_xboole_0(u1_struct_0(X1)) | (k7_domain_1(u1_struct_0(X1),sK2(X1),sK2(X1)) = k2_tarski(sK2(X1),sK2(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | v2_lattice3(X1))))).
% 0.21/0.50  
% 0.21/0.50  tff(u152,axiom,
% 0.21/0.50      (![X0] : ((v1_xboole_0(u1_struct_0(X0)) | (k7_domain_1(u1_struct_0(X0),sK3(X0),sK3(X0)) = k2_tarski(sK3(X0),sK3(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | v2_lattice3(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u151,negated_conjecture,
% 0.21/0.50      l1_orders_2(sK0)).
% 0.21/0.50  
% 0.21/0.50  tff(u150,axiom,
% 0.21/0.50      (![X1, X0] : ((~m1_subset_1(X0,X1) | v1_xboole_0(X1) | (k7_domain_1(X1,X0,X0) = k2_tarski(X0,X0)))))).
% 0.21/0.50  
% 0.21/0.50  tff(u149,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | (k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)))))).
% 0.21/0.50  
% 0.21/0.50  tff(u148,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | (k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k12_lattice3(X0,X1,X2)))))).
% 0.21/0.50  
% 0.21/0.50  tff(u147,axiom,
% 0.21/0.50      (![X1, X2] : ((~m1_subset_1(X1,u1_struct_0(X2)) | v1_xboole_0(u1_struct_0(X2)) | (k7_domain_1(u1_struct_0(X2),X1,sK3(X2)) = k2_tarski(X1,sK3(X2))) | ~l1_orders_2(X2) | ~v5_orders_2(X2) | v2_lattice3(X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u146,axiom,
% 0.21/0.50      (![X3, X4] : ((~m1_subset_1(X3,u1_struct_0(X4)) | v1_xboole_0(u1_struct_0(X4)) | (k7_domain_1(u1_struct_0(X4),X3,sK2(X4)) = k2_tarski(X3,sK2(X4))) | ~l1_orders_2(X4) | ~v5_orders_2(X4) | v2_lattice3(X4))))).
% 0.21/0.50  
% 0.21/0.50  tff(u145,axiom,
% 0.21/0.50      (![X1, X2] : ((~m1_subset_1(X1,u1_struct_0(X2)) | v1_xboole_0(u1_struct_0(X2)) | (k7_domain_1(u1_struct_0(X2),sK3(X2),X1) = k2_tarski(sK3(X2),X1)) | ~l1_orders_2(X2) | ~v5_orders_2(X2) | v2_lattice3(X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u144,axiom,
% 0.21/0.50      (![X3, X4] : ((~m1_subset_1(X3,u1_struct_0(X4)) | v1_xboole_0(u1_struct_0(X4)) | (k7_domain_1(u1_struct_0(X4),sK2(X4),X3) = k2_tarski(sK2(X4),X3)) | ~l1_orders_2(X4) | ~v5_orders_2(X4) | v2_lattice3(X4))))).
% 0.21/0.50  
% 0.21/0.50  tff(u143,axiom,
% 0.21/0.50      (![X1, X0] : ((~m1_subset_1(X0,u1_struct_0(X1)) | ~v5_orders_2(X1) | ~v2_lattice3(X1) | ~l1_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | (k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X0,X0)) = k12_lattice3(X1,X0,X0)))))).
% 0.21/0.50  
% 0.21/0.50  tff(u142,negated_conjecture,
% 0.21/0.50      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.50  
% 0.21/0.50  tff(u141,axiom,
% 0.21/0.50      (![X0] : ((m1_subset_1(sK3(X0),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | v2_lattice3(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u140,axiom,
% 0.21/0.50      (![X0] : ((m1_subset_1(sK2(X0),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | v2_lattice3(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u139,axiom,
% 0.21/0.50      (![X0] : ((~v2_lattice3(X0) | ~l1_orders_2(X0) | ~v2_struct_0(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u138,negated_conjecture,
% 0.21/0.50      v2_lattice3(sK0)).
% 0.21/0.50  
% 0.21/0.50  tff(u137,axiom,
% 0.21/0.50      (![X0] : ((v2_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | (k7_domain_1(u1_struct_0(X0),sK3(X0),sK2(X0)) = k2_tarski(sK3(X0),sK2(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u136,axiom,
% 0.21/0.50      (![X0] : ((v2_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | (k2_tarski(sK2(X0),sK3(X0)) = k7_domain_1(u1_struct_0(X0),sK2(X0),sK3(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u135,axiom,
% 0.21/0.50      (![X0] : ((v2_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | (k7_domain_1(u1_struct_0(X0),sK2(X0),sK2(X0)) = k2_tarski(sK2(X0),sK2(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u134,axiom,
% 0.21/0.50      (![X0] : ((v2_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | (k7_domain_1(u1_struct_0(X0),sK3(X0),sK3(X0)) = k2_tarski(sK3(X0),sK3(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u133,negated_conjecture,
% 0.21/0.50      ((~v5_yellow_0(k5_yellow_0(sK0,sK1),sK0)) | v5_yellow_0(k5_yellow_0(sK0,sK1),sK0))).
% 0.21/0.50  
% 0.21/0.50  tff(u132,axiom,
% 0.21/0.50      (![X0] : ((~r2_yellow_0(X0,k2_tarski(sK2(X0),sK3(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | v2_lattice3(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u131,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((r2_yellow_0(X0,k2_tarski(X1,X2)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~v2_lattice3(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u130,negated_conjecture,
% 0.21/0.50      v5_orders_2(sK0)).
% 0.21/0.50  
% 0.21/0.50  tff(u129,negated_conjecture,
% 0.21/0.50      v3_orders_2(sK0)).
% 0.21/0.50  
% 0.21/0.50  tff(u128,negated_conjecture,
% 0.21/0.50      v4_orders_2(sK0)).
% 0.21/0.50  
% 0.21/0.50  tff(u127,negated_conjecture,
% 0.21/0.50      v13_waybel_0(sK1,sK0)).
% 0.21/0.50  
% 0.21/0.50  tff(u126,negated_conjecture,
% 0.21/0.50      ((~~v2_waybel_0(sK1,sK0)) | ~v2_waybel_0(sK1,sK0))).
% 0.21/0.50  
% 0.21/0.50  % (25627)# SZS output end Saturation.
% 0.21/0.50  % (25627)------------------------------
% 0.21/0.50  % (25627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (25627)Termination reason: Satisfiable
% 0.21/0.50  
% 0.21/0.50  % (25627)Memory used [KB]: 10618
% 0.21/0.50  % (25627)Time elapsed: 0.095 s
% 0.21/0.50  % (25627)------------------------------
% 0.21/0.50  % (25627)------------------------------
% 0.21/0.50  % (25621)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (25636)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.50  % (25621)Refutation not found, incomplete strategy% (25621)------------------------------
% 0.21/0.50  % (25621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (25621)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (25621)Memory used [KB]: 6140
% 0.21/0.50  % (25621)Time elapsed: 0.059 s
% 0.21/0.50  % (25621)------------------------------
% 0.21/0.50  % (25621)------------------------------
% 0.21/0.51  % (25612)Success in time 0.148 s
%------------------------------------------------------------------------------
