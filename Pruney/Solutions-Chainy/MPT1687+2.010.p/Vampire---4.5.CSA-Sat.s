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
% DateTime   : Thu Dec  3 13:17:21 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   58 (  58 expanded)
%              Number of leaves         :   58 (  58 expanded)
%              Depth                    :    0
%              Number of atoms          :  157 ( 157 expanded)
%              Number of equality atoms :   37 (  37 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u388,negated_conjecture,
    ( ~ ( k1_xboole_0 != u1_struct_0(sK1) )
    | k1_xboole_0 != u1_struct_0(sK1) )).

tff(u387,negated_conjecture,
    ( ~ ( k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) )
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) )).

tff(u386,axiom,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 )).

tff(u385,axiom,(
    ! [X0] : k1_relset_1(X0,X0,k6_relat_1(X0)) = X0 )).

tff(u384,negated_conjecture,
    ( u1_struct_0(sK0) != k1_relat_1(sK2)
    | u1_struct_0(sK0) = k1_relat_1(sK2) )).

tff(u383,axiom,(
    ! [X0] : k2_relset_1(X0,X0,k6_relat_1(X0)) = k2_relat_1(k6_relat_1(X0)) )).

tff(u382,negated_conjecture,
    ( k1_relat_1(sK2) != k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)
    | k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) )).

tff(u381,negated_conjecture,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)
    | k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) )).

tff(u380,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u379,negated_conjecture,
    ( ~ ~ v1_xboole_0(k1_relat_1(sK2))
    | ~ v1_xboole_0(k1_relat_1(sK2)) )).

tff(u378,axiom,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) )).

tff(u377,negated_conjecture,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(sK2) )).

tff(u376,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) )).

tff(u375,negated_conjecture,
    ( ~ v1_funct_1(sK2)
    | v1_funct_1(sK2) )).

tff(u374,axiom,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ) )).

tff(u373,axiom,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) )).

tff(u372,axiom,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0 ) )).

tff(u371,axiom,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(k2_funct_1(X0)) ) )).

tff(u370,axiom,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) )).

tff(u369,axiom,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) )).

tff(u368,negated_conjecture,
    ( ~ ~ v2_funct_1(sK2)
    | ~ v2_funct_1(sK2) )).

tff(u367,axiom,(
    ! [X0] :
      ( ~ v2_funct_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | k2_relat_1(k6_relat_1(X0)) != X0
      | m1_subset_1(k2_funct_1(k6_relat_1(X0)),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_xboole_0 = X0 ) )).

tff(u366,axiom,(
    ! [X0] :
      ( ~ v2_funct_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | k2_relat_1(k6_relat_1(X0)) != X0
      | v1_funct_2(k2_funct_1(k6_relat_1(X0)),X0,X0)
      | k1_xboole_0 = X0 ) )).

tff(u365,axiom,(
    ! [X0] :
      ( ~ v2_funct_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | v1_funct_1(k2_funct_1(k6_relat_1(X0))) ) )).

tff(u364,axiom,
    ( ~ ~ v2_funct_1(k6_relat_1(k1_xboole_0))
    | ~ v2_funct_1(k6_relat_1(k1_xboole_0)) )).

tff(u363,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) )).

tff(u362,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) )).

tff(u361,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) )).

tff(u360,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) )).

tff(u359,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) )).

tff(u358,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) )).

tff(u357,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0) ) )).

tff(u356,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) )).

tff(u355,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | v1_funct_1(k2_funct_1(X2)) ) )).

tff(u354,axiom,(
    ! [X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0) ) )).

tff(u353,axiom,(
    ! [X1,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) )).

tff(u352,axiom,(
    ! [X1,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) )).

tff(u351,axiom,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) ) )).

tff(u350,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )).

tff(u349,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) )).

tff(u348,axiom,(
    ! [X1] :
      ( ~ v4_relat_1(X1,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | v1_partfun1(X1,k1_relat_1(X1)) ) )).

tff(u347,axiom,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) )).

tff(u346,negated_conjecture,
    ( ~ v4_relat_1(sK2,k1_relat_1(sK2))
    | v4_relat_1(sK2,k1_relat_1(sK2)) )).

tff(u345,axiom,(
    ! [X0] :
      ( ~ v1_funct_2(k6_relat_1(X0),X0,X0)
      | k2_relat_1(k6_relat_1(X0)) != X0
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v2_funct_1(k6_relat_1(X0))
      | m1_subset_1(k2_funct_1(k6_relat_1(X0)),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) )).

tff(u344,axiom,(
    ! [X0] :
      ( ~ v1_funct_2(k6_relat_1(X0),X0,X0)
      | k2_relat_1(k6_relat_1(X0)) != X0
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v2_funct_1(k6_relat_1(X0))
      | v1_funct_2(k2_funct_1(k6_relat_1(X0)),X0,X0) ) )).

tff(u343,axiom,
    ( ~ v1_funct_2(k6_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | v1_funct_2(k6_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) )).

tff(u342,axiom,(
    ! [X0] :
      ( v1_funct_2(k6_relat_1(X0),X0,X0)
      | k1_xboole_0 = X0 ) )).

tff(u341,negated_conjecture,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) )).

tff(u340,axiom,(
    ! [X1,X0] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) )).

tff(u339,axiom,(
    ! [X0] : v1_partfun1(k6_relat_1(X0),X0) )).

tff(u338,negated_conjecture,
    ( ~ v1_partfun1(sK2,k1_relat_1(sK2))
    | v1_partfun1(sK2,k1_relat_1(sK2)) )).

tff(u337,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u336,negated_conjecture,
    ( ~ ~ v2_struct_0(sK1)
    | ~ v2_struct_0(sK1) )).

tff(u335,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

tff(u334,negated_conjecture,
    ( ~ l1_struct_0(sK1)
    | l1_struct_0(sK1) )).

tff(u333,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u332,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u331,negated_conjecture,
    ( ~ l1_orders_2(sK1)
    | l1_orders_2(sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:31:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.46  % (8792)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.49  % (8807)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.49  % (8798)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.49  % (8813)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.19/0.49  % (8807)# SZS output start Saturation.
% 0.19/0.49  tff(u388,negated_conjecture,
% 0.19/0.49      ((~(k1_xboole_0 != u1_struct_0(sK1))) | (k1_xboole_0 != u1_struct_0(sK1)))).
% 0.19/0.49  
% 0.19/0.49  tff(u387,negated_conjecture,
% 0.19/0.49      ((~(k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2))) | (k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)))).
% 0.19/0.49  
% 0.19/0.49  tff(u386,axiom,
% 0.19/0.49      (![X0] : ((k1_relat_1(k6_relat_1(X0)) = X0)))).
% 0.19/0.49  
% 0.19/0.49  tff(u385,axiom,
% 0.19/0.49      (![X0] : ((k1_relset_1(X0,X0,k6_relat_1(X0)) = X0)))).
% 0.19/0.49  
% 0.19/0.49  tff(u384,negated_conjecture,
% 0.19/0.49      ((~(u1_struct_0(sK0) = k1_relat_1(sK2))) | (u1_struct_0(sK0) = k1_relat_1(sK2)))).
% 0.19/0.49  
% 0.19/0.49  tff(u383,axiom,
% 0.19/0.49      (![X0] : ((k2_relset_1(X0,X0,k6_relat_1(X0)) = k2_relat_1(k6_relat_1(X0)))))).
% 0.19/0.49  
% 0.19/0.49  tff(u382,negated_conjecture,
% 0.19/0.49      ((~(k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2))) | (k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)))).
% 0.19/0.49  
% 0.19/0.49  tff(u381,negated_conjecture,
% 0.19/0.49      ((~(k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2))) | (k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)))).
% 0.19/0.49  
% 0.19/0.49  tff(u380,axiom,
% 0.19/0.49      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.19/0.49  
% 0.19/0.49  tff(u379,negated_conjecture,
% 0.19/0.49      ((~~v1_xboole_0(k1_relat_1(sK2))) | ~v1_xboole_0(k1_relat_1(sK2)))).
% 0.19/0.49  
% 0.19/0.49  tff(u378,axiom,
% 0.19/0.49      ((~v1_xboole_0(k1_xboole_0)) | v1_xboole_0(k1_xboole_0))).
% 0.19/0.49  
% 0.19/0.49  tff(u377,negated_conjecture,
% 0.19/0.49      ((~v1_relat_1(sK2)) | v1_relat_1(sK2))).
% 0.19/0.49  
% 0.19/0.49  tff(u376,axiom,
% 0.19/0.49      (![X0] : (v1_relat_1(k6_relat_1(X0))))).
% 0.19/0.49  
% 0.19/0.49  tff(u375,negated_conjecture,
% 0.19/0.49      ((~v1_funct_1(sK2)) | v1_funct_1(sK2))).
% 0.19/0.49  
% 0.19/0.49  tff(u374,axiom,
% 0.19/0.49      (![X0] : ((~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))))))).
% 0.19/0.49  
% 0.19/0.49  tff(u373,axiom,
% 0.19/0.49      (![X0] : ((~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))))))).
% 0.19/0.49  
% 0.19/0.49  tff(u372,axiom,
% 0.19/0.49      (![X0] : ((~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | (k2_funct_1(k2_funct_1(X0)) = X0))))).
% 0.19/0.49  
% 0.19/0.49  tff(u371,axiom,
% 0.19/0.49      (![X0] : ((~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(k2_funct_1(X0)))))).
% 0.19/0.49  
% 0.19/0.49  tff(u370,axiom,
% 0.19/0.49      (![X0] : ((~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0)))))).
% 0.19/0.49  
% 0.19/0.49  tff(u369,axiom,
% 0.19/0.49      (![X0] : ((~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)))))).
% 0.19/0.49  
% 0.19/0.49  tff(u368,negated_conjecture,
% 0.19/0.49      ((~~v2_funct_1(sK2)) | ~v2_funct_1(sK2))).
% 0.19/0.49  
% 0.19/0.49  tff(u367,axiom,
% 0.19/0.49      (![X0] : ((~v2_funct_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | (k2_relat_1(k6_relat_1(X0)) != X0) | m1_subset_1(k2_funct_1(k6_relat_1(X0)),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | (k1_xboole_0 = X0))))).
% 0.19/0.49  
% 0.19/0.49  tff(u366,axiom,
% 0.19/0.49      (![X0] : ((~v2_funct_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | (k2_relat_1(k6_relat_1(X0)) != X0) | v1_funct_2(k2_funct_1(k6_relat_1(X0)),X0,X0) | (k1_xboole_0 = X0))))).
% 0.19/0.49  
% 0.19/0.49  tff(u365,axiom,
% 0.19/0.49      (![X0] : ((~v2_funct_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | v1_funct_1(k2_funct_1(k6_relat_1(X0))))))).
% 0.19/0.49  
% 0.19/0.49  tff(u364,axiom,
% 0.19/0.49      ((~~v2_funct_1(k6_relat_1(k1_xboole_0))) | ~v2_funct_1(k6_relat_1(k1_xboole_0)))).
% 0.19/0.49  
% 0.19/0.49  tff(u363,axiom,
% 0.19/0.49      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2))))).
% 0.19/0.49  
% 0.19/0.49  tff(u362,axiom,
% 0.19/0.49      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (k1_relset_1(X0,X1,X2) = k1_relat_1(X2)))))).
% 0.19/0.49  
% 0.19/0.49  tff(u361,axiom,
% 0.19/0.49      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (k2_relset_1(X0,X1,X2) = k2_relat_1(X2)))))).
% 0.19/0.49  
% 0.19/0.49  tff(u360,axiom,
% 0.19/0.49      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0))))).
% 0.19/0.49  
% 0.19/0.49  tff(u359,axiom,
% 0.19/0.49      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (k1_xboole_0 = X1) | (k1_relset_1(X0,X1,X2) != X0) | v1_funct_2(X2,X0,X1))))).
% 0.19/0.49  
% 0.19/0.49  tff(u358,axiom,
% 0.19/0.49      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (k1_xboole_0 = X1) | (k1_relset_1(X0,X1,X2) = X0) | ~v1_funct_2(X2,X0,X1))))).
% 0.19/0.49  
% 0.19/0.49  tff(u357,axiom,
% 0.19/0.49      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | (k2_relset_1(X0,X1,X2) != X1) | v1_funct_2(k2_funct_1(X2),X1,X0))))).
% 0.19/0.49  
% 0.19/0.49  tff(u356,axiom,
% 0.19/0.49      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | (k2_relset_1(X0,X1,X2) != X1) | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))))).
% 0.19/0.49  
% 0.19/0.49  tff(u355,axiom,
% 0.19/0.49      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | v1_funct_1(k2_funct_1(X2)))))).
% 0.19/0.49  
% 0.19/0.49  tff(u354,axiom,
% 0.19/0.49      (![X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | (k1_xboole_0 = X0) | (k1_xboole_0 = X2) | ~v1_funct_2(X2,X0,k1_xboole_0))))).
% 0.19/0.49  
% 0.19/0.49  tff(u353,axiom,
% 0.19/0.49      (![X1, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)) | v1_funct_2(X2,k1_xboole_0,X1))))).
% 0.19/0.49  
% 0.19/0.49  tff(u352,axiom,
% 0.19/0.49      (![X1, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) | ~v1_funct_2(X2,k1_xboole_0,X1))))).
% 0.19/0.49  
% 0.19/0.49  tff(u351,axiom,
% 0.19/0.49      (![X0] : ((~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | (k1_xboole_0 = X0) | v1_funct_2(k1_xboole_0,X0,k1_xboole_0))))).
% 0.19/0.49  
% 0.19/0.49  tff(u350,axiom,
% 0.19/0.49      (![X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))))).
% 0.19/0.49  
% 0.19/0.49  tff(u349,negated_conjecture,
% 0.19/0.49      ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))))).
% 0.19/0.49  
% 0.19/0.49  tff(u348,axiom,
% 0.19/0.49      (![X1] : ((~v4_relat_1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1) | v1_partfun1(X1,k1_relat_1(X1)))))).
% 0.19/0.49  
% 0.19/0.49  tff(u347,axiom,
% 0.19/0.49      (![X0] : (v4_relat_1(k6_relat_1(X0),X0)))).
% 0.19/0.49  
% 0.19/0.49  tff(u346,negated_conjecture,
% 0.19/0.49      ((~v4_relat_1(sK2,k1_relat_1(sK2))) | v4_relat_1(sK2,k1_relat_1(sK2)))).
% 0.19/0.49  
% 0.19/0.49  tff(u345,axiom,
% 0.19/0.49      (![X0] : ((~v1_funct_2(k6_relat_1(X0),X0,X0) | (k2_relat_1(k6_relat_1(X0)) != X0) | ~v1_funct_1(k6_relat_1(X0)) | ~v2_funct_1(k6_relat_1(X0)) | m1_subset_1(k2_funct_1(k6_relat_1(X0)),k1_zfmisc_1(k2_zfmisc_1(X0,X0))))))).
% 0.19/0.49  
% 0.19/0.49  tff(u344,axiom,
% 0.19/0.49      (![X0] : ((~v1_funct_2(k6_relat_1(X0),X0,X0) | (k2_relat_1(k6_relat_1(X0)) != X0) | ~v1_funct_1(k6_relat_1(X0)) | ~v2_funct_1(k6_relat_1(X0)) | v1_funct_2(k2_funct_1(k6_relat_1(X0)),X0,X0))))).
% 0.19/0.49  
% 0.19/0.49  tff(u343,axiom,
% 0.19/0.49      ((~v1_funct_2(k6_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0)) | v1_funct_2(k6_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0))).
% 0.19/0.49  
% 0.19/0.49  tff(u342,axiom,
% 0.19/0.49      (![X0] : ((v1_funct_2(k6_relat_1(X0),X0,X0) | (k1_xboole_0 = X0))))).
% 0.19/0.49  
% 0.19/0.49  tff(u341,negated_conjecture,
% 0.19/0.49      ((~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))) | v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)))).
% 0.19/0.49  
% 0.19/0.49  tff(u340,axiom,
% 0.19/0.49      (![X1, X0] : ((~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | (k1_relat_1(X1) = X0) | ~v1_relat_1(X1))))).
% 0.19/0.49  
% 0.19/0.49  tff(u339,axiom,
% 0.19/0.49      (![X0] : (v1_partfun1(k6_relat_1(X0),X0)))).
% 0.19/0.49  
% 0.19/0.49  tff(u338,negated_conjecture,
% 0.19/0.49      ((~v1_partfun1(sK2,k1_relat_1(sK2))) | v1_partfun1(sK2,k1_relat_1(sK2)))).
% 0.19/0.49  
% 0.19/0.49  tff(u337,negated_conjecture,
% 0.19/0.49      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 0.19/0.49  
% 0.19/0.49  tff(u336,negated_conjecture,
% 0.19/0.49      ((~~v2_struct_0(sK1)) | ~v2_struct_0(sK1))).
% 0.19/0.49  
% 0.19/0.49  tff(u335,negated_conjecture,
% 0.19/0.49      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 0.19/0.49  
% 0.19/0.49  tff(u334,negated_conjecture,
% 0.19/0.49      ((~l1_struct_0(sK1)) | l1_struct_0(sK1))).
% 0.19/0.49  
% 0.19/0.49  tff(u333,axiom,
% 0.19/0.49      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.19/0.49  
% 0.19/0.49  tff(u332,negated_conjecture,
% 0.19/0.49      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.19/0.49  
% 0.19/0.49  tff(u331,negated_conjecture,
% 0.19/0.49      ((~l1_orders_2(sK1)) | l1_orders_2(sK1))).
% 0.19/0.49  
% 0.19/0.49  % (8807)# SZS output end Saturation.
% 0.19/0.49  % (8807)------------------------------
% 0.19/0.49  % (8807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (8807)Termination reason: Satisfiable
% 0.19/0.49  
% 0.19/0.49  % (8807)Memory used [KB]: 10874
% 0.19/0.49  % (8807)Time elapsed: 0.104 s
% 0.19/0.49  % (8807)------------------------------
% 0.19/0.49  % (8807)------------------------------
% 0.19/0.50  % (8805)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.50  % (8790)Success in time 0.141 s
%------------------------------------------------------------------------------
