%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:35 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   34 (  34 expanded)
%              Number of leaves         :   34 (  34 expanded)
%              Depth                    :    0
%              Number of atoms          :  133 ( 133 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal clause size      :    9 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u75,negated_conjecture,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0))) )).

cnf(u76,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),sK2(k6_tmap_1(sK0,u1_struct_0(sK1)),X0,X1))),X1,k7_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),sK2(k6_tmap_1(sK0,u1_struct_0(sK1)),X0,X1)))
    | ~ v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_pre_topc(X0,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X0)))))
    | v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | k9_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X0) = X1 )).

cnf(u31,axiom,
    ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2(X0,X1,X2))),X2,k7_tmap_1(X0,sK2(X0,X1,X2)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | v2_struct_0(X0)
    | k9_tmap_1(X0,X1) = X2 )).

cnf(u23,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k3_struct_0(sK0)) )).

cnf(u53,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) )).

cnf(u49,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(sK0,sK1)) )).

cnf(u22,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) )).

cnf(u27,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) )).

cnf(u35,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v1_funct_1(k9_tmap_1(X0,X1)) )).

cnf(u36,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) )).

cnf(u37,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) )).

cnf(u43,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) )).

% (4302)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
cnf(u57,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) )).

cnf(u45,negated_conjecture,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u78,negated_conjecture,
    ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X5)))))
    | ~ v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_pre_topc(X5,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X5)))
    | v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | u1_struct_0(X5) = sK2(k6_tmap_1(sK0,u1_struct_0(sK1)),X5,X4)
    | k9_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X5) = X4 )).

cnf(u77,negated_conjecture,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X3)))))
    | ~ v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_pre_topc(X3,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X3)))
    | v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | m1_subset_1(sK2(k6_tmap_1(sK0,u1_struct_0(sK1)),X3,X2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X3) = X2 )).

cnf(u30,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | v2_struct_0(X0)
    | u1_struct_0(X1) = sK2(X0,X1,X2)
    | k9_tmap_1(X0,X1) = X2 )).

cnf(u29,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | v2_struct_0(X0)
    | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | k9_tmap_1(X0,X1) = X2 )).

cnf(u80,negated_conjecture,
    ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X7)) )).

cnf(u81,negated_conjecture,
    ( ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X8) )).

cnf(u79,negated_conjecture,
    ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | u1_pre_topc(k6_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X6)) = k5_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X6) )).

cnf(u32,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) )).

cnf(u33,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )).

cnf(u34,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) )).

cnf(u25,negated_conjecture,
    ( v2_pre_topc(sK0) )).

cnf(u84,negated_conjecture,
    ( ~ v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK1))) )).

cnf(u85,negated_conjecture,
    ( ~ v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK1)) )).

cnf(u86,negated_conjecture,
    ( ~ v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | u1_pre_topc(k6_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK1))) = k5_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK1)) )).

cnf(u24,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u21,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u26,negated_conjecture,
    ( l1_pre_topc(sK0) )).

cnf(u67,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) = k5_tmap_1(sK0,u1_struct_0(sK1)) )).

cnf(u74,negated_conjecture,
    ( k7_tmap_1(sK0,u1_struct_0(sK1)) = k6_partfun1(u1_struct_0(sK0)) )).

cnf(u70,negated_conjecture,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:28:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (4293)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.42  % (4293)Refutation not found, incomplete strategy% (4293)------------------------------
% 0.20/0.42  % (4293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (4310)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.42  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.42  % (4310)# SZS output start Saturation.
% 0.20/0.42  cnf(u75,negated_conjecture,
% 0.20/0.42      r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)))).
% 0.20/0.42  
% 0.20/0.42  cnf(u76,negated_conjecture,
% 0.20/0.42      ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),sK2(k6_tmap_1(sK0,u1_struct_0(sK1)),X0,X1))),X1,k7_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),sK2(k6_tmap_1(sK0,u1_struct_0(sK1)),X0,X1))) | ~v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_pre_topc(X0,k6_tmap_1(sK0,u1_struct_0(sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X0))))) | v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | k9_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X0) = X1).
% 0.20/0.42  
% 0.20/0.42  cnf(u31,axiom,
% 0.20/0.42      ~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2(X0,X1,X2))),X2,k7_tmap_1(X0,sK2(X0,X1,X2))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | v2_struct_0(X0) | k9_tmap_1(X0,X1) = X2).
% 0.20/0.42  
% 0.20/0.42  cnf(u23,negated_conjecture,
% 0.20/0.42      ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k3_struct_0(sK0))).
% 0.20/0.42  
% 0.20/0.42  cnf(u53,negated_conjecture,
% 0.20/0.42      v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))).
% 0.20/0.42  
% 0.20/0.42  cnf(u49,negated_conjecture,
% 0.20/0.42      v1_funct_1(k9_tmap_1(sK0,sK1))).
% 0.20/0.42  
% 0.20/0.42  cnf(u22,negated_conjecture,
% 0.20/0.42      m1_pre_topc(sK1,sK0)).
% 0.20/0.42  
% 0.20/0.42  cnf(u27,axiom,
% 0.20/0.42      ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))).
% 0.20/0.42  
% 0.20/0.42  cnf(u35,axiom,
% 0.20/0.42      ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_funct_1(k9_tmap_1(X0,X1))).
% 0.20/0.42  
% 0.20/0.42  cnf(u36,axiom,
% 0.20/0.42      ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))).
% 0.20/0.42  
% 0.20/0.42  cnf(u37,axiom,
% 0.20/0.42      ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))).
% 0.20/0.42  
% 0.20/0.42  cnf(u43,axiom,
% 0.20/0.42      ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))).
% 0.20/0.42  
% 0.20/0.42  % (4302)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.42  cnf(u57,negated_conjecture,
% 0.20/0.42      m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))).
% 0.20/0.42  
% 0.20/0.42  cnf(u45,negated_conjecture,
% 0.20/0.42      m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.42  
% 0.20/0.42  cnf(u78,negated_conjecture,
% 0.20/0.42      ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X5))))) | ~v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_pre_topc(X5,k6_tmap_1(sK0,u1_struct_0(sK1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X5))) | v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | u1_struct_0(X5) = sK2(k6_tmap_1(sK0,u1_struct_0(sK1)),X5,X4) | k9_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X5) = X4).
% 0.20/0.42  
% 0.20/0.42  cnf(u77,negated_conjecture,
% 0.20/0.42      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X3))))) | ~v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_pre_topc(X3,k6_tmap_1(sK0,u1_struct_0(sK1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X3))) | v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | m1_subset_1(sK2(k6_tmap_1(sK0,u1_struct_0(sK1)),X3,X2),k1_zfmisc_1(u1_struct_0(sK0))) | k9_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X3) = X2).
% 0.20/0.42  
% 0.20/0.42  cnf(u30,axiom,
% 0.20/0.42      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | v2_struct_0(X0) | u1_struct_0(X1) = sK2(X0,X1,X2) | k9_tmap_1(X0,X1) = X2).
% 0.20/0.42  
% 0.20/0.42  cnf(u29,axiom,
% 0.20/0.42      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | v2_struct_0(X0) | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) = X2).
% 0.20/0.42  
% 0.20/0.42  cnf(u80,negated_conjecture,
% 0.20/0.42      ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X7))).
% 0.20/0.42  
% 0.20/0.43  cnf(u81,negated_conjecture,
% 0.20/0.43      ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X8)).
% 0.20/0.43  
% 0.20/0.43  cnf(u79,negated_conjecture,
% 0.20/0.43      ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | u1_pre_topc(k6_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X6)) = k5_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X6)).
% 0.20/0.43  
% 0.20/0.43  cnf(u32,axiom,
% 0.20/0.43      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))).
% 0.20/0.43  
% 0.20/0.43  cnf(u33,axiom,
% 0.20/0.43      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))).
% 0.20/0.43  
% 0.20/0.43  cnf(u34,axiom,
% 0.20/0.43      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)).
% 0.20/0.43  
% 0.20/0.43  cnf(u25,negated_conjecture,
% 0.20/0.43      v2_pre_topc(sK0)).
% 0.20/0.43  
% 0.20/0.43  cnf(u84,negated_conjecture,
% 0.20/0.43      ~v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK1)))).
% 0.20/0.43  
% 0.20/0.43  cnf(u85,negated_conjecture,
% 0.20/0.43      ~v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK1))).
% 0.20/0.43  
% 0.20/0.43  cnf(u86,negated_conjecture,
% 0.20/0.43      ~v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | u1_pre_topc(k6_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK1))) = k5_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK1))).
% 0.20/0.43  
% 0.20/0.43  cnf(u24,negated_conjecture,
% 0.20/0.43      ~v2_struct_0(sK0)).
% 0.20/0.43  
% 0.20/0.43  cnf(u21,negated_conjecture,
% 0.20/0.43      ~v2_struct_0(sK1)).
% 0.20/0.43  
% 0.20/0.43  cnf(u26,negated_conjecture,
% 0.20/0.43      l1_pre_topc(sK0)).
% 0.20/0.43  
% 0.20/0.43  cnf(u67,negated_conjecture,
% 0.20/0.43      u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) = k5_tmap_1(sK0,u1_struct_0(sK1))).
% 0.20/0.43  
% 0.20/0.43  cnf(u74,negated_conjecture,
% 0.20/0.43      k7_tmap_1(sK0,u1_struct_0(sK1)) = k6_partfun1(u1_struct_0(sK0))).
% 0.20/0.43  
% 0.20/0.43  cnf(u70,negated_conjecture,
% 0.20/0.43      u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))).
% 0.20/0.43  
% 0.20/0.43  % (4310)# SZS output end Saturation.
% 0.20/0.43  % (4310)------------------------------
% 0.20/0.43  % (4310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (4310)Termination reason: Satisfiable
% 0.20/0.43  
% 0.20/0.43  % (4310)Memory used [KB]: 1663
% 0.20/0.43  % (4310)Time elapsed: 0.006 s
% 0.20/0.43  % (4310)------------------------------
% 0.20/0.43  % (4310)------------------------------
% 0.20/0.43  % (4288)Success in time 0.075 s
%------------------------------------------------------------------------------
