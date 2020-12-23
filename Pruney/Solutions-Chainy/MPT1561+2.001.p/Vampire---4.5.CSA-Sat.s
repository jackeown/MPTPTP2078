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
% DateTime   : Thu Dec  3 13:16:08 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   72 (  72 expanded)
%              Number of leaves         :   72 (  72 expanded)
%              Depth                    :    0
%              Number of atoms          :  221 ( 221 expanded)
%              Number of equality atoms :   81 (  81 expanded)
%              Maximal clause size      :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u110,negated_conjecture,
    ( r2_lattice3(sK0,X0,sK1)
    | r2_hidden(sK2(sK0,X0,sK1),X0) )).

cnf(u112,negated_conjecture,
    ( r2_lattice3(sK0,X0,sK1)
    | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0)) )).

cnf(u60,axiom,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | r1_orders_2(X0,X4,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u111,negated_conjecture,
    ( r1_lattice3(sK0,X0,sK1)
    | r2_hidden(sK3(sK0,X0,sK1),X0) )).

cnf(u113,negated_conjecture,
    ( r1_lattice3(sK0,X0,sK1)
    | m1_subset_1(sK3(sK0,X0,sK1),u1_struct_0(sK0)) )).

cnf(u64,axiom,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | r1_orders_2(X0,X2,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u52,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u69,axiom,
    ( ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | X1 = X2 )).

cnf(u51,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u68,axiom,
    ( ~ v3_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_orders_2(X0,X1,X1)
    | v2_struct_0(X0) )).

cnf(u50,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u97,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1) )).

cnf(u107,negated_conjecture,
    ( ~ r1_orders_2(sK0,X0,X1)
    | ~ r1_orders_2(sK0,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | X0 = X1 )).

cnf(u58,axiom,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u67,axiom,
    ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
    | r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u63,axiom,
    ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
    | r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u53,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u57,axiom,
    ( ~ l1_orders_2(X0)
    | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )).

cnf(u62,axiom,
    ( ~ l1_orders_2(X0)
    | r2_hidden(sK2(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_lattice3(X0,X1,X2) )).

cnf(u66,axiom,
    ( ~ l1_orders_2(X0)
    | r2_hidden(sK3(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_lattice3(X0,X1,X2) )).

cnf(u61,axiom,
    ( ~ l1_orders_2(X0)
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_lattice3(X0,X1,X2) )).

cnf(u65,axiom,
    ( ~ l1_orders_2(X0)
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_lattice3(X0,X1,X2) )).

cnf(u59,axiom,
    ( ~ l1_orders_2(X0)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,X1,X2) )).

cnf(u87,negated_conjecture,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

cnf(u54,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u145,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r2_hidden(X1,X0)
    | m1_subset_1(sK3(sK0,X0,sK1),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,X1) )).

cnf(u141,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r2_hidden(X1,X0)
    | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0))
    | r1_orders_2(sK0,X1,sK1) )).

cnf(u138,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(sK3(sK0,X0,sK1),X0)
    | r1_orders_2(sK0,sK1,X1) )).

cnf(u135,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(sK2(sK0,X0,sK1),X0)
    | r1_orders_2(sK0,X1,sK1) )).

cnf(u115,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r2_hidden(k4_tarski(X0,sK1),u1_orders_2(sK0))
    | r1_orders_2(sK0,X0,sK1) )).

cnf(u101,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_orders_2(sK0,X0,X1) )).

cnf(u100,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0))
    | r1_lattice3(sK0,X0,X1) )).

cnf(u99,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
    | r2_lattice3(sK0,X0,X1) )).

cnf(u98,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r2_hidden(sK3(sK0,X0,X1),X0)
    | r1_lattice3(sK0,X0,X1) )).

cnf(u96,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r2_hidden(sK2(sK0,X0,X1),X0)
    | r2_lattice3(sK0,X0,X1) )).

cnf(u91,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_orders_2(sK0,X0,X0) )).

cnf(u74,axiom,
    ( ~ m1_subset_1(X1,X0)
    | k6_domain_1(X0,X1) = k1_tarski(X1)
    | v1_xboole_0(X0) )).

cnf(u73,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X2)
    | ~ v1_xboole_0(X0) )).

cnf(u77,axiom,
    ( r2_hidden(sK5(X0,X1),X1)
    | sK5(X0,X1) = X0
    | k1_tarski(X0) = X1 )).

cnf(u71,axiom,
    ( r2_hidden(sK4(X0),X0)
    | v1_xboole_0(X0) )).

cnf(u105,negated_conjecture,
    ( r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0)) )).

cnf(u80,axiom,
    ( r2_hidden(X3,k1_tarski(X3)) )).

cnf(u301,axiom,
    ( ~ r2_hidden(sK5(X14,k1_tarski(X13)),k1_tarski(X13))
    | sK5(X14,k1_tarski(X13)) != X12
    | k1_tarski(X13) = k1_tarski(X12)
    | sK5(X12,k1_tarski(X13)) = X12
    | k1_tarski(X13) = k1_tarski(X14) )).

cnf(u78,axiom,
    ( ~ r2_hidden(sK5(X0,X1),X1)
    | sK5(X0,X1) != X0
    | k1_tarski(X0) = X1 )).

cnf(u169,negated_conjecture,
    ( ~ r2_hidden(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | k1_tarski(X0) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)) = k1_tarski(u1_orders_2(sK0)) )).

cnf(u81,axiom,
    ( ~ r2_hidden(X3,k1_tarski(X0))
    | X0 = X3 )).

cnf(u131,axiom,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | k1_tarski(X0) = k1_tarski(X1)
    | sK5(X0,k1_tarski(X1)) = X1 )).

cnf(u187,axiom,
    ( ~ r2_hidden(X4,k1_tarski(X3))
    | sK5(X2,k1_tarski(X3)) = X4
    | sK5(X2,k1_tarski(X3)) = X2
    | k1_tarski(X3) = k1_tarski(X2) )).

cnf(u192,axiom,
    ( ~ r2_hidden(X17,k1_tarski(X16))
    | k1_tarski(X16) = k1_tarski(X17)
    | sK5(X15,k1_tarski(X16)) = sK5(X17,k1_tarski(X16))
    | sK5(X15,k1_tarski(X16)) = X15
    | k1_tarski(X16) = k1_tarski(X15) )).

cnf(u70,axiom,
    ( ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X0) )).

cnf(u109,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)) = k1_tarski(u1_orders_2(sK0)) )).

cnf(u142,negated_conjecture,
    ( ~ v1_xboole_0(u1_orders_2(sK0)) )).

cnf(u108,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_orders_2(sK0)) )).

cnf(u82,axiom,
    ( ~ v1_xboole_0(k1_tarski(X0)) )).

cnf(u92,axiom,
    ( ~ v1_xboole_0(X1)
    | k1_tarski(X0) = X1
    | sK5(X0,X1) = X0 )).

cnf(u156,axiom,
    ( sK5(sK5(X2,k1_tarski(X3)),k1_tarski(X3)) = X3
    | k1_tarski(X3) = k1_tarski(sK5(X2,k1_tarski(X3)))
    | sK5(X2,k1_tarski(X3)) = X2
    | k1_tarski(X3) = k1_tarski(X2) )).

cnf(u151,negated_conjecture,
    ( k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)) = k1_tarski(u1_orders_2(sK0))
    | sK5(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = X0
    | k1_tarski(X0) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u190,axiom,
    ( sK5(X11,k1_tarski(X10)) = X11
    | sK5(X9,k1_tarski(X10)) = sK5(X11,k1_tarski(X10))
    | sK5(X9,k1_tarski(X10)) = X9
    | k1_tarski(X10) = k1_tarski(X11)
    | k1_tarski(X10) = k1_tarski(X9) )).

cnf(u93,axiom,
    ( sK5(X2,k1_tarski(X3)) = X2
    | sK5(X2,k1_tarski(X3)) = X3
    | k1_tarski(X3) = k1_tarski(X2) )).

cnf(u93_001,axiom,
    ( sK5(X2,k1_tarski(X3)) = X2
    | sK5(X2,k1_tarski(X3)) = X3
    | k1_tarski(X3) = k1_tarski(X2) )).

cnf(u190_002,axiom,
    ( sK5(X11,k1_tarski(X10)) = X11
    | sK5(X9,k1_tarski(X10)) = sK5(X11,k1_tarski(X10))
    | sK5(X9,k1_tarski(X10)) = X9
    | k1_tarski(X10) = k1_tarski(X11)
    | k1_tarski(X10) = k1_tarski(X9) )).

cnf(u190_003,axiom,
    ( sK5(X11,k1_tarski(X10)) = X11
    | sK5(X9,k1_tarski(X10)) = sK5(X11,k1_tarski(X10))
    | sK5(X9,k1_tarski(X10)) = X9
    | k1_tarski(X10) = k1_tarski(X11)
    | k1_tarski(X10) = k1_tarski(X9) )).

cnf(u86,axiom,
    ( sK4(k1_tarski(X1)) = X1 )).

cnf(u159,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) )).

cnf(u151_004,negated_conjecture,
    ( k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)) = k1_tarski(u1_orders_2(sK0))
    | sK5(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = X0
    | k1_tarski(X0) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u181,axiom,
    ( k1_tarski(X5) = k1_tarski(sK5(X4,k1_tarski(X5)))
    | sK5(X4,k1_tarski(X5)) = X4
    | k1_tarski(X5) = k1_tarski(X4) )).

cnf(u56,axiom,
    ( k1_tarski(X0) = k3_relat_1(k1_tarski(k4_tarski(X0,X0))) )).

cnf(u259,axiom,
    ( sK5(X2,k1_tarski(X1)) != X0
    | sK5(X2,k1_tarski(X1)) = X2
    | sK5(X0,k1_tarski(X1)) = X0
    | k1_tarski(X1) = k1_tarski(X2)
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u257,axiom,
    ( sK5(X2,k1_tarski(X1)) != X0
    | sK5(X0,k1_tarski(X1)) = sK5(X2,k1_tarski(X1))
    | sK5(X2,k1_tarski(X1)) = X2
    | k1_tarski(X0) = k1_tarski(X1)
    | k1_tarski(X1) = k1_tarski(X2) )).

cnf(u161,negated_conjecture,
    ( sK1 != k2_yellow_0(sK0,k1_tarski(sK1))
    | sK1 != k1_yellow_0(sK0,k1_tarski(sK1)) )).

cnf(u126,axiom,
    ( X0 != X1
    | sK5(X0,k1_tarski(X1)) = X1
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u132,axiom,
    ( X0 != X1
    | k1_tarski(X0) = k1_tarski(X1)
    | sK5(X0,k1_tarski(X1)) = X0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:37:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (4055)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.49  % (4045)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.49  % (4043)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.50  % (4055)Refutation not found, incomplete strategy% (4055)------------------------------
% 0.21/0.50  % (4055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (4055)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (4055)Memory used [KB]: 10618
% 0.21/0.50  % (4055)Time elapsed: 0.057 s
% 0.21/0.50  % (4055)------------------------------
% 0.21/0.50  % (4055)------------------------------
% 0.21/0.50  % (4037)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (4031)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.50  % (4061)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (4032)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.50  % (4032)Refutation not found, incomplete strategy% (4032)------------------------------
% 0.21/0.50  % (4032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (4032)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (4032)Memory used [KB]: 1663
% 0.21/0.50  % (4032)Time elapsed: 0.098 s
% 0.21/0.50  % (4032)------------------------------
% 0.21/0.50  % (4032)------------------------------
% 0.21/0.51  % (4043)Refutation not found, incomplete strategy% (4043)------------------------------
% 0.21/0.51  % (4043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4035)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (4043)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (4043)Memory used [KB]: 10746
% 0.21/0.51  % (4043)Time elapsed: 0.094 s
% 0.21/0.51  % (4043)------------------------------
% 0.21/0.51  % (4043)------------------------------
% 0.21/0.51  % (4042)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.51  % (4041)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.51  % (4051)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.51  % (4041)Refutation not found, incomplete strategy% (4041)------------------------------
% 0.21/0.51  % (4041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4041)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (4041)Memory used [KB]: 10746
% 0.21/0.51  % (4041)Time elapsed: 0.106 s
% 0.21/0.51  % (4041)------------------------------
% 0.21/0.51  % (4041)------------------------------
% 0.21/0.51  % (4061)Refutation not found, incomplete strategy% (4061)------------------------------
% 0.21/0.51  % (4061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4061)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (4061)Memory used [KB]: 1663
% 0.21/0.51  % (4061)Time elapsed: 0.105 s
% 0.21/0.51  % (4061)------------------------------
% 0.21/0.51  % (4061)------------------------------
% 0.21/0.52  % (4036)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (4040)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (4047)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.52  % (4038)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (4036)Refutation not found, incomplete strategy% (4036)------------------------------
% 0.21/0.52  % (4036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (4036)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (4036)Memory used [KB]: 1791
% 0.21/0.52  % (4036)Time elapsed: 0.121 s
% 0.21/0.52  % (4036)------------------------------
% 0.21/0.52  % (4036)------------------------------
% 0.21/0.52  % (4059)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.52  % (4033)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (4054)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (4039)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (4044)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (4049)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (4050)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (4049)Refutation not found, incomplete strategy% (4049)------------------------------
% 0.21/0.53  % (4049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4049)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (4049)Memory used [KB]: 1663
% 0.21/0.53  % (4049)Time elapsed: 0.133 s
% 0.21/0.53  % (4049)------------------------------
% 0.21/0.53  % (4049)------------------------------
% 0.21/0.53  % (4052)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (4034)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (4058)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (4035)Refutation not found, incomplete strategy% (4035)------------------------------
% 0.21/0.53  % (4035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4035)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (4035)Memory used [KB]: 1791
% 0.21/0.53  % (4035)Time elapsed: 0.113 s
% 0.21/0.53  % (4035)------------------------------
% 0.21/0.53  % (4035)------------------------------
% 0.21/0.53  % (4058)Refutation not found, incomplete strategy% (4058)------------------------------
% 0.21/0.53  % (4058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4058)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (4058)Memory used [KB]: 6140
% 0.21/0.53  % (4058)Time elapsed: 0.130 s
% 0.21/0.53  % (4058)------------------------------
% 0.21/0.53  % (4058)------------------------------
% 0.21/0.53  % (4056)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  % (4048)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (4056)Refutation not found, incomplete strategy% (4056)------------------------------
% 0.21/0.53  % (4056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4056)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (4056)Memory used [KB]: 6268
% 0.21/0.53  % (4056)Time elapsed: 0.130 s
% 0.21/0.53  % (4056)------------------------------
% 0.21/0.53  % (4056)------------------------------
% 0.21/0.53  % (4048)Refutation not found, incomplete strategy% (4048)------------------------------
% 0.21/0.53  % (4048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4048)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (4048)Memory used [KB]: 1791
% 0.21/0.53  % (4048)Time elapsed: 0.131 s
% 0.21/0.53  % (4048)------------------------------
% 0.21/0.53  % (4048)------------------------------
% 0.21/0.53  % (4053)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (4057)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (4046)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (4057)Refutation not found, incomplete strategy% (4057)------------------------------
% 0.21/0.54  % (4057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4057)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4057)Memory used [KB]: 6268
% 0.21/0.54  % (4057)Time elapsed: 0.130 s
% 0.21/0.54  % (4057)------------------------------
% 0.21/0.54  % (4057)------------------------------
% 0.21/0.54  % (4059)Refutation not found, incomplete strategy% (4059)------------------------------
% 0.21/0.54  % (4059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4059)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4059)Memory used [KB]: 10746
% 0.21/0.54  % (4059)Time elapsed: 0.143 s
% 0.21/0.54  % (4059)------------------------------
% 0.21/0.54  % (4059)------------------------------
% 0.21/0.54  % (4047)Refutation not found, incomplete strategy% (4047)------------------------------
% 0.21/0.54  % (4047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4047)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4047)Memory used [KB]: 10618
% 0.21/0.54  % (4047)Time elapsed: 0.143 s
% 0.21/0.54  % (4047)------------------------------
% 0.21/0.54  % (4047)------------------------------
% 0.21/0.54  % (4054)Refutation not found, incomplete strategy% (4054)------------------------------
% 0.21/0.54  % (4054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4054)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4054)Memory used [KB]: 10746
% 0.21/0.54  % (4054)Time elapsed: 0.125 s
% 0.21/0.54  % (4054)------------------------------
% 0.21/0.54  % (4054)------------------------------
% 0.21/0.55  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.55  % (4038)# SZS output start Saturation.
% 0.21/0.55  cnf(u110,negated_conjecture,
% 0.21/0.55      r2_lattice3(sK0,X0,sK1) | r2_hidden(sK2(sK0,X0,sK1),X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u112,negated_conjecture,
% 0.21/0.55      r2_lattice3(sK0,X0,sK1) | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u60,axiom,
% 0.21/0.55      ~r2_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X4,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u111,negated_conjecture,
% 0.21/0.55      r1_lattice3(sK0,X0,sK1) | r2_hidden(sK3(sK0,X0,sK1),X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u113,negated_conjecture,
% 0.21/0.55      r1_lattice3(sK0,X0,sK1) | m1_subset_1(sK3(sK0,X0,sK1),u1_struct_0(sK0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u64,axiom,
% 0.21/0.55      ~r1_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X2,X4) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u52,negated_conjecture,
% 0.21/0.55      v5_orders_2(sK0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u69,axiom,
% 0.21/0.55      ~v5_orders_2(X0) | ~r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | X1 = X2).
% 0.21/0.55  
% 0.21/0.55  cnf(u51,negated_conjecture,
% 0.21/0.55      v3_orders_2(sK0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u68,axiom,
% 0.21/0.55      ~v3_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X1) | v2_struct_0(X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u50,negated_conjecture,
% 0.21/0.55      ~v2_struct_0(sK0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u97,negated_conjecture,
% 0.21/0.55      r1_orders_2(sK0,sK1,sK1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u107,negated_conjecture,
% 0.21/0.55      ~r1_orders_2(sK0,X0,X1) | ~r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | X0 = X1).
% 0.21/0.55  
% 0.21/0.55  cnf(u58,axiom,
% 0.21/0.55      ~r1_orders_2(X0,X1,X2) | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u67,axiom,
% 0.21/0.55      ~r1_orders_2(X0,X2,sK3(X0,X1,X2)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u63,axiom,
% 0.21/0.55      ~r1_orders_2(X0,sK2(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u53,negated_conjecture,
% 0.21/0.55      l1_orders_2(sK0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u57,axiom,
% 0.21/0.55      ~l1_orders_2(X0) | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))).
% 0.21/0.55  
% 0.21/0.55  cnf(u62,axiom,
% 0.21/0.55      ~l1_orders_2(X0) | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_lattice3(X0,X1,X2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u66,axiom,
% 0.21/0.55      ~l1_orders_2(X0) | r2_hidden(sK3(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattice3(X0,X1,X2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u61,axiom,
% 0.21/0.55      ~l1_orders_2(X0) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_lattice3(X0,X1,X2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u65,axiom,
% 0.21/0.55      ~l1_orders_2(X0) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattice3(X0,X1,X2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u59,axiom,
% 0.21/0.55      ~l1_orders_2(X0) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u87,negated_conjecture,
% 0.21/0.55      m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 0.21/0.55  
% 0.21/0.55  cnf(u54,negated_conjecture,
% 0.21/0.55      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u145,negated_conjecture,
% 0.21/0.55      ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | m1_subset_1(sK3(sK0,X0,sK1),u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u141,negated_conjecture,
% 0.21/0.55      ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0)) | r1_orders_2(sK0,X1,sK1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u138,negated_conjecture,
% 0.21/0.55      ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r2_hidden(sK3(sK0,X0,sK1),X0) | r1_orders_2(sK0,sK1,X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u135,negated_conjecture,
% 0.21/0.55      ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r2_hidden(sK2(sK0,X0,sK1),X0) | r1_orders_2(sK0,X1,sK1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u115,negated_conjecture,
% 0.21/0.55      ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(k4_tarski(X0,sK1),u1_orders_2(sK0)) | r1_orders_2(sK0,X0,sK1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u101,negated_conjecture,
% 0.21/0.55      ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u100,negated_conjecture,
% 0.21/0.55      ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0)) | r1_lattice3(sK0,X0,X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u99,negated_conjecture,
% 0.21/0.55      ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u98,negated_conjecture,
% 0.21/0.55      ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(sK3(sK0,X0,X1),X0) | r1_lattice3(sK0,X0,X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u96,negated_conjecture,
% 0.21/0.55      ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(sK2(sK0,X0,X1),X0) | r2_lattice3(sK0,X0,X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u91,negated_conjecture,
% 0.21/0.55      ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u74,axiom,
% 0.21/0.55      ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u73,axiom,
% 0.21/0.55      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u77,axiom,
% 0.21/0.55      r2_hidden(sK5(X0,X1),X1) | sK5(X0,X1) = X0 | k1_tarski(X0) = X1).
% 0.21/0.55  
% 0.21/0.55  cnf(u71,axiom,
% 0.21/0.55      r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u105,negated_conjecture,
% 0.21/0.55      r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u80,axiom,
% 0.21/0.55      r2_hidden(X3,k1_tarski(X3))).
% 0.21/0.55  
% 0.21/0.55  cnf(u301,axiom,
% 0.21/0.55      ~r2_hidden(sK5(X14,k1_tarski(X13)),k1_tarski(X13)) | sK5(X14,k1_tarski(X13)) != X12 | k1_tarski(X13) = k1_tarski(X12) | sK5(X12,k1_tarski(X13)) = X12 | k1_tarski(X13) = k1_tarski(X14)).
% 0.21/0.55  
% 0.21/0.55  cnf(u78,axiom,
% 0.21/0.55      ~r2_hidden(sK5(X0,X1),X1) | sK5(X0,X1) != X0 | k1_tarski(X0) = X1).
% 0.21/0.55  
% 0.21/0.55  cnf(u169,negated_conjecture,
% 0.21/0.55      ~r2_hidden(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | k1_tarski(X0) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) | k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)) = k1_tarski(u1_orders_2(sK0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u81,axiom,
% 0.21/0.55      ~r2_hidden(X3,k1_tarski(X0)) | X0 = X3).
% 0.21/0.55  
% 0.21/0.55  cnf(u131,axiom,
% 0.21/0.55      ~r2_hidden(X0,k1_tarski(X1)) | k1_tarski(X0) = k1_tarski(X1) | sK5(X0,k1_tarski(X1)) = X1).
% 0.21/0.55  
% 0.21/0.55  cnf(u187,axiom,
% 0.21/0.55      ~r2_hidden(X4,k1_tarski(X3)) | sK5(X2,k1_tarski(X3)) = X4 | sK5(X2,k1_tarski(X3)) = X2 | k1_tarski(X3) = k1_tarski(X2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u192,axiom,
% 0.21/0.55      ~r2_hidden(X17,k1_tarski(X16)) | k1_tarski(X16) = k1_tarski(X17) | sK5(X15,k1_tarski(X16)) = sK5(X17,k1_tarski(X16)) | sK5(X15,k1_tarski(X16)) = X15 | k1_tarski(X16) = k1_tarski(X15)).
% 0.21/0.55  
% 0.21/0.55  cnf(u70,axiom,
% 0.21/0.55      ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u109,negated_conjecture,
% 0.21/0.55      v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)) = k1_tarski(u1_orders_2(sK0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u142,negated_conjecture,
% 0.21/0.55      ~v1_xboole_0(u1_orders_2(sK0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u108,negated_conjecture,
% 0.21/0.55      ~v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_orders_2(sK0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u82,axiom,
% 0.21/0.55      ~v1_xboole_0(k1_tarski(X0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u92,axiom,
% 0.21/0.55      ~v1_xboole_0(X1) | k1_tarski(X0) = X1 | sK5(X0,X1) = X0).
% 0.21/0.55  
% 0.21/0.55  cnf(u156,axiom,
% 0.21/0.55      sK5(sK5(X2,k1_tarski(X3)),k1_tarski(X3)) = X3 | k1_tarski(X3) = k1_tarski(sK5(X2,k1_tarski(X3))) | sK5(X2,k1_tarski(X3)) = X2 | k1_tarski(X3) = k1_tarski(X2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u151,negated_conjecture,
% 0.21/0.55      k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)) = k1_tarski(u1_orders_2(sK0)) | sK5(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = X0 | k1_tarski(X0) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))).
% 0.21/0.55  
% 0.21/0.55  cnf(u190,axiom,
% 0.21/0.55      sK5(X11,k1_tarski(X10)) = X11 | sK5(X9,k1_tarski(X10)) = sK5(X11,k1_tarski(X10)) | sK5(X9,k1_tarski(X10)) = X9 | k1_tarski(X10) = k1_tarski(X11) | k1_tarski(X10) = k1_tarski(X9)).
% 0.21/0.55  
% 0.21/0.55  cnf(u93,axiom,
% 0.21/0.55      sK5(X2,k1_tarski(X3)) = X2 | sK5(X2,k1_tarski(X3)) = X3 | k1_tarski(X3) = k1_tarski(X2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u93,axiom,
% 0.21/0.55      sK5(X2,k1_tarski(X3)) = X2 | sK5(X2,k1_tarski(X3)) = X3 | k1_tarski(X3) = k1_tarski(X2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u190,axiom,
% 0.21/0.55      sK5(X11,k1_tarski(X10)) = X11 | sK5(X9,k1_tarski(X10)) = sK5(X11,k1_tarski(X10)) | sK5(X9,k1_tarski(X10)) = X9 | k1_tarski(X10) = k1_tarski(X11) | k1_tarski(X10) = k1_tarski(X9)).
% 0.21/0.55  
% 0.21/0.55  cnf(u190,axiom,
% 0.21/0.55      sK5(X11,k1_tarski(X10)) = X11 | sK5(X9,k1_tarski(X10)) = sK5(X11,k1_tarski(X10)) | sK5(X9,k1_tarski(X10)) = X9 | k1_tarski(X10) = k1_tarski(X11) | k1_tarski(X10) = k1_tarski(X9)).
% 0.21/0.55  
% 0.21/0.55  cnf(u86,axiom,
% 0.21/0.55      sK4(k1_tarski(X1)) = X1).
% 0.21/0.55  
% 0.21/0.55  cnf(u159,negated_conjecture,
% 0.21/0.55      k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u151,negated_conjecture,
% 0.21/0.55      k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)) = k1_tarski(u1_orders_2(sK0)) | sK5(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = X0 | k1_tarski(X0) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))).
% 0.21/0.55  
% 0.21/0.55  cnf(u181,axiom,
% 0.21/0.55      k1_tarski(X5) = k1_tarski(sK5(X4,k1_tarski(X5))) | sK5(X4,k1_tarski(X5)) = X4 | k1_tarski(X5) = k1_tarski(X4)).
% 0.21/0.55  
% 0.21/0.55  cnf(u56,axiom,
% 0.21/0.55      k1_tarski(X0) = k3_relat_1(k1_tarski(k4_tarski(X0,X0)))).
% 0.21/0.55  
% 0.21/0.55  cnf(u259,axiom,
% 0.21/0.55      sK5(X2,k1_tarski(X1)) != X0 | sK5(X2,k1_tarski(X1)) = X2 | sK5(X0,k1_tarski(X1)) = X0 | k1_tarski(X1) = k1_tarski(X2) | k1_tarski(X0) = k1_tarski(X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u257,axiom,
% 0.21/0.55      sK5(X2,k1_tarski(X1)) != X0 | sK5(X0,k1_tarski(X1)) = sK5(X2,k1_tarski(X1)) | sK5(X2,k1_tarski(X1)) = X2 | k1_tarski(X0) = k1_tarski(X1) | k1_tarski(X1) = k1_tarski(X2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u161,negated_conjecture,
% 0.21/0.55      sK1 != k2_yellow_0(sK0,k1_tarski(sK1)) | sK1 != k1_yellow_0(sK0,k1_tarski(sK1))).
% 0.21/0.55  
% 0.21/0.55  cnf(u126,axiom,
% 0.21/0.55      X0 != X1 | sK5(X0,k1_tarski(X1)) = X1 | k1_tarski(X0) = k1_tarski(X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u132,axiom,
% 0.21/0.55      X0 != X1 | k1_tarski(X0) = k1_tarski(X1) | sK5(X0,k1_tarski(X1)) = X0).
% 0.21/0.55  
% 0.21/0.55  % (4038)# SZS output end Saturation.
% 0.21/0.55  % (4038)------------------------------
% 0.21/0.55  % (4038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (4038)Termination reason: Satisfiable
% 0.21/0.55  
% 0.21/0.55  % (4038)Memory used [KB]: 1918
% 0.21/0.55  % (4038)Time elapsed: 0.129 s
% 0.21/0.55  % (4038)------------------------------
% 0.21/0.55  % (4038)------------------------------
% 0.21/0.55  % (4030)Success in time 0.187 s
%------------------------------------------------------------------------------
