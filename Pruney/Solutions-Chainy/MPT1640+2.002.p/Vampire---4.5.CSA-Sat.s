%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:59 EST 2020

% Result     : CounterSatisfiable 2.82s
% Output     : Saturation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of leaves         :   27 (  27 expanded)
%              Depth                    :    0
%              Number of atoms          :   65 (  65 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u206,negated_conjecture,
    ( ~ ( sK1 != sK2 )
    | sK1 != sK2 )).

tff(u205,negated_conjecture,
    ( k6_waybel_0(sK0,sK1) != k6_waybel_0(sK0,sK2)
    | k6_waybel_0(sK0,sK1) = k6_waybel_0(sK0,sK2) )).

tff(u204,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) )).

tff(u203,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK2) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k6_domain_1(u1_struct_0(sK0),sK2) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) )).

tff(u202,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) )).

tff(u201,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) )).

tff(u200,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ! [X0] :
        ( ~ r1_tarski(k6_domain_1(u1_struct_0(sK0),sK1),X0)
        | r2_hidden(sK1,X0) ) )).

tff(u199,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK2) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | ! [X0] :
        ( ~ r1_tarski(k6_domain_1(u1_struct_0(sK0),sK2),X0)
        | r2_hidden(sK2,X0) ) )).

tff(u198,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X1,X2)
      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) )).

tff(u197,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u196,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

tff(u195,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u194,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0)) )).

tff(u193,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u192,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )).

tff(u191,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
      | v1_xboole_0(X0) ) )).

tff(u190,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) )).

tff(u189,negated_conjecture,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u188,negated_conjecture,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u187,negated_conjecture,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u186,negated_conjecture,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u185,negated_conjecture,
    ( ~ m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k6_domain_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k6_domain_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )).

tff(u184,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u183,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u182,negated_conjecture,
    ( ~ v5_orders_2(sK0)
    | v5_orders_2(sK0) )).

tff(u181,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X2,X1)
      | X1 = X2
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) )).

tff(u180,negated_conjecture,
    ( ~ v3_orders_2(sK0)
    | v3_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n008.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 14:16:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (19497)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (19512)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.47  % (19512)Refutation not found, incomplete strategy% (19512)------------------------------
% 0.21/0.47  % (19512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (19512)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (19512)Memory used [KB]: 6268
% 0.21/0.47  % (19512)Time elapsed: 0.065 s
% 0.21/0.47  % (19512)------------------------------
% 0.21/0.47  % (19512)------------------------------
% 0.21/0.50  % (19495)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.50  % (19496)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (19496)Refutation not found, incomplete strategy% (19496)------------------------------
% 0.21/0.50  % (19496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (19496)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (19496)Memory used [KB]: 1663
% 0.21/0.50  % (19496)Time elapsed: 0.098 s
% 0.21/0.50  % (19496)------------------------------
% 0.21/0.50  % (19496)------------------------------
% 0.21/0.51  % (19492)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (19516)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.51  % (19492)Refutation not found, incomplete strategy% (19492)------------------------------
% 0.21/0.51  % (19492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (19492)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (19492)Memory used [KB]: 1663
% 0.21/0.51  % (19492)Time elapsed: 0.106 s
% 0.21/0.51  % (19492)------------------------------
% 0.21/0.51  % (19492)------------------------------
% 0.21/0.51  % (19493)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (19513)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (19513)Refutation not found, incomplete strategy% (19513)------------------------------
% 0.21/0.51  % (19513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (19513)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (19513)Memory used [KB]: 6268
% 0.21/0.51  % (19513)Time elapsed: 0.083 s
% 0.21/0.51  % (19513)------------------------------
% 0.21/0.51  % (19513)------------------------------
% 0.21/0.51  % (19508)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.51  % (19508)Refutation not found, incomplete strategy% (19508)------------------------------
% 0.21/0.51  % (19508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (19508)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (19508)Memory used [KB]: 1663
% 0.21/0.51  % (19508)Time elapsed: 0.114 s
% 0.21/0.51  % (19508)------------------------------
% 0.21/0.51  % (19508)------------------------------
% 0.21/0.51  % (19505)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (19498)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (19505)Refutation not found, incomplete strategy% (19505)------------------------------
% 0.21/0.52  % (19505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19505)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (19505)Memory used [KB]: 1791
% 0.21/0.52  % (19505)Time elapsed: 0.093 s
% 0.21/0.52  % (19505)------------------------------
% 0.21/0.52  % (19505)------------------------------
% 0.21/0.52  % (19502)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (19506)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (19503)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (19501)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (19515)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.52  % (19500)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (19500)Refutation not found, incomplete strategy% (19500)------------------------------
% 0.21/0.52  % (19500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19500)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (19500)Memory used [KB]: 1663
% 0.21/0.52  % (19500)Time elapsed: 0.098 s
% 0.21/0.52  % (19500)------------------------------
% 0.21/0.52  % (19500)------------------------------
% 0.21/0.52  % (19515)Refutation not found, incomplete strategy% (19515)------------------------------
% 0.21/0.52  % (19515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19515)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (19515)Memory used [KB]: 10618
% 0.21/0.52  % (19515)Time elapsed: 0.121 s
% 0.21/0.52  % (19515)------------------------------
% 0.21/0.52  % (19515)------------------------------
% 0.21/0.52  % (19504)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (19495)Refutation not found, incomplete strategy% (19495)------------------------------
% 0.21/0.52  % (19495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19495)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (19495)Memory used [KB]: 1791
% 0.21/0.52  % (19495)Time elapsed: 0.122 s
% 0.21/0.52  % (19495)------------------------------
% 0.21/0.52  % (19495)------------------------------
% 0.21/0.52  % (19494)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (19516)Refutation not found, incomplete strategy% (19516)------------------------------
% 0.21/0.52  % (19516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19516)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (19516)Memory used [KB]: 6268
% 0.21/0.52  % (19516)Time elapsed: 0.133 s
% 0.21/0.52  % (19516)------------------------------
% 0.21/0.52  % (19516)------------------------------
% 0.21/0.53  % (19518)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (19514)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (19510)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (19520)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (19503)Refutation not found, incomplete strategy% (19503)------------------------------
% 0.21/0.53  % (19503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (19511)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (19503)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (19503)Memory used [KB]: 10618
% 0.21/0.53  % (19503)Time elapsed: 0.133 s
% 0.21/0.53  % (19503)------------------------------
% 0.21/0.53  % (19503)------------------------------
% 0.21/0.53  % (19517)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (19499)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.46/0.53  % (19501)Refutation not found, incomplete strategy% (19501)------------------------------
% 1.46/0.53  % (19501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.53  % (19517)Refutation not found, incomplete strategy% (19517)------------------------------
% 1.46/0.53  % (19517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.53  % (19517)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.53  
% 1.46/0.53  % (19517)Memory used [KB]: 6268
% 1.46/0.53  % (19517)Time elapsed: 0.141 s
% 1.46/0.53  % (19517)------------------------------
% 1.46/0.53  % (19517)------------------------------
% 1.46/0.54  % (19491)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.46/0.54  % (19510)Refutation not found, incomplete strategy% (19510)------------------------------
% 1.46/0.54  % (19510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.54  % (19510)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.54  
% 1.46/0.54  % (19510)Memory used [KB]: 1663
% 1.46/0.54  % (19510)Time elapsed: 0.141 s
% 1.46/0.54  % (19510)------------------------------
% 1.46/0.54  % (19510)------------------------------
% 1.46/0.54  % (19507)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.46/0.54  % (19501)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.54  
% 1.46/0.54  % (19501)Memory used [KB]: 10746
% 1.46/0.54  % (19501)Time elapsed: 0.144 s
% 1.46/0.54  % (19501)------------------------------
% 1.46/0.54  % (19501)------------------------------
% 1.46/0.54  % (19507)Refutation not found, incomplete strategy% (19507)------------------------------
% 1.46/0.54  % (19507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.54  % (19507)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.54  
% 1.46/0.54  % (19507)Memory used [KB]: 10618
% 1.46/0.54  % (19507)Time elapsed: 0.141 s
% 1.46/0.54  % (19507)------------------------------
% 1.46/0.54  % (19507)------------------------------
% 1.46/0.54  % (19519)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.46/0.54  % (19518)Refutation not found, incomplete strategy% (19518)------------------------------
% 1.46/0.54  % (19518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.54  % (19518)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.54  
% 1.46/0.54  % (19518)Memory used [KB]: 6140
% 1.46/0.54  % (19518)Time elapsed: 0.142 s
% 1.46/0.54  % (19518)------------------------------
% 1.46/0.54  % (19518)------------------------------
% 1.46/0.54  % (19520)Refutation not found, incomplete strategy% (19520)------------------------------
% 1.46/0.54  % (19520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.54  % (19520)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.54  
% 1.46/0.54  % (19520)Memory used [KB]: 1663
% 1.46/0.54  % (19520)Time elapsed: 0.003 s
% 1.46/0.54  % (19520)------------------------------
% 1.46/0.54  % (19520)------------------------------
% 1.46/0.54  % (19519)Refutation not found, incomplete strategy% (19519)------------------------------
% 1.46/0.54  % (19519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.54  % (19502)Refutation not found, incomplete strategy% (19502)------------------------------
% 1.46/0.54  % (19502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.54  % (19519)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.54  
% 1.46/0.54  % (19519)Memory used [KB]: 10746
% 1.46/0.54  % (19519)Time elapsed: 0.124 s
% 1.46/0.54  % (19519)------------------------------
% 1.46/0.54  % (19519)------------------------------
% 1.46/0.54  % (19504)Refutation not found, incomplete strategy% (19504)------------------------------
% 1.46/0.54  % (19504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.54  % (19504)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.54  
% 1.46/0.54  % (19504)Memory used [KB]: 6268
% 1.46/0.54  % (19504)Time elapsed: 0.134 s
% 1.46/0.54  % (19504)------------------------------
% 1.46/0.54  % (19504)------------------------------
% 1.46/0.54  % (19514)Refutation not found, incomplete strategy% (19514)------------------------------
% 1.46/0.54  % (19514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.54  % (19509)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.46/0.55  % (19514)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (19514)Memory used [KB]: 10746
% 1.46/0.55  % (19514)Time elapsed: 0.146 s
% 1.46/0.55  % (19514)------------------------------
% 1.46/0.55  % (19514)------------------------------
% 1.64/0.55  % (19509)Refutation not found, incomplete strategy% (19509)------------------------------
% 1.64/0.55  % (19509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.55  % (19502)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.55  
% 1.64/0.55  % (19502)Memory used [KB]: 6268
% 1.64/0.55  % (19502)Time elapsed: 0.143 s
% 1.64/0.55  % (19502)------------------------------
% 1.64/0.55  % (19502)------------------------------
% 1.64/0.56  % (19509)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.56  
% 1.64/0.56  % (19509)Memory used [KB]: 1663
% 1.64/0.56  % (19509)Time elapsed: 0.153 s
% 1.64/0.56  % (19509)------------------------------
% 1.64/0.56  % (19509)------------------------------
% 1.64/0.58  % (19521)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.64/0.59  % (19521)Refutation not found, incomplete strategy% (19521)------------------------------
% 1.64/0.59  % (19521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.59  % (19521)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.59  
% 1.64/0.59  % (19521)Memory used [KB]: 6268
% 1.64/0.59  % (19521)Time elapsed: 0.009 s
% 1.64/0.59  % (19521)------------------------------
% 1.64/0.59  % (19521)------------------------------
% 1.97/0.63  % (19525)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 1.97/0.63  % (19491)Refutation not found, incomplete strategy% (19491)------------------------------
% 1.97/0.63  % (19491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.63  % (19491)Termination reason: Refutation not found, incomplete strategy
% 1.97/0.63  
% 1.97/0.63  % (19491)Memory used [KB]: 1663
% 1.97/0.63  % (19491)Time elapsed: 0.229 s
% 1.97/0.63  % (19491)------------------------------
% 1.97/0.63  % (19491)------------------------------
% 1.97/0.63  % (19525)Refutation not found, incomplete strategy% (19525)------------------------------
% 1.97/0.63  % (19525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.63  % (19525)Termination reason: Refutation not found, incomplete strategy
% 1.97/0.63  
% 1.97/0.63  % (19525)Memory used [KB]: 10618
% 1.97/0.63  % (19525)Time elapsed: 0.089 s
% 1.97/0.63  % (19525)------------------------------
% 1.97/0.63  % (19525)------------------------------
% 1.97/0.63  % (19526)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 1.97/0.63  % (19527)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 1.97/0.64  % (19524)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 1.97/0.64  % (19524)Refutation not found, incomplete strategy% (19524)------------------------------
% 1.97/0.64  % (19524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.64  % (19524)Termination reason: Refutation not found, incomplete strategy
% 1.97/0.64  
% 1.97/0.64  % (19524)Memory used [KB]: 6140
% 1.97/0.64  % (19524)Time elapsed: 0.101 s
% 1.97/0.64  % (19524)------------------------------
% 1.97/0.64  % (19524)------------------------------
% 1.97/0.64  % (19529)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 1.97/0.64  % (19529)Refutation not found, incomplete strategy% (19529)------------------------------
% 1.97/0.64  % (19529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.64  % (19529)Termination reason: Refutation not found, incomplete strategy
% 1.97/0.64  
% 1.97/0.64  % (19529)Memory used [KB]: 1791
% 1.97/0.64  % (19529)Time elapsed: 0.099 s
% 1.97/0.64  % (19529)------------------------------
% 1.97/0.64  % (19529)------------------------------
% 1.97/0.65  % (19494)Refutation not found, incomplete strategy% (19494)------------------------------
% 1.97/0.65  % (19494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.65  % (19494)Termination reason: Refutation not found, incomplete strategy
% 1.97/0.65  
% 1.97/0.65  % (19494)Memory used [KB]: 6140
% 1.97/0.65  % (19494)Time elapsed: 0.250 s
% 1.97/0.65  % (19494)------------------------------
% 1.97/0.65  % (19494)------------------------------
% 1.97/0.65  % (19528)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 1.97/0.65  % (19528)Refutation not found, incomplete strategy% (19528)------------------------------
% 1.97/0.65  % (19528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.65  % (19528)Termination reason: Refutation not found, incomplete strategy
% 1.97/0.65  
% 1.97/0.65  % (19528)Memory used [KB]: 10618
% 1.97/0.65  % (19528)Time elapsed: 0.098 s
% 1.97/0.65  % (19528)------------------------------
% 1.97/0.65  % (19528)------------------------------
% 1.97/0.65  % (19523)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 1.97/0.65  % (19526)Refutation not found, incomplete strategy% (19526)------------------------------
% 1.97/0.65  % (19526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.65  % (19526)Termination reason: Refutation not found, incomplete strategy
% 1.97/0.65  
% 1.97/0.65  % (19526)Memory used [KB]: 10746
% 1.97/0.65  % (19526)Time elapsed: 0.098 s
% 1.97/0.65  % (19526)------------------------------
% 1.97/0.65  % (19526)------------------------------
% 1.97/0.65  % (19532)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 1.97/0.65  % (19493)Refutation not found, incomplete strategy% (19493)------------------------------
% 1.97/0.65  % (19493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.65  % (19493)Termination reason: Refutation not found, incomplete strategy
% 1.97/0.65  
% 1.97/0.65  % (19493)Memory used [KB]: 6268
% 1.97/0.65  % (19493)Time elapsed: 0.231 s
% 1.97/0.65  % (19493)------------------------------
% 1.97/0.65  % (19493)------------------------------
% 1.97/0.65  % (19532)Refutation not found, incomplete strategy% (19532)------------------------------
% 1.97/0.65  % (19532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.65  % (19532)Termination reason: Refutation not found, incomplete strategy
% 1.97/0.65  
% 1.97/0.65  % (19532)Memory used [KB]: 6140
% 1.97/0.65  % (19532)Time elapsed: 0.088 s
% 1.97/0.65  % (19532)------------------------------
% 1.97/0.65  % (19532)------------------------------
% 1.97/0.65  % (19523)Refutation not found, incomplete strategy% (19523)------------------------------
% 1.97/0.65  % (19523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.65  % (19523)Termination reason: Refutation not found, incomplete strategy
% 1.97/0.65  
% 1.97/0.65  % (19523)Memory used [KB]: 10746
% 1.97/0.65  % (19523)Time elapsed: 0.115 s
% 1.97/0.65  % (19523)------------------------------
% 1.97/0.65  % (19523)------------------------------
% 1.97/0.66  % (19533)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 1.97/0.66  % (19531)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 1.97/0.66  % (19541)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 1.97/0.66  % (19538)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 1.97/0.66  % (19531)Refutation not found, incomplete strategy% (19531)------------------------------
% 1.97/0.66  % (19531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.66  % (19531)Termination reason: Refutation not found, incomplete strategy
% 1.97/0.66  
% 1.97/0.66  % (19531)Memory used [KB]: 10746
% 1.97/0.66  % (19531)Time elapsed: 0.101 s
% 1.97/0.66  % (19531)------------------------------
% 1.97/0.66  % (19531)------------------------------
% 1.97/0.66  % (19533)Refutation not found, incomplete strategy% (19533)------------------------------
% 1.97/0.66  % (19533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.66  % (19533)Termination reason: Refutation not found, incomplete strategy
% 1.97/0.66  
% 1.97/0.66  % (19533)Memory used [KB]: 10746
% 1.97/0.66  % (19533)Time elapsed: 0.098 s
% 1.97/0.66  % (19533)------------------------------
% 1.97/0.66  % (19533)------------------------------
% 1.97/0.66  % (19530)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 1.97/0.66  % (19534)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 1.97/0.66  % (19534)Refutation not found, incomplete strategy% (19534)------------------------------
% 1.97/0.66  % (19534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.66  % (19534)Termination reason: Refutation not found, incomplete strategy
% 1.97/0.66  
% 1.97/0.66  % (19534)Memory used [KB]: 1663
% 1.97/0.66  % (19534)Time elapsed: 0.106 s
% 1.97/0.66  % (19534)------------------------------
% 1.97/0.66  % (19534)------------------------------
% 1.97/0.67  % (19536)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 1.97/0.67  % (19499)Refutation not found, incomplete strategy% (19499)------------------------------
% 1.97/0.67  % (19499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.67  % (19499)Termination reason: Refutation not found, incomplete strategy
% 1.97/0.67  
% 1.97/0.67  % (19499)Memory used [KB]: 6268
% 1.97/0.67  % (19499)Time elapsed: 0.275 s
% 1.97/0.67  % (19499)------------------------------
% 1.97/0.67  % (19499)------------------------------
% 2.36/0.67  % (19535)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 2.36/0.67  % (19535)Refutation not found, incomplete strategy% (19535)------------------------------
% 2.36/0.67  % (19535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.36/0.67  % (19535)Termination reason: Refutation not found, incomplete strategy
% 2.36/0.67  
% 2.36/0.67  % (19535)Memory used [KB]: 10746
% 2.36/0.67  % (19535)Time elapsed: 0.107 s
% 2.36/0.67  % (19535)------------------------------
% 2.36/0.67  % (19535)------------------------------
% 2.36/0.67  % (19537)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 2.36/0.67  % (19506)Refutation not found, incomplete strategy% (19506)------------------------------
% 2.36/0.67  % (19506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.36/0.67  % (19506)Termination reason: Refutation not found, incomplete strategy
% 2.36/0.67  
% 2.36/0.67  % (19506)Memory used [KB]: 6140
% 2.36/0.67  % (19506)Time elapsed: 0.271 s
% 2.36/0.67  % (19506)------------------------------
% 2.36/0.67  % (19506)------------------------------
% 2.36/0.67  % (19540)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 2.36/0.67  % (19539)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 2.36/0.68  % (19542)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 2.36/0.71  % (19540)Refutation not found, incomplete strategy% (19540)------------------------------
% 2.36/0.71  % (19540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.36/0.71  % (19540)Termination reason: Refutation not found, incomplete strategy
% 2.36/0.71  
% 2.36/0.71  % (19540)Memory used [KB]: 6140
% 2.36/0.71  % (19540)Time elapsed: 0.140 s
% 2.36/0.71  % (19540)------------------------------
% 2.36/0.71  % (19540)------------------------------
% 2.36/0.73  % (19537)Refutation not found, incomplete strategy% (19537)------------------------------
% 2.36/0.73  % (19537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.36/0.73  % (19537)Termination reason: Refutation not found, incomplete strategy
% 2.36/0.73  
% 2.36/0.73  % (19537)Memory used [KB]: 6140
% 2.36/0.73  % (19537)Time elapsed: 0.178 s
% 2.36/0.73  % (19537)------------------------------
% 2.36/0.73  % (19537)------------------------------
% 2.82/0.74  % (19536)Refutation not found, incomplete strategy% (19536)------------------------------
% 2.82/0.74  % (19536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.82/0.74  % (19536)Termination reason: Refutation not found, incomplete strategy
% 2.82/0.74  
% 2.82/0.74  % (19536)Memory used [KB]: 6268
% 2.82/0.74  % (19536)Time elapsed: 0.169 s
% 2.82/0.74  % (19536)------------------------------
% 2.82/0.74  % (19536)------------------------------
% 2.82/0.74  % (19530)Refutation not found, incomplete strategy% (19530)------------------------------
% 2.82/0.74  % (19530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.82/0.74  % (19530)Termination reason: Refutation not found, incomplete strategy
% 2.82/0.74  
% 2.82/0.74  % (19530)Memory used [KB]: 6268
% 2.82/0.74  % (19530)Time elapsed: 0.184 s
% 2.82/0.74  % (19530)------------------------------
% 2.82/0.74  % (19530)------------------------------
% 2.82/0.77  % SZS status CounterSatisfiable for theBenchmark
% 2.82/0.77  % (19542)# SZS output start Saturation.
% 2.82/0.77  tff(u206,negated_conjecture,
% 2.82/0.77      ((~(sK1 != sK2)) | (sK1 != sK2))).
% 2.82/0.77  
% 2.82/0.77  tff(u205,negated_conjecture,
% 2.82/0.77      ((~(k6_waybel_0(sK0,sK1) = k6_waybel_0(sK0,sK2))) | (k6_waybel_0(sK0,sK1) = k6_waybel_0(sK0,sK2)))).
% 2.82/0.77  
% 2.82/0.77  tff(u204,negated_conjecture,
% 2.82/0.77      ((~(k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | (k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))).
% 2.82/0.77  
% 2.82/0.77  tff(u203,negated_conjecture,
% 2.82/0.77      ((~(k6_domain_1(u1_struct_0(sK0),sK2) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) | (k6_domain_1(u1_struct_0(sK0),sK2) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))).
% 2.82/0.77  
% 2.82/0.77  tff(u202,axiom,
% 2.82/0.77      (![X1, X0, X2] : ((~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | r2_hidden(X0,X2))))).
% 2.82/0.77  
% 2.82/0.77  tff(u201,axiom,
% 2.82/0.77      (![X1, X0, X2] : ((~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | r2_hidden(X1,X2))))).
% 2.82/0.77  
% 2.82/0.77  tff(u200,negated_conjecture,
% 2.82/0.77      ((~(k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | (![X0] : ((~r1_tarski(k6_domain_1(u1_struct_0(sK0),sK1),X0) | r2_hidden(sK1,X0)))))).
% 2.82/0.77  
% 2.82/0.77  tff(u199,negated_conjecture,
% 2.82/0.77      ((~(k6_domain_1(u1_struct_0(sK0),sK2) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) | (![X0] : ((~r1_tarski(k6_domain_1(u1_struct_0(sK0),sK2),X0) | r2_hidden(sK2,X0)))))).
% 2.82/0.77  
% 2.82/0.77  tff(u198,axiom,
% 2.82/0.77      (![X1, X0, X2] : ((~r2_hidden(X1,X2) | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X0,X2))))).
% 2.82/0.77  
% 2.82/0.77  tff(u197,negated_conjecture,
% 2.82/0.77      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 2.82/0.77  
% 2.82/0.77  tff(u196,negated_conjecture,
% 2.82/0.77      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 2.82/0.77  
% 2.82/0.77  tff(u195,axiom,
% 2.82/0.77      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 2.82/0.77  
% 2.82/0.77  tff(u194,negated_conjecture,
% 2.82/0.77      ((~~v1_xboole_0(u1_struct_0(sK0))) | ~v1_xboole_0(u1_struct_0(sK0)))).
% 2.82/0.77  
% 2.82/0.77  tff(u193,negated_conjecture,
% 2.82/0.77      ((~v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))))).
% 2.82/0.77  
% 2.82/0.77  tff(u192,negated_conjecture,
% 2.82/0.77      ((~v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))).
% 2.82/0.77  
% 2.82/0.77  tff(u191,axiom,
% 2.82/0.77      (![X1, X0] : ((~m1_subset_1(X1,X0) | (k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | v1_xboole_0(X0))))).
% 2.82/0.77  
% 2.82/0.77  tff(u190,axiom,
% 2.82/0.77      (![X1, X0] : ((~m1_subset_1(X1,X0) | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | v1_xboole_0(X0))))).
% 2.82/0.77  
% 2.82/0.77  tff(u189,negated_conjecture,
% 2.82/0.77      ((~m1_subset_1(sK1,u1_struct_0(sK0))) | m1_subset_1(sK1,u1_struct_0(sK0)))).
% 2.82/0.77  
% 2.82/0.77  tff(u188,negated_conjecture,
% 2.82/0.77      ((~m1_subset_1(sK2,u1_struct_0(sK0))) | m1_subset_1(sK2,u1_struct_0(sK0)))).
% 2.82/0.77  
% 2.82/0.77  tff(u187,negated_conjecture,
% 2.82/0.77      ((~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))))).
% 2.82/0.77  
% 2.82/0.77  tff(u186,negated_conjecture,
% 2.82/0.77      ((~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))))).
% 2.82/0.77  
% 2.82/0.77  tff(u185,negated_conjecture,
% 2.82/0.77      ((~m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k6_domain_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) | m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k6_domain_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))).
% 2.82/0.77  
% 2.82/0.77  tff(u184,axiom,
% 2.82/0.77      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 2.82/0.77  
% 2.82/0.77  tff(u183,negated_conjecture,
% 2.82/0.77      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 2.82/0.77  
% 2.82/0.77  tff(u182,negated_conjecture,
% 2.82/0.77      ((~v5_orders_2(sK0)) | v5_orders_2(sK0))).
% 2.82/0.77  
% 2.82/0.77  tff(u181,axiom,
% 2.82/0.77      (![X1, X0, X2] : ((~r1_orders_2(X0,X2,X1) | (X1 = X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0))))).
% 2.82/0.77  
% 2.82/0.77  tff(u180,negated_conjecture,
% 2.82/0.77      ((~v3_orders_2(sK0)) | v3_orders_2(sK0))).
% 2.82/0.77  
% 2.82/0.77  % (19542)# SZS output end Saturation.
% 2.82/0.77  % (19542)------------------------------
% 2.82/0.77  % (19542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.82/0.77  % (19542)Termination reason: Satisfiable
% 2.82/0.77  
% 2.82/0.77  % (19542)Memory used [KB]: 6268
% 2.82/0.77  % (19542)Time elapsed: 0.180 s
% 2.82/0.77  % (19542)------------------------------
% 2.82/0.77  % (19542)------------------------------
% 3.06/0.77  % (19490)Success in time 0.406 s
%------------------------------------------------------------------------------
