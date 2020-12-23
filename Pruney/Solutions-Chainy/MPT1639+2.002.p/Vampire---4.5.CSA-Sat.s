%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:59 EST 2020

% Result     : CounterSatisfiable 2.71s
% Output     : Saturation 2.71s
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
    ( k5_waybel_0(sK0,sK1) != k5_waybel_0(sK0,sK2)
    | k5_waybel_0(sK0,sK1) = k5_waybel_0(sK0,sK2) )).

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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:37:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (2905)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.50  % (2915)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.50  % (2915)Refutation not found, incomplete strategy% (2915)------------------------------
% 0.20/0.50  % (2915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (2915)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (2915)Memory used [KB]: 1663
% 0.20/0.50  % (2915)Time elapsed: 0.085 s
% 0.20/0.50  % (2915)------------------------------
% 0.20/0.50  % (2915)------------------------------
% 0.20/0.52  % (2904)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.29/0.53  % (2898)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.29/0.53  % (2898)Refutation not found, incomplete strategy% (2898)------------------------------
% 1.29/0.53  % (2898)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (2898)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (2898)Memory used [KB]: 1663
% 1.29/0.53  % (2898)Time elapsed: 0.113 s
% 1.29/0.53  % (2898)------------------------------
% 1.29/0.53  % (2898)------------------------------
% 1.29/0.54  % (2903)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.54  % (2902)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.29/0.54  % (2901)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.29/0.54  % (2919)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.29/0.54  % (2901)Refutation not found, incomplete strategy% (2901)------------------------------
% 1.29/0.54  % (2901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (2901)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (2901)Memory used [KB]: 1791
% 1.29/0.54  % (2901)Time elapsed: 0.119 s
% 1.29/0.54  % (2901)------------------------------
% 1.29/0.54  % (2901)------------------------------
% 1.29/0.54  % (2919)Refutation not found, incomplete strategy% (2919)------------------------------
% 1.29/0.54  % (2919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (2919)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (2919)Memory used [KB]: 6268
% 1.29/0.54  % (2919)Time elapsed: 0.096 s
% 1.29/0.54  % (2919)------------------------------
% 1.29/0.54  % (2919)------------------------------
% 1.29/0.54  % (2922)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.29/0.54  % (2900)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.29/0.54  % (2926)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.29/0.54  % (2926)Refutation not found, incomplete strategy% (2926)------------------------------
% 1.29/0.54  % (2926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (2926)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (2926)Memory used [KB]: 1663
% 1.29/0.54  % (2926)Time elapsed: 0.001 s
% 1.29/0.54  % (2926)------------------------------
% 1.29/0.54  % (2926)------------------------------
% 1.29/0.55  % (2921)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.29/0.55  % (2911)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.29/0.55  % (2908)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.29/0.55  % (2921)Refutation not found, incomplete strategy% (2921)------------------------------
% 1.29/0.55  % (2921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (2921)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (2921)Memory used [KB]: 10618
% 1.29/0.55  % (2921)Time elapsed: 0.129 s
% 1.29/0.55  % (2921)------------------------------
% 1.29/0.55  % (2921)------------------------------
% 1.29/0.55  % (2911)Refutation not found, incomplete strategy% (2911)------------------------------
% 1.29/0.55  % (2911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (2906)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.29/0.55  % (2911)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (2911)Memory used [KB]: 1791
% 1.29/0.55  % (2911)Time elapsed: 0.097 s
% 1.29/0.55  % (2911)------------------------------
% 1.29/0.55  % (2911)------------------------------
% 1.29/0.55  % (2908)Refutation not found, incomplete strategy% (2908)------------------------------
% 1.29/0.55  % (2908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (2908)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (2908)Memory used [KB]: 6268
% 1.29/0.55  % (2908)Time elapsed: 0.131 s
% 1.29/0.55  % (2908)------------------------------
% 1.29/0.55  % (2908)------------------------------
% 1.29/0.55  % (2906)Refutation not found, incomplete strategy% (2906)------------------------------
% 1.29/0.55  % (2906)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (2906)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (2906)Memory used [KB]: 1663
% 1.29/0.55  % (2906)Time elapsed: 0.124 s
% 1.29/0.55  % (2906)------------------------------
% 1.29/0.55  % (2906)------------------------------
% 1.29/0.55  % (2918)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.29/0.55  % (2923)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.29/0.55  % (2913)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.29/0.55  % (2918)Refutation not found, incomplete strategy% (2918)------------------------------
% 1.29/0.55  % (2918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (2918)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (2918)Memory used [KB]: 6268
% 1.29/0.55  % (2918)Time elapsed: 0.139 s
% 1.29/0.55  % (2918)------------------------------
% 1.29/0.55  % (2918)------------------------------
% 1.29/0.55  % (2923)Refutation not found, incomplete strategy% (2923)------------------------------
% 1.29/0.55  % (2923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (2923)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (2923)Memory used [KB]: 6268
% 1.29/0.55  % (2923)Time elapsed: 0.137 s
% 1.29/0.55  % (2923)------------------------------
% 1.29/0.55  % (2923)------------------------------
% 1.29/0.55  % (2899)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.29/0.55  % (2913)Refutation not found, incomplete strategy% (2913)------------------------------
% 1.29/0.55  % (2913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (2913)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (2913)Memory used [KB]: 10618
% 1.29/0.55  % (2913)Time elapsed: 0.139 s
% 1.29/0.55  % (2913)------------------------------
% 1.29/0.55  % (2913)------------------------------
% 1.29/0.55  % (2914)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.29/0.55  % (2924)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.29/0.55  % (2907)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.55/0.55  % (2924)Refutation not found, incomplete strategy% (2924)------------------------------
% 1.55/0.55  % (2924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.55  % (2924)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.55  
% 1.55/0.55  % (2924)Memory used [KB]: 6140
% 1.55/0.55  % (2924)Time elapsed: 0.138 s
% 1.55/0.55  % (2924)------------------------------
% 1.55/0.55  % (2924)------------------------------
% 1.55/0.55  % (2897)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.55/0.55  % (2907)Refutation not found, incomplete strategy% (2907)------------------------------
% 1.55/0.55  % (2907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.55  % (2907)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.55  
% 1.55/0.55  % (2907)Memory used [KB]: 10746
% 1.55/0.55  % (2907)Time elapsed: 0.142 s
% 1.55/0.55  % (2907)------------------------------
% 1.55/0.55  % (2907)------------------------------
% 1.55/0.56  % (2916)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.55/0.56  % (2902)Refutation not found, incomplete strategy% (2902)------------------------------
% 1.55/0.56  % (2902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (2902)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.56  
% 1.55/0.56  % (2902)Memory used [KB]: 1663
% 1.55/0.56  % (2902)Time elapsed: 0.116 s
% 1.55/0.56  % (2902)------------------------------
% 1.55/0.56  % (2902)------------------------------
% 1.55/0.56  % (2912)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.55/0.56  % (2916)Refutation not found, incomplete strategy% (2916)------------------------------
% 1.55/0.56  % (2916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (2916)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.56  
% 1.55/0.56  % (2916)Memory used [KB]: 1663
% 1.55/0.56  % (2916)Time elapsed: 0.140 s
% 1.55/0.56  % (2916)------------------------------
% 1.55/0.56  % (2916)------------------------------
% 1.55/0.56  % (2922)Refutation not found, incomplete strategy% (2922)------------------------------
% 1.55/0.56  % (2922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (2922)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.56  
% 1.55/0.56  % (2922)Memory used [KB]: 6268
% 1.55/0.56  % (2922)Time elapsed: 0.138 s
% 1.55/0.56  % (2922)------------------------------
% 1.55/0.56  % (2922)------------------------------
% 1.55/0.56  % (2910)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.55/0.56  % (2914)Refutation not found, incomplete strategy% (2914)------------------------------
% 1.55/0.56  % (2914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (2914)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.56  
% 1.55/0.56  % (2914)Memory used [KB]: 1663
% 1.55/0.56  % (2914)Time elapsed: 0.138 s
% 1.55/0.56  % (2914)------------------------------
% 1.55/0.56  % (2914)------------------------------
% 1.55/0.56  % (2910)Refutation not found, incomplete strategy% (2910)------------------------------
% 1.55/0.56  % (2910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (2910)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.56  
% 1.55/0.56  % (2910)Memory used [KB]: 6268
% 1.55/0.56  % (2910)Time elapsed: 0.151 s
% 1.55/0.56  % (2910)------------------------------
% 1.55/0.56  % (2910)------------------------------
% 1.55/0.56  % (2925)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.55/0.56  % (2925)Refutation not found, incomplete strategy% (2925)------------------------------
% 1.55/0.56  % (2925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (2925)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.56  
% 1.55/0.56  % (2925)Memory used [KB]: 10746
% 1.55/0.56  % (2925)Time elapsed: 0.148 s
% 1.55/0.56  % (2925)------------------------------
% 1.55/0.56  % (2925)------------------------------
% 1.55/0.56  % (2917)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.55/0.57  % (2909)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.55/0.57  % (2909)Refutation not found, incomplete strategy% (2909)------------------------------
% 1.55/0.57  % (2909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (2909)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.57  
% 1.55/0.57  % (2909)Memory used [KB]: 10618
% 1.55/0.57  % (2909)Time elapsed: 0.154 s
% 1.55/0.57  % (2909)------------------------------
% 1.55/0.57  % (2909)------------------------------
% 1.55/0.58  % (2920)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.55/0.58  % (2920)Refutation not found, incomplete strategy% (2920)------------------------------
% 1.55/0.58  % (2920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  % (2920)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.58  
% 1.55/0.58  % (2920)Memory used [KB]: 10746
% 1.55/0.58  % (2920)Time elapsed: 0.136 s
% 1.55/0.58  % (2920)------------------------------
% 1.55/0.58  % (2920)------------------------------
% 1.55/0.61  % (2905)Refutation not found, incomplete strategy% (2905)------------------------------
% 1.55/0.61  % (2905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.61  % (2905)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.61  
% 1.55/0.61  % (2905)Memory used [KB]: 6268
% 1.55/0.61  % (2905)Time elapsed: 0.189 s
% 1.55/0.61  % (2905)------------------------------
% 1.55/0.61  % (2905)------------------------------
% 1.55/0.61  % (2927)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.55/0.62  % (2927)Refutation not found, incomplete strategy% (2927)------------------------------
% 1.55/0.62  % (2927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.62  % (2927)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.62  
% 1.55/0.62  % (2927)Memory used [KB]: 6268
% 1.55/0.62  % (2927)Time elapsed: 0.005 s
% 1.55/0.62  % (2927)------------------------------
% 1.55/0.62  % (2927)------------------------------
% 1.87/0.65  % (2935)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 1.87/0.65  % (2897)Refutation not found, incomplete strategy% (2897)------------------------------
% 1.87/0.65  % (2897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.65  % (2897)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.65  
% 1.87/0.65  % (2897)Memory used [KB]: 1663
% 1.87/0.65  % (2897)Time elapsed: 0.236 s
% 1.87/0.65  % (2897)------------------------------
% 1.87/0.65  % (2897)------------------------------
% 1.87/0.66  % (2928)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 1.87/0.66  % (2928)Refutation not found, incomplete strategy% (2928)------------------------------
% 1.87/0.66  % (2928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.66  % (2928)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.66  
% 1.87/0.66  % (2928)Memory used [KB]: 10746
% 1.87/0.66  % (2928)Time elapsed: 0.089 s
% 1.87/0.66  % (2928)------------------------------
% 1.87/0.66  % (2928)------------------------------
% 1.87/0.66  % (2930)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 1.87/0.66  % (2929)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 1.87/0.66  % (2929)Refutation not found, incomplete strategy% (2929)------------------------------
% 1.87/0.66  % (2929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.66  % (2929)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.66  
% 1.87/0.66  % (2929)Memory used [KB]: 6140
% 1.87/0.66  % (2929)Time elapsed: 0.091 s
% 1.87/0.66  % (2929)------------------------------
% 1.87/0.66  % (2929)------------------------------
% 1.87/0.67  % (2932)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 1.87/0.67  % (2947)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 1.87/0.67  % (2941)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 1.87/0.67  % (2900)Refutation not found, incomplete strategy% (2900)------------------------------
% 1.87/0.67  % (2900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.67  % (2900)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.67  
% 1.87/0.67  % (2900)Memory used [KB]: 6140
% 1.87/0.67  % (2900)Time elapsed: 0.256 s
% 1.87/0.67  % (2900)------------------------------
% 1.87/0.67  % (2900)------------------------------
% 2.01/0.67  % (2899)Refutation not found, incomplete strategy% (2899)------------------------------
% 2.01/0.67  % (2899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.67  % (2899)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.67  
% 2.01/0.67  % (2899)Memory used [KB]: 6268
% 2.01/0.67  % (2899)Time elapsed: 0.256 s
% 2.01/0.67  % (2899)------------------------------
% 2.01/0.67  % (2899)------------------------------
% 2.01/0.68  % (2931)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.01/0.68  % (2933)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.01/0.68  % (2931)Refutation not found, incomplete strategy% (2931)------------------------------
% 2.01/0.68  % (2931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.68  % (2931)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.68  
% 2.01/0.68  % (2931)Memory used [KB]: 10746
% 2.01/0.68  % (2931)Time elapsed: 0.098 s
% 2.01/0.68  % (2931)------------------------------
% 2.01/0.68  % (2931)------------------------------
% 2.01/0.68  % (2943)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 2.01/0.68  % (2933)Refutation not found, incomplete strategy% (2933)------------------------------
% 2.01/0.68  % (2933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.68  % (2933)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.68  
% 2.01/0.68  % (2933)Memory used [KB]: 10618
% 2.01/0.68  % (2933)Time elapsed: 0.106 s
% 2.01/0.68  % (2933)------------------------------
% 2.01/0.68  % (2933)------------------------------
% 2.01/0.68  % (2930)Refutation not found, incomplete strategy% (2930)------------------------------
% 2.01/0.68  % (2930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.68  % (2930)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.68  
% 2.01/0.68  % (2930)Memory used [KB]: 10618
% 2.01/0.68  % (2930)Time elapsed: 0.113 s
% 2.01/0.68  % (2930)------------------------------
% 2.01/0.68  % (2930)------------------------------
% 2.01/0.68  % (2934)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.01/0.68  % (2934)Refutation not found, incomplete strategy% (2934)------------------------------
% 2.01/0.68  % (2934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.68  % (2934)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.68  
% 2.01/0.68  % (2934)Memory used [KB]: 1791
% 2.01/0.68  % (2934)Time elapsed: 0.106 s
% 2.01/0.68  % (2934)------------------------------
% 2.01/0.68  % (2934)------------------------------
% 2.01/0.68  % (2937)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.01/0.68  % (2942)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 2.01/0.69  % (2937)Refutation not found, incomplete strategy% (2937)------------------------------
% 2.01/0.69  % (2937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.69  % (2937)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.69  
% 2.01/0.69  % (2937)Memory used [KB]: 6140
% 2.01/0.69  % (2937)Time elapsed: 0.104 s
% 2.01/0.69  % (2937)------------------------------
% 2.01/0.69  % (2937)------------------------------
% 2.01/0.69  % (2940)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 2.01/0.69  % (2939)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.01/0.69  % (2936)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.01/0.69  % (2945)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 2.01/0.69  % (2939)Refutation not found, incomplete strategy% (2939)------------------------------
% 2.01/0.69  % (2939)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.69  % (2939)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.69  
% 2.01/0.69  % (2939)Memory used [KB]: 1663
% 2.01/0.69  % (2939)Time elapsed: 0.100 s
% 2.01/0.69  % (2939)------------------------------
% 2.01/0.69  % (2939)------------------------------
% 2.01/0.69  % (2912)Refutation not found, incomplete strategy% (2912)------------------------------
% 2.01/0.69  % (2912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.69  % (2912)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.69  
% 2.01/0.69  % (2912)Memory used [KB]: 6140
% 2.01/0.69  % (2912)Time elapsed: 0.264 s
% 2.01/0.69  % (2912)------------------------------
% 2.01/0.69  % (2912)------------------------------
% 2.01/0.69  % (2936)Refutation not found, incomplete strategy% (2936)------------------------------
% 2.01/0.69  % (2936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.69  % (2936)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.69  
% 2.01/0.69  % (2936)Memory used [KB]: 10746
% 2.01/0.69  % (2936)Time elapsed: 0.116 s
% 2.01/0.69  % (2936)------------------------------
% 2.01/0.69  % (2936)------------------------------
% 2.01/0.69  % (2946)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 2.01/0.69  % (2938)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.01/0.69  % (2938)Refutation not found, incomplete strategy% (2938)------------------------------
% 2.01/0.69  % (2938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.69  % (2938)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.69  
% 2.01/0.69  % (2938)Memory used [KB]: 10746
% 2.01/0.69  % (2938)Time elapsed: 0.116 s
% 2.01/0.69  % (2938)------------------------------
% 2.01/0.69  % (2938)------------------------------
% 2.01/0.70  % (2940)Refutation not found, incomplete strategy% (2940)------------------------------
% 2.01/0.70  % (2940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.70  % (2940)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.70  
% 2.01/0.70  % (2940)Memory used [KB]: 10746
% 2.01/0.70  % (2940)Time elapsed: 0.119 s
% 2.01/0.70  % (2940)------------------------------
% 2.01/0.70  % (2940)------------------------------
% 2.01/0.70  % (2944)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 2.01/0.72  % (2935)Refutation not found, incomplete strategy% (2935)------------------------------
% 2.01/0.72  % (2935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.72  % (2935)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.72  
% 2.01/0.72  % (2935)Memory used [KB]: 6268
% 2.01/0.72  % (2935)Time elapsed: 0.134 s
% 2.01/0.72  % (2935)------------------------------
% 2.01/0.72  % (2935)------------------------------
% 2.01/0.73  % (2941)Refutation not found, incomplete strategy% (2941)------------------------------
% 2.01/0.73  % (2941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.73  % (2941)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.73  
% 2.01/0.73  % (2941)Memory used [KB]: 6268
% 2.01/0.73  % (2941)Time elapsed: 0.147 s
% 2.01/0.73  % (2941)------------------------------
% 2.01/0.73  % (2941)------------------------------
% 2.71/0.74  % (2942)Refutation not found, incomplete strategy% (2942)------------------------------
% 2.71/0.74  % (2942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.71/0.74  % (2942)Termination reason: Refutation not found, incomplete strategy
% 2.71/0.74  
% 2.71/0.74  % (2942)Memory used [KB]: 6140
% 2.71/0.74  % (2942)Time elapsed: 0.142 s
% 2.71/0.74  % (2942)------------------------------
% 2.71/0.74  % (2942)------------------------------
% 2.71/0.74  % SZS status CounterSatisfiable for theBenchmark
% 2.71/0.74  % (2947)# SZS output start Saturation.
% 2.71/0.74  tff(u206,negated_conjecture,
% 2.71/0.74      ((~(sK1 != sK2)) | (sK1 != sK2))).
% 2.71/0.74  
% 2.71/0.74  tff(u205,negated_conjecture,
% 2.71/0.74      ((~(k5_waybel_0(sK0,sK1) = k5_waybel_0(sK0,sK2))) | (k5_waybel_0(sK0,sK1) = k5_waybel_0(sK0,sK2)))).
% 2.71/0.74  
% 2.71/0.74  tff(u204,negated_conjecture,
% 2.71/0.74      ((~(k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | (k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))).
% 2.71/0.74  
% 2.71/0.74  tff(u203,negated_conjecture,
% 2.71/0.74      ((~(k6_domain_1(u1_struct_0(sK0),sK2) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) | (k6_domain_1(u1_struct_0(sK0),sK2) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))).
% 2.71/0.74  
% 2.71/0.74  tff(u202,axiom,
% 2.71/0.74      (![X1, X0, X2] : ((~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | r2_hidden(X0,X2))))).
% 2.71/0.74  
% 2.71/0.74  tff(u201,axiom,
% 2.71/0.74      (![X1, X0, X2] : ((~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | r2_hidden(X1,X2))))).
% 2.71/0.74  
% 2.71/0.74  tff(u200,negated_conjecture,
% 2.71/0.74      ((~(k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | (![X0] : ((~r1_tarski(k6_domain_1(u1_struct_0(sK0),sK1),X0) | r2_hidden(sK1,X0)))))).
% 2.71/0.74  
% 2.71/0.74  tff(u199,negated_conjecture,
% 2.71/0.74      ((~(k6_domain_1(u1_struct_0(sK0),sK2) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) | (![X0] : ((~r1_tarski(k6_domain_1(u1_struct_0(sK0),sK2),X0) | r2_hidden(sK2,X0)))))).
% 2.71/0.74  
% 2.71/0.74  tff(u198,axiom,
% 2.71/0.74      (![X1, X0, X2] : ((~r2_hidden(X1,X2) | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X0,X2))))).
% 2.71/0.74  
% 2.71/0.74  tff(u197,negated_conjecture,
% 2.71/0.74      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 2.71/0.74  
% 2.71/0.74  tff(u196,negated_conjecture,
% 2.71/0.74      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 2.71/0.74  
% 2.71/0.74  tff(u195,axiom,
% 2.71/0.74      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 2.71/0.74  
% 2.71/0.74  tff(u194,negated_conjecture,
% 2.71/0.74      ((~~v1_xboole_0(u1_struct_0(sK0))) | ~v1_xboole_0(u1_struct_0(sK0)))).
% 2.71/0.74  
% 2.71/0.74  tff(u193,negated_conjecture,
% 2.71/0.74      ((~v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))))).
% 2.71/0.74  
% 2.71/0.74  tff(u192,negated_conjecture,
% 2.71/0.74      ((~v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))).
% 2.71/0.74  
% 2.71/0.74  tff(u191,axiom,
% 2.71/0.74      (![X1, X0] : ((~m1_subset_1(X1,X0) | (k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | v1_xboole_0(X0))))).
% 2.71/0.74  
% 2.71/0.74  tff(u190,axiom,
% 2.71/0.74      (![X1, X0] : ((~m1_subset_1(X1,X0) | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | v1_xboole_0(X0))))).
% 2.71/0.74  
% 2.71/0.74  tff(u189,negated_conjecture,
% 2.71/0.74      ((~m1_subset_1(sK1,u1_struct_0(sK0))) | m1_subset_1(sK1,u1_struct_0(sK0)))).
% 2.71/0.74  
% 2.71/0.74  tff(u188,negated_conjecture,
% 2.71/0.74      ((~m1_subset_1(sK2,u1_struct_0(sK0))) | m1_subset_1(sK2,u1_struct_0(sK0)))).
% 2.71/0.74  
% 2.71/0.74  tff(u187,negated_conjecture,
% 2.71/0.74      ((~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))))).
% 2.71/0.74  
% 2.71/0.74  tff(u186,negated_conjecture,
% 2.71/0.74      ((~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))))).
% 2.71/0.74  
% 2.71/0.74  tff(u185,negated_conjecture,
% 2.71/0.74      ((~m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k6_domain_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) | m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k6_domain_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))).
% 2.71/0.74  
% 2.71/0.74  tff(u184,axiom,
% 2.71/0.74      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 2.71/0.74  
% 2.71/0.74  tff(u183,negated_conjecture,
% 2.71/0.74      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 2.71/0.74  
% 2.71/0.74  tff(u182,negated_conjecture,
% 2.71/0.74      ((~v5_orders_2(sK0)) | v5_orders_2(sK0))).
% 2.71/0.74  
% 2.71/0.74  tff(u181,axiom,
% 2.71/0.74      (![X1, X0, X2] : ((~r1_orders_2(X0,X2,X1) | (X1 = X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0))))).
% 2.71/0.74  
% 2.71/0.74  tff(u180,negated_conjecture,
% 2.71/0.74      ((~v3_orders_2(sK0)) | v3_orders_2(sK0))).
% 2.71/0.74  
% 2.71/0.74  % (2947)# SZS output end Saturation.
% 2.71/0.74  % (2947)------------------------------
% 2.71/0.74  % (2947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.71/0.74  % (2947)Termination reason: Satisfiable
% 2.71/0.74  
% 2.71/0.74  % (2947)Memory used [KB]: 6268
% 2.71/0.74  % (2947)Time elapsed: 0.150 s
% 2.71/0.74  % (2947)------------------------------
% 2.71/0.74  % (2947)------------------------------
% 2.71/0.75  % (2896)Success in time 0.368 s
%------------------------------------------------------------------------------
