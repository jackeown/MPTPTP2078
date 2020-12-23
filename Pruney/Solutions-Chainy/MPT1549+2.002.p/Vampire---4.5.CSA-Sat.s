%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:03 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   14 (  14 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    0
%              Number of atoms          :   44 (  44 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    9 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u118,negated_conjecture,
    ( ~ ( k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2) )
    | k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2) )).

tff(u117,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ! [X1,X0] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_orders_2(sK0) = X1 ) )).

tff(u116,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ! [X1,X0] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK0) = X0 ) )).

tff(u115,negated_conjecture,
    ( u1_struct_0(sK0) != u1_struct_0(sK1)
    | u1_struct_0(sK0) = u1_struct_0(sK1) )).

tff(u114,negated_conjecture,
    ( u1_orders_2(sK0) != u1_orders_2(sK1)
    | u1_orders_2(sK0) = u1_orders_2(sK1) )).

tff(u113,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) )).

tff(u112,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u111,negated_conjecture,
    ( ~ l1_orders_2(sK1)
    | l1_orders_2(sK1) )).

tff(u110,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3 ) )).

tff(u109,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) )).

tff(u108,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

tff(u107,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u106,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X2) ) )).

tff(u105,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
          | r1_orders_2(sK1,X0,X1)
          | ~ m1_subset_1(X0,u1_struct_0(sK0))
          | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
        | r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n004.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:46:53 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.50  % (31415)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (31423)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (31415)Refutation not found, incomplete strategy% (31415)------------------------------
% 0.21/0.51  % (31415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31415)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31415)Memory used [KB]: 6268
% 0.21/0.51  % (31415)Time elapsed: 0.101 s
% 0.21/0.51  % (31415)------------------------------
% 0.21/0.51  % (31415)------------------------------
% 0.21/0.52  % (31439)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (31432)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (31439)Refutation not found, incomplete strategy% (31439)------------------------------
% 0.21/0.52  % (31439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31439)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31439)Memory used [KB]: 1791
% 0.21/0.52  % (31439)Time elapsed: 0.106 s
% 0.21/0.52  % (31439)------------------------------
% 0.21/0.52  % (31439)------------------------------
% 0.21/0.52  % (31424)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (31414)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (31411)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (31412)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (31429)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (31421)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (31434)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (31432)Refutation not found, incomplete strategy% (31432)------------------------------
% 0.21/0.54  % (31432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31432)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31432)Memory used [KB]: 10746
% 0.21/0.54  % (31432)Time elapsed: 0.100 s
% 0.21/0.54  % (31432)------------------------------
% 0.21/0.54  % (31432)------------------------------
% 0.21/0.54  % (31414)Refutation not found, incomplete strategy% (31414)------------------------------
% 0.21/0.54  % (31414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31414)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31414)Memory used [KB]: 6140
% 0.21/0.54  % (31414)Time elapsed: 0.113 s
% 0.21/0.54  % (31414)------------------------------
% 0.21/0.54  % (31414)------------------------------
% 0.21/0.54  % (31422)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (31426)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (31421)Refutation not found, incomplete strategy% (31421)------------------------------
% 0.21/0.54  % (31421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.55  % (31430)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (31429)Refutation not found, incomplete strategy% (31429)------------------------------
% 0.21/0.55  % (31429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (31421)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (31421)Memory used [KB]: 10618
% 0.21/0.55  % (31421)Time elapsed: 0.136 s
% 0.21/0.55  % (31421)------------------------------
% 0.21/0.55  % (31421)------------------------------
% 0.21/0.55  % (31429)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (31429)Memory used [KB]: 10746
% 0.21/0.55  % (31429)Time elapsed: 0.137 s
% 0.21/0.55  % (31429)------------------------------
% 0.21/0.55  % (31429)------------------------------
% 0.21/0.55  % (31434)Refutation not found, incomplete strategy% (31434)------------------------------
% 0.21/0.55  % (31434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (31426)# SZS output start Saturation.
% 0.21/0.55  tff(u118,negated_conjecture,
% 0.21/0.55      ((~(k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2))) | (k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2)))).
% 0.21/0.55  
% 0.21/0.55  tff(u117,negated_conjecture,
% 0.21/0.55      ((~m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) | (![X1, X0] : (((g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) | (u1_orders_2(sK0) = X1)))))).
% 0.21/0.55  
% 0.21/0.55  tff(u116,negated_conjecture,
% 0.21/0.55      ((~m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) | (![X1, X0] : (((g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) | (u1_struct_0(sK0) = X0)))))).
% 0.21/0.55  
% 0.21/0.55  tff(u115,negated_conjecture,
% 0.21/0.55      ((~(u1_struct_0(sK0) = u1_struct_0(sK1))) | (u1_struct_0(sK0) = u1_struct_0(sK1)))).
% 0.21/0.55  
% 0.21/0.55  tff(u114,negated_conjecture,
% 0.21/0.55      ((~(u1_orders_2(sK0) = u1_orders_2(sK1))) | (u1_orders_2(sK0) = u1_orders_2(sK1)))).
% 0.21/0.55  
% 0.21/0.55  tff(u113,axiom,
% 0.21/0.55      (![X0] : ((~l1_orders_2(X0) | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))))).
% 0.21/0.55  
% 0.21/0.55  tff(u112,negated_conjecture,
% 0.21/0.55      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.21/0.55  
% 0.21/0.55  tff(u111,negated_conjecture,
% 0.21/0.55      ((~l1_orders_2(sK1)) | l1_orders_2(sK1))).
% 0.21/0.55  
% 0.21/0.55  tff(u110,axiom,
% 0.21/0.55      (![X1, X3, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | (g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | (X1 = X3))))).
% 0.21/0.55  
% 0.21/0.55  tff(u109,axiom,
% 0.21/0.55      (![X1, X3, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | (g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | (X0 = X2))))).
% 0.21/0.55  
% 0.21/0.55  tff(u108,negated_conjecture,
% 0.21/0.55      ((~m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))).
% 0.21/0.55  
% 0.21/0.55  tff(u107,axiom,
% 0.21/0.55      (![X1, X0, X2] : ((~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.55  
% 0.21/0.55  tff(u106,axiom,
% 0.21/0.55      (![X1, X0, X2] : ((~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2))))).
% 0.21/0.55  
% 0.21/0.55  tff(u105,negated_conjecture,
% 0.21/0.55      ((~(![X1, X0] : ((~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | r1_orders_2(sK1,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)))))) | (![X1, X0] : ((~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | r1_orders_2(sK1,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))))))).
% 0.21/0.55  
% 0.21/0.55  % (31426)# SZS output end Saturation.
% 0.21/0.55  % (31426)------------------------------
% 0.21/0.55  % (31426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (31426)Termination reason: Satisfiable
% 0.21/0.55  
% 0.21/0.55  % (31426)Memory used [KB]: 10746
% 0.21/0.55  % (31426)Time elapsed: 0.128 s
% 0.21/0.55  % (31426)------------------------------
% 0.21/0.55  % (31426)------------------------------
% 0.21/0.55  % (31428)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (31430)Refutation not found, incomplete strategy% (31430)------------------------------
% 0.21/0.55  % (31430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (31430)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (31430)Memory used [KB]: 10746
% 0.21/0.55  % (31430)Time elapsed: 0.139 s
% 0.21/0.55  % (31430)------------------------------
% 0.21/0.55  % (31430)------------------------------
% 0.21/0.55  % (31409)Success in time 0.186 s
%------------------------------------------------------------------------------
