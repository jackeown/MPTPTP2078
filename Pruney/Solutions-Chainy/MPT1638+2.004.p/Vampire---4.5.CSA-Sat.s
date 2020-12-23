%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:58 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   25 (  25 expanded)
%              Number of leaves         :   25 (  25 expanded)
%              Depth                    :    0
%              Number of atoms          :   72 (  72 expanded)
%              Number of equality atoms :   48 (  48 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u264,negated_conjecture,
    ( ~ ( k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(sK1) )
    | k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(sK1) )).

tff(u263,negated_conjecture,
    ( ~ ( k6_domain_1(u1_struct_0(sK0),sK2) != k1_tarski(sK2) )
    | k6_domain_1(u1_struct_0(sK0),sK2) != k1_tarski(sK2) )).

tff(u262,axiom,(
    ! [X3,X2] :
      ( sK3(X2,X3) != sK3(sK3(X2,X3),X3)
      | k1_tarski(X2) = X3
      | sK3(X2,X3) = X2
      | k1_tarski(sK3(X2,X3)) = X3 ) )).

tff(u261,axiom,(
    ! [X1,X0,X2] :
      ( sK3(X2,k1_tarski(X1)) != X0
      | sK3(X0,k1_tarski(X1)) = sK3(X2,k1_tarski(X1))
      | sK3(X2,k1_tarski(X1)) = X2
      | k1_tarski(X0) = k1_tarski(X1)
      | k1_tarski(X1) = k1_tarski(X2) ) )).

tff(u260,axiom,(
    ! [X1,X0,X2] :
      ( sK3(X2,k1_tarski(X1)) != X0
      | sK3(X2,k1_tarski(X1)) = X2
      | sK3(X0,k1_tarski(X1)) = X0
      | k1_tarski(X1) = k1_tarski(X2)
      | k1_tarski(X0) = k1_tarski(X1) ) )).

tff(u259,axiom,(
    ! [X1,X0] :
      ( X0 != X1
      | sK3(X0,k1_tarski(X1)) = X0
      | k1_tarski(X0) = k1_tarski(X1) ) )).

tff(u258,axiom,(
    ! [X1,X0] :
      ( X0 != X1
      | sK3(X0,k1_tarski(X1)) = X1
      | k1_tarski(X0) = k1_tarski(X1) ) )).

tff(u257,axiom,(
    ! [X1,X0] :
      ( sK3(X0,k1_tarski(X1)) = X0
      | sK3(X0,k1_tarski(X1)) = X1
      | k1_tarski(X0) = k1_tarski(X1) ) )).

tff(u256,axiom,(
    ! [X3,X5,X4] :
      ( sK3(X3,k1_tarski(X4)) = sK3(X5,k1_tarski(X4))
      | sK3(X5,k1_tarski(X4)) = X5
      | sK3(X3,k1_tarski(X4)) = X3
      | k1_tarski(X5) = k1_tarski(X4)
      | k1_tarski(X3) = k1_tarski(X4) ) )).

tff(u255,axiom,(
    ! [X3,X2] :
      ( sK3(sK3(X2,k1_tarski(X3)),k1_tarski(X3)) = X3
      | sK3(X2,k1_tarski(X3)) = X2
      | k1_tarski(X3) = k1_tarski(sK3(X2,k1_tarski(X3)))
      | k1_tarski(X3) = k1_tarski(X2) ) )).

tff(u254,axiom,(
    ! [X1,X0] :
      ( k1_tarski(X1) = k1_tarski(sK3(X0,k1_tarski(X1)))
      | sK3(X0,k1_tarski(X1)) = X0
      | k1_tarski(X0) = k1_tarski(X1) ) )).

tff(u253,negated_conjecture,
    ( ~ ~ r2_hidden(sK2,k6_waybel_0(sK0,sK1))
    | ~ r2_hidden(sK2,k6_waybel_0(sK0,sK1)) )).

tff(u252,axiom,(
    ! [X9,X11,X10] :
      ( ~ r2_hidden(X11,k1_tarski(X10))
      | sK3(X9,k1_tarski(X10)) = X11
      | sK3(X9,k1_tarski(X10)) = X9
      | k1_tarski(X9) = k1_tarski(X10) ) )).

tff(u251,axiom,(
    ! [X3,X0] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) )).

tff(u250,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X0,X1)
      | sK3(X0,X1) != X0
      | k1_tarski(X0) = X1 ) )).

tff(u249,axiom,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) )).

tff(u248,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK3(X0,X1),X1)
      | sK3(X0,X1) = X0
      | k1_tarski(X0) = X1 ) )).

tff(u247,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) )).

tff(u246,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) )).

tff(u245,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) )).

tff(u244,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) )).

tff(u243,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u242,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u241,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) )).

tff(u240,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK1,sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:53:17 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.45  % (11496)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.51  % (11501)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.51  % (11498)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.52  % (11488)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.52  % (11506)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.52  % (11509)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.52  % (11487)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.53  % (11493)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.53  % (11490)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.53  % (11490)Refutation not found, incomplete strategy% (11490)------------------------------
% 0.20/0.53  % (11490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (11490)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (11490)Memory used [KB]: 10618
% 0.20/0.53  % (11490)Time elapsed: 0.107 s
% 0.20/0.53  % (11490)------------------------------
% 0.20/0.53  % (11490)------------------------------
% 0.20/0.53  % (11503)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.53  % (11484)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.53  % (11495)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.54  % (11484)Refutation not found, incomplete strategy% (11484)------------------------------
% 0.20/0.54  % (11484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (11484)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (11484)Memory used [KB]: 10490
% 0.20/0.54  % (11484)Time elapsed: 0.099 s
% 0.20/0.54  % (11484)------------------------------
% 0.20/0.54  % (11484)------------------------------
% 0.20/0.54  % (11495)Refutation not found, incomplete strategy% (11495)------------------------------
% 0.20/0.54  % (11495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (11495)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (11495)Memory used [KB]: 10490
% 0.20/0.54  % (11495)Time elapsed: 0.123 s
% 0.20/0.54  % (11495)------------------------------
% 0.20/0.54  % (11495)------------------------------
% 0.20/0.54  % (11489)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.54  % (11486)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.54  % (11500)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.55  % (11497)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.55  % (11497)Refutation not found, incomplete strategy% (11497)------------------------------
% 0.20/0.55  % (11497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (11497)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (11497)Memory used [KB]: 6140
% 0.20/0.55  % (11497)Time elapsed: 0.101 s
% 0.20/0.55  % (11497)------------------------------
% 0.20/0.55  % (11497)------------------------------
% 0.20/0.55  % (11507)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.55  % (11494)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.55  % (11505)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.55  % (11508)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.55  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.55  % (11494)# SZS output start Saturation.
% 0.20/0.55  tff(u264,negated_conjecture,
% 0.20/0.55      ((~(k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(sK1))) | (k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(sK1)))).
% 0.20/0.55  
% 0.20/0.55  tff(u263,negated_conjecture,
% 0.20/0.55      ((~(k6_domain_1(u1_struct_0(sK0),sK2) != k1_tarski(sK2))) | (k6_domain_1(u1_struct_0(sK0),sK2) != k1_tarski(sK2)))).
% 0.20/0.55  
% 0.20/0.55  tff(u262,axiom,
% 0.20/0.55      (![X3, X2] : (((sK3(X2,X3) != sK3(sK3(X2,X3),X3)) | (k1_tarski(X2) = X3) | (sK3(X2,X3) = X2) | (k1_tarski(sK3(X2,X3)) = X3))))).
% 0.20/0.55  
% 0.20/0.55  tff(u261,axiom,
% 0.20/0.55      (![X1, X0, X2] : (((sK3(X2,k1_tarski(X1)) != X0) | (sK3(X0,k1_tarski(X1)) = sK3(X2,k1_tarski(X1))) | (sK3(X2,k1_tarski(X1)) = X2) | (k1_tarski(X0) = k1_tarski(X1)) | (k1_tarski(X1) = k1_tarski(X2)))))).
% 0.20/0.55  
% 0.20/0.55  tff(u260,axiom,
% 0.20/0.55      (![X1, X0, X2] : (((sK3(X2,k1_tarski(X1)) != X0) | (sK3(X2,k1_tarski(X1)) = X2) | (sK3(X0,k1_tarski(X1)) = X0) | (k1_tarski(X1) = k1_tarski(X2)) | (k1_tarski(X0) = k1_tarski(X1)))))).
% 0.20/0.55  
% 0.20/0.55  tff(u259,axiom,
% 0.20/0.55      (![X1, X0] : (((X0 != X1) | (sK3(X0,k1_tarski(X1)) = X0) | (k1_tarski(X0) = k1_tarski(X1)))))).
% 0.20/0.55  
% 0.20/0.55  tff(u258,axiom,
% 0.20/0.55      (![X1, X0] : (((X0 != X1) | (sK3(X0,k1_tarski(X1)) = X1) | (k1_tarski(X0) = k1_tarski(X1)))))).
% 0.20/0.55  
% 0.20/0.55  tff(u257,axiom,
% 0.20/0.55      (![X1, X0] : (((sK3(X0,k1_tarski(X1)) = X0) | (sK3(X0,k1_tarski(X1)) = X1) | (k1_tarski(X0) = k1_tarski(X1)))))).
% 0.20/0.55  
% 0.20/0.55  tff(u256,axiom,
% 0.20/0.55      (![X3, X5, X4] : (((sK3(X3,k1_tarski(X4)) = sK3(X5,k1_tarski(X4))) | (sK3(X5,k1_tarski(X4)) = X5) | (sK3(X3,k1_tarski(X4)) = X3) | (k1_tarski(X5) = k1_tarski(X4)) | (k1_tarski(X3) = k1_tarski(X4)))))).
% 0.20/0.55  
% 0.20/0.55  tff(u255,axiom,
% 0.20/0.55      (![X3, X2] : (((sK3(sK3(X2,k1_tarski(X3)),k1_tarski(X3)) = X3) | (sK3(X2,k1_tarski(X3)) = X2) | (k1_tarski(X3) = k1_tarski(sK3(X2,k1_tarski(X3)))) | (k1_tarski(X3) = k1_tarski(X2)))))).
% 0.20/0.55  
% 0.20/0.55  tff(u254,axiom,
% 0.20/0.55      (![X1, X0] : (((k1_tarski(X1) = k1_tarski(sK3(X0,k1_tarski(X1)))) | (sK3(X0,k1_tarski(X1)) = X0) | (k1_tarski(X0) = k1_tarski(X1)))))).
% 0.20/0.55  
% 0.20/0.55  tff(u253,negated_conjecture,
% 0.20/0.55      ((~~r2_hidden(sK2,k6_waybel_0(sK0,sK1))) | ~r2_hidden(sK2,k6_waybel_0(sK0,sK1)))).
% 0.20/0.55  
% 0.20/0.55  tff(u252,axiom,
% 0.20/0.55      (![X9, X11, X10] : ((~r2_hidden(X11,k1_tarski(X10)) | (sK3(X9,k1_tarski(X10)) = X11) | (sK3(X9,k1_tarski(X10)) = X9) | (k1_tarski(X9) = k1_tarski(X10)))))).
% 0.20/0.55  
% 0.20/0.55  tff(u251,axiom,
% 0.20/0.55      (![X3, X0] : ((~r2_hidden(X3,k1_tarski(X0)) | (X0 = X3))))).
% 0.20/0.55  
% 0.20/0.55  tff(u250,axiom,
% 0.20/0.55      (![X1, X0] : ((~r2_hidden(X0,X1) | (sK3(X0,X1) != X0) | (k1_tarski(X0) = X1))))).
% 0.20/0.55  
% 0.20/0.55  tff(u249,axiom,
% 0.20/0.55      (![X3] : (r2_hidden(X3,k1_tarski(X3))))).
% 0.20/0.55  
% 0.20/0.55  tff(u248,axiom,
% 0.20/0.55      (![X1, X0] : ((r2_hidden(sK3(X0,X1),X1) | (sK3(X0,X1) = X0) | (k1_tarski(X0) = X1))))).
% 0.20/0.55  
% 0.20/0.55  tff(u247,axiom,
% 0.20/0.55      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1))))).
% 0.20/0.55  
% 0.20/0.55  tff(u246,axiom,
% 0.20/0.55      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1))))).
% 0.20/0.55  
% 0.20/0.55  tff(u245,axiom,
% 0.20/0.55      (![X1, X0] : ((~m1_subset_1(X1,X0) | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | v1_xboole_0(X0))))).
% 0.20/0.55  
% 0.20/0.55  tff(u244,axiom,
% 0.20/0.55      (![X1, X0] : ((~m1_subset_1(X1,X0) | (k6_domain_1(X0,X1) = k1_tarski(X1)) | v1_xboole_0(X0))))).
% 0.20/0.55  
% 0.20/0.55  tff(u243,negated_conjecture,
% 0.20/0.55      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.20/0.55  
% 0.20/0.55  tff(u242,negated_conjecture,
% 0.20/0.55      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.20/0.55  
% 0.20/0.55  tff(u241,negated_conjecture,
% 0.20/0.55      ((~v1_xboole_0(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0)))).
% 0.20/0.55  
% 0.20/0.55  tff(u240,negated_conjecture,
% 0.20/0.55      ((~r1_orders_2(sK0,sK1,sK2)) | r1_orders_2(sK0,sK1,sK2))).
% 0.20/0.55  
% 0.20/0.55  % (11494)# SZS output end Saturation.
% 0.20/0.55  % (11494)------------------------------
% 0.20/0.55  % (11494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (11494)Termination reason: Satisfiable
% 0.20/0.55  
% 0.20/0.55  % (11494)Memory used [KB]: 10618
% 0.20/0.55  % (11494)Time elapsed: 0.138 s
% 0.20/0.55  % (11494)------------------------------
% 0.20/0.55  % (11494)------------------------------
% 0.20/0.55  % (11504)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.55  % (11502)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.56  % (11492)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.56  % (11499)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.56  % (11485)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.56  % (11485)Refutation not found, incomplete strategy% (11485)------------------------------
% 0.20/0.56  % (11485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (11485)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (11485)Memory used [KB]: 10618
% 0.20/0.56  % (11485)Time elapsed: 0.152 s
% 0.20/0.56  % (11485)------------------------------
% 0.20/0.56  % (11485)------------------------------
% 0.20/0.56  % (11491)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.56  % (11491)Refutation not found, incomplete strategy% (11491)------------------------------
% 0.20/0.56  % (11491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (11491)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (11491)Memory used [KB]: 1663
% 0.20/0.56  % (11491)Time elapsed: 0.148 s
% 0.20/0.56  % (11491)------------------------------
% 0.20/0.56  % (11491)------------------------------
% 0.20/0.57  % (11483)Success in time 0.204 s
%------------------------------------------------------------------------------
