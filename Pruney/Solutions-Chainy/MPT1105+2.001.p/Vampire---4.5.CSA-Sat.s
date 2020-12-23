%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:03 EST 2020

% Result     : CounterSatisfiable 1.42s
% Output     : Saturation 1.42s
% Verified   : 
% Statistics : Number of formulae       :   14 (  14 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    0
%              Number of atoms          :   39 (  39 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u58,negated_conjecture,(
    k2_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),k1_struct_0(sK0)) )).

tff(u57,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_tarski(X1,X2)
      | r1_xboole_0(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) )).

tff(u56,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) )).

tff(u55,axiom,(
    ! [X1] : r1_tarski(X1,X1) )).

tff(u54,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_xboole_0(X0,k3_subset_1(X1,X0)) ) )).

tff(u53,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) )).

tff(u52,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) )).

tff(u51,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
      | ~ l1_struct_0(X0) ) )).

tff(u50,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_struct_0(X0) = X1
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k1_xboole_0
      | ~ l1_struct_0(X0) ) )).

tff(u49,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) )).

tff(u48,axiom,(
    ! [X0] :
      ( ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k2_struct_0(X0))
      | ~ l1_struct_0(X0) ) )).

tff(u47,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_xboole_0(X1,k3_subset_1(X0,X2))
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) )).

tff(u46,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_xboole_0(X1,X2)
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2
      | k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) )).

tff(u45,negated_conjecture,(
    l1_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 19:32:21 EST 2020
% 0.23/0.36  % CPUTime    : 
% 0.23/0.48  % (31672)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.23/0.48  % (31664)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.23/0.48  % (31664)Refutation not found, incomplete strategy% (31664)------------------------------
% 0.23/0.48  % (31664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.48  % (31664)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.48  
% 0.23/0.48  % (31664)Memory used [KB]: 6012
% 0.23/0.48  % (31664)Time elapsed: 0.046 s
% 0.23/0.48  % (31664)------------------------------
% 0.23/0.48  % (31664)------------------------------
% 0.23/0.49  % (31665)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.50  % (31657)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.23/0.50  % (31657)Refutation not found, incomplete strategy% (31657)------------------------------
% 0.23/0.50  % (31657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.50  % (31657)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.50  
% 0.23/0.50  % (31657)Memory used [KB]: 10490
% 0.23/0.50  % (31657)Time elapsed: 0.046 s
% 0.23/0.50  % (31657)------------------------------
% 0.23/0.50  % (31657)------------------------------
% 0.23/0.51  % (31656)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.23/0.51  % (31658)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.23/0.51  % (31658)Refutation not found, incomplete strategy% (31658)------------------------------
% 0.23/0.51  % (31658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (31658)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.51  
% 0.23/0.51  % (31658)Memory used [KB]: 1663
% 0.23/0.51  % (31658)Time elapsed: 0.090 s
% 0.23/0.51  % (31658)------------------------------
% 0.23/0.51  % (31658)------------------------------
% 0.23/0.51  % (31651)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.23/0.52  % (31651)Refutation not found, incomplete strategy% (31651)------------------------------
% 0.23/0.52  % (31651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (31651)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (31651)Memory used [KB]: 10490
% 0.23/0.52  % (31651)Time elapsed: 0.086 s
% 0.23/0.52  % (31651)------------------------------
% 0.23/0.52  % (31651)------------------------------
% 0.23/0.52  % (31667)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.23/0.52  % (31666)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.23/0.52  % (31655)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.23/0.52  % (31659)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.23/0.53  % (31676)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.23/0.53  % (31652)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.53  % (31654)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.23/0.53  % (31652)Refutation not found, incomplete strategy% (31652)------------------------------
% 0.23/0.53  % (31652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (31652)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (31652)Memory used [KB]: 10490
% 0.23/0.53  % (31652)Time elapsed: 0.106 s
% 0.23/0.53  % (31652)------------------------------
% 0.23/0.53  % (31652)------------------------------
% 0.23/0.53  % (31654)Refutation not found, incomplete strategy% (31654)------------------------------
% 0.23/0.53  % (31654)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (31654)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (31654)Memory used [KB]: 6012
% 0.23/0.53  % (31654)Time elapsed: 0.107 s
% 0.23/0.53  % (31654)------------------------------
% 0.23/0.53  % (31654)------------------------------
% 0.23/0.53  % (31675)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.23/0.53  % (31653)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.23/0.53  % (31670)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.23/0.53  % (31663)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.23/0.53  % (31674)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.23/0.53  % (31656)Refutation not found, incomplete strategy% (31656)------------------------------
% 0.23/0.53  % (31656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (31656)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (31656)Memory used [KB]: 6012
% 0.23/0.53  % (31656)Time elapsed: 0.108 s
% 0.23/0.53  % (31656)------------------------------
% 0.23/0.53  % (31656)------------------------------
% 0.23/0.54  % (31673)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.23/0.54  % (31669)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.23/0.54  % (31662)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.23/0.54  % (31662)Refutation not found, incomplete strategy% (31662)------------------------------
% 0.23/0.54  % (31662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (31662)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (31662)Memory used [KB]: 10490
% 0.23/0.54  % (31662)Time elapsed: 0.122 s
% 0.23/0.54  % (31662)------------------------------
% 0.23/0.54  % (31662)------------------------------
% 1.42/0.55  % (31660)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.42/0.55  % (31661)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.42/0.55  % SZS status CounterSatisfiable for theBenchmark
% 1.42/0.55  % (31661)# SZS output start Saturation.
% 1.42/0.55  tff(u58,negated_conjecture,
% 1.42/0.55      (k2_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),k1_struct_0(sK0)))).
% 1.42/0.55  
% 1.42/0.55  tff(u57,axiom,
% 1.42/0.55      (![X1, X0, X2] : ((~r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))))).
% 1.42/0.55  
% 1.42/0.55  tff(u56,axiom,
% 1.42/0.55      (![X1, X0] : ((~r1_tarski(X1,X0) | (X0 = X1) | ~r1_tarski(X0,X1))))).
% 1.42/0.55  
% 1.42/0.55  tff(u55,axiom,
% 1.42/0.55      (![X1] : (r1_tarski(X1,X1)))).
% 1.42/0.55  
% 1.42/0.55  tff(u54,axiom,
% 1.42/0.55      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_xboole_0(X0,k3_subset_1(X1,X0)))))).
% 1.42/0.55  
% 1.42/0.55  tff(u53,axiom,
% 1.42/0.55      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)))))).
% 1.42/0.55  
% 1.42/0.55  tff(u52,axiom,
% 1.42/0.55      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))))).
% 1.42/0.55  
% 1.42/0.55  tff(u51,axiom,
% 1.42/0.55      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1) | ~l1_struct_0(X0))))).
% 1.42/0.55  
% 1.42/0.55  tff(u50,axiom,
% 1.42/0.55      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | (k2_struct_0(X0) = X1) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k1_xboole_0) | ~l1_struct_0(X0))))).
% 1.42/0.55  
% 1.42/0.55  tff(u49,axiom,
% 1.42/0.55      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | (k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0)) | ~l1_struct_0(X0))))).
% 1.42/0.55  
% 1.42/0.55  tff(u48,axiom,
% 1.42/0.55      (![X0] : ((~m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k2_struct_0(X0))) | ~l1_struct_0(X0))))).
% 1.42/0.55  
% 1.42/0.55  tff(u47,axiom,
% 1.42/0.55      (![X1, X0, X2] : ((~r1_xboole_0(X1,k3_subset_1(X0,X2)) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))))).
% 1.42/0.55  
% 1.42/0.55  tff(u46,axiom,
% 1.42/0.55      (![X1, X0, X2] : ((~r1_xboole_0(X1,X2) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2) | (k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))))).
% 1.42/0.55  
% 1.42/0.55  tff(u45,negated_conjecture,
% 1.42/0.55      l1_struct_0(sK0)).
% 1.42/0.55  
% 1.42/0.55  % (31661)# SZS output end Saturation.
% 1.42/0.55  % (31661)------------------------------
% 1.42/0.55  % (31661)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (31661)Termination reason: Satisfiable
% 1.42/0.55  
% 1.42/0.55  % (31661)Memory used [KB]: 10618
% 1.42/0.55  % (31661)Time elapsed: 0.130 s
% 1.42/0.55  % (31661)------------------------------
% 1.42/0.55  % (31661)------------------------------
% 1.42/0.55  % (31650)Success in time 0.18 s
%------------------------------------------------------------------------------
