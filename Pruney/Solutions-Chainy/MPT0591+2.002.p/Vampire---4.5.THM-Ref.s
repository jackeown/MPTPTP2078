%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:01 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   51 (  82 expanded)
%              Number of leaves         :   11 (  22 expanded)
%              Depth                    :   13
%              Number of atoms          :  121 ( 222 expanded)
%              Number of equality atoms :   57 ( 115 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f77,plain,(
    $false ),
    inference(global_subsumption,[],[f24,f76])).

fof(f76,plain,(
    k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f75])).

fof(f75,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f72,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f58,f30])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 ) ),
    inference(resolution,[],[f54,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | k1_relat_1(k2_zfmisc_1(X1,X0)) = X1 ) ),
    inference(resolution,[],[f51,f46])).

fof(f46,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,k1_relat_1(k2_zfmisc_1(X3,X4)))
      | k1_relat_1(k2_zfmisc_1(X3,X4)) = X3 ) ),
    inference(resolution,[],[f36,f33])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_relat_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_relat_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f39,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
      | r1_tarski(X1,X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2,X3] :
          ( r1_tarski(X1,X3)
          | ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            & ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1,X2,X3] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
         => r1_tarski(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1)))) ),
    inference(resolution,[],[f28,f31])).

fof(f31,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f72,plain,(
    sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(global_subsumption,[],[f23,f71])).

fof(f71,plain,
    ( sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f70])).

fof(f70,plain,
    ( sK1 != sK1
    | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f25,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f59,f30])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 ) ),
    inference(resolution,[],[f56,f29])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 ) ),
    inference(resolution,[],[f52,f45])).

fof(f45,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k2_relat_1(k2_zfmisc_1(X2,X1)))
      | k2_relat_1(k2_zfmisc_1(X2,X1)) = X1 ) ),
    inference(resolution,[],[f36,f32])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).

fof(f52,plain,(
    ! [X2,X3] :
      ( r1_tarski(X2,k2_relat_1(k2_zfmisc_1(X3,X2)))
      | v1_xboole_0(X3) ) ),
    inference(resolution,[],[f39,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | r1_tarski(X1,X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f25,plain,
    ( sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1))
      | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) )
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) != X1
          | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ( sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1))
        | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) )
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) != X1
        | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
              & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

fof(f23,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).

fof(f24,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:57:16 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (29727)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (29722)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (29727)Refutation not found, incomplete strategy% (29727)------------------------------
% 0.22/0.51  % (29727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (29727)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (29727)Memory used [KB]: 10490
% 0.22/0.51  % (29727)Time elapsed: 0.104 s
% 0.22/0.51  % (29727)------------------------------
% 0.22/0.51  % (29727)------------------------------
% 0.22/0.52  % (29730)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (29722)Refutation not found, incomplete strategy% (29722)------------------------------
% 0.22/0.52  % (29722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (29722)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (29722)Memory used [KB]: 10490
% 0.22/0.52  % (29722)Time elapsed: 0.093 s
% 0.22/0.52  % (29722)------------------------------
% 0.22/0.52  % (29722)------------------------------
% 0.22/0.53  % (29725)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.53  % (29725)Refutation not found, incomplete strategy% (29725)------------------------------
% 0.22/0.53  % (29725)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (29725)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (29725)Memory used [KB]: 6140
% 0.22/0.53  % (29725)Time elapsed: 0.105 s
% 0.22/0.53  % (29725)------------------------------
% 0.22/0.53  % (29725)------------------------------
% 0.22/0.53  % (29735)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.54  % (29741)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.54  % (29741)Refutation not found, incomplete strategy% (29741)------------------------------
% 0.22/0.54  % (29741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (29741)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (29741)Memory used [KB]: 10618
% 0.22/0.54  % (29741)Time elapsed: 0.120 s
% 0.22/0.54  % (29741)------------------------------
% 0.22/0.54  % (29741)------------------------------
% 0.22/0.54  % (29723)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.44/0.54  % (29740)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.44/0.55  % (29745)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.44/0.55  % (29726)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.44/0.55  % (29726)Refutation not found, incomplete strategy% (29726)------------------------------
% 1.44/0.55  % (29726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (29726)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (29726)Memory used [KB]: 6012
% 1.44/0.55  % (29726)Time elapsed: 0.130 s
% 1.44/0.55  % (29726)------------------------------
% 1.44/0.55  % (29726)------------------------------
% 1.44/0.55  % (29733)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.44/0.55  % (29743)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.44/0.56  % (29733)Refutation found. Thanks to Tanya!
% 1.44/0.56  % SZS status Theorem for theBenchmark
% 1.44/0.56  % SZS output start Proof for theBenchmark
% 1.44/0.56  fof(f77,plain,(
% 1.44/0.56    $false),
% 1.44/0.56    inference(global_subsumption,[],[f24,f76])).
% 1.44/0.56  fof(f76,plain,(
% 1.44/0.56    k1_xboole_0 = sK1),
% 1.44/0.56    inference(trivial_inequality_removal,[],[f75])).
% 1.44/0.56  fof(f75,plain,(
% 1.44/0.56    sK0 != sK0 | k1_xboole_0 = sK1),
% 1.44/0.56    inference(superposition,[],[f72,f60])).
% 1.44/0.56  fof(f60,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1) )),
% 1.44/0.56    inference(resolution,[],[f58,f30])).
% 1.44/0.56  fof(f30,plain,(
% 1.44/0.56    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 1.44/0.56    inference(cnf_transformation,[],[f20])).
% 1.44/0.56  fof(f20,plain,(
% 1.44/0.56    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 1.44/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f19])).
% 1.44/0.56  fof(f19,plain,(
% 1.44/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f16,plain,(
% 1.44/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.44/0.56    inference(ennf_transformation,[],[f2])).
% 1.44/0.56  fof(f2,axiom,(
% 1.44/0.56    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.44/0.56  fof(f58,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) )),
% 1.44/0.56    inference(resolution,[],[f54,f29])).
% 1.44/0.56  fof(f29,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f15])).
% 1.44/0.56  fof(f15,plain,(
% 1.44/0.56    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.44/0.56    inference(ennf_transformation,[],[f11])).
% 1.44/0.56  fof(f11,plain,(
% 1.44/0.56    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.44/0.56    inference(unused_predicate_definition_removal,[],[f1])).
% 1.44/0.56  fof(f1,axiom,(
% 1.44/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.44/0.56  fof(f54,plain,(
% 1.44/0.56    ( ! [X0,X1] : (v1_xboole_0(X0) | k1_relat_1(k2_zfmisc_1(X1,X0)) = X1) )),
% 1.44/0.56    inference(resolution,[],[f51,f46])).
% 1.44/0.56  fof(f46,plain,(
% 1.44/0.56    ( ! [X4,X3] : (~r1_tarski(X3,k1_relat_1(k2_zfmisc_1(X3,X4))) | k1_relat_1(k2_zfmisc_1(X3,X4)) = X3) )),
% 1.44/0.56    inference(resolution,[],[f36,f33])).
% 1.44/0.56  fof(f33,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f6])).
% 1.44/0.56  fof(f6,axiom,(
% 1.44/0.56    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_relat_1)).
% 1.44/0.56  fof(f36,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f22])).
% 1.44/0.56  fof(f22,plain,(
% 1.44/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.44/0.56    inference(flattening,[],[f21])).
% 1.44/0.56  fof(f21,plain,(
% 1.44/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.44/0.56    inference(nnf_transformation,[],[f3])).
% 1.44/0.56  fof(f3,axiom,(
% 1.44/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.44/0.56  fof(f51,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r1_tarski(X0,k1_relat_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 1.44/0.56    inference(resolution,[],[f39,f27])).
% 1.44/0.56  fof(f27,plain,(
% 1.44/0.56    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(X1,X3) | v1_xboole_0(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f13])).
% 1.44/0.56  fof(f13,plain,(
% 1.44/0.56    ! [X0] : (! [X1,X2,X3] : (r1_tarski(X1,X3) | (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) & ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))) | v1_xboole_0(X0))),
% 1.44/0.56    inference(ennf_transformation,[],[f4])).
% 1.44/0.56  fof(f4,axiom,(
% 1.44/0.56    ! [X0] : (~v1_xboole_0(X0) => ! [X1,X2,X3] : ((r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => r1_tarski(X1,X3)))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).
% 1.44/0.56  fof(f39,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1))))) )),
% 1.44/0.56    inference(resolution,[],[f28,f31])).
% 1.44/0.56  fof(f31,plain,(
% 1.44/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.44/0.56    inference(cnf_transformation,[],[f5])).
% 1.44/0.56  fof(f5,axiom,(
% 1.44/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.44/0.56  fof(f28,plain,(
% 1.44/0.56    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 1.44/0.56    inference(cnf_transformation,[],[f14])).
% 1.44/0.56  fof(f14,plain,(
% 1.44/0.56    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.44/0.56    inference(ennf_transformation,[],[f8])).
% 1.44/0.56  fof(f8,axiom,(
% 1.44/0.56    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 1.44/0.56  fof(f72,plain,(
% 1.44/0.56    sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.44/0.56    inference(global_subsumption,[],[f23,f71])).
% 1.44/0.56  fof(f71,plain,(
% 1.44/0.56    sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK0),
% 1.44/0.56    inference(trivial_inequality_removal,[],[f70])).
% 1.44/0.56  fof(f70,plain,(
% 1.44/0.56    sK1 != sK1 | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK0),
% 1.44/0.56    inference(superposition,[],[f25,f61])).
% 1.44/0.56  fof(f61,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X0) )),
% 1.44/0.56    inference(resolution,[],[f59,f30])).
% 1.44/0.56  fof(f59,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | k2_relat_1(k2_zfmisc_1(X0,X1)) = X1) )),
% 1.44/0.56    inference(resolution,[],[f56,f29])).
% 1.44/0.56  fof(f56,plain,(
% 1.44/0.56    ( ! [X0,X1] : (v1_xboole_0(X0) | k2_relat_1(k2_zfmisc_1(X0,X1)) = X1) )),
% 1.44/0.56    inference(resolution,[],[f52,f45])).
% 1.44/0.56  fof(f45,plain,(
% 1.44/0.56    ( ! [X2,X1] : (~r1_tarski(X1,k2_relat_1(k2_zfmisc_1(X2,X1))) | k2_relat_1(k2_zfmisc_1(X2,X1)) = X1) )),
% 1.44/0.56    inference(resolution,[],[f36,f32])).
% 1.44/0.56  fof(f32,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f7])).
% 1.44/0.56  fof(f7,axiom,(
% 1.44/0.56    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).
% 1.44/0.56  fof(f52,plain,(
% 1.44/0.56    ( ! [X2,X3] : (r1_tarski(X2,k2_relat_1(k2_zfmisc_1(X3,X2))) | v1_xboole_0(X3)) )),
% 1.44/0.56    inference(resolution,[],[f39,f26])).
% 1.44/0.56  fof(f26,plain,(
% 1.44/0.56    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | r1_tarski(X1,X3) | v1_xboole_0(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f13])).
% 1.44/0.56  fof(f25,plain,(
% 1.44/0.56    sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1)) | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.44/0.56    inference(cnf_transformation,[],[f18])).
% 1.44/0.56  fof(f18,plain,(
% 1.44/0.56    (sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1)) | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 1.44/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f17])).
% 1.44/0.56  fof(f17,plain,(
% 1.44/0.56    ? [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) != X1 | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0) => ((sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1)) | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f12,plain,(
% 1.44/0.56    ? [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) != X1 | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.44/0.56    inference(ennf_transformation,[],[f10])).
% 1.44/0.56  fof(f10,negated_conjecture,(
% 1.44/0.56    ~! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.44/0.56    inference(negated_conjecture,[],[f9])).
% 1.44/0.56  fof(f9,conjecture,(
% 1.44/0.56    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).
% 1.44/0.56  fof(f23,plain,(
% 1.44/0.56    k1_xboole_0 != sK0),
% 1.44/0.56    inference(cnf_transformation,[],[f18])).
% 1.44/0.56  fof(f24,plain,(
% 1.44/0.56    k1_xboole_0 != sK1),
% 1.44/0.56    inference(cnf_transformation,[],[f18])).
% 1.44/0.56  % SZS output end Proof for theBenchmark
% 1.44/0.56  % (29733)------------------------------
% 1.44/0.56  % (29733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (29733)Termination reason: Refutation
% 1.44/0.56  
% 1.44/0.56  % (29733)Memory used [KB]: 6140
% 1.44/0.56  % (29733)Time elapsed: 0.134 s
% 1.44/0.56  % (29733)------------------------------
% 1.44/0.56  % (29733)------------------------------
% 1.44/0.56  % (29720)Success in time 0.196 s
%------------------------------------------------------------------------------
