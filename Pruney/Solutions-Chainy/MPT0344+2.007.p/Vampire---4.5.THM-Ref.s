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
% DateTime   : Thu Dec  3 12:43:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 340 expanded)
%              Number of leaves         :   10 (  85 expanded)
%              Depth                    :   24
%              Number of atoms          :  169 (1226 expanded)
%              Number of equality atoms :   51 ( 372 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f194,plain,(
    $false ),
    inference(subsumption_resolution,[],[f191,f108])).

fof(f108,plain,(
    ! [X0] : r2_hidden(X0,sK1) ),
    inference(resolution,[],[f101,f50])).

fof(f50,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

% (15942)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK1,X1)
      | r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f31,f99])).

fof(f99,plain,(
    ! [X0] : k2_tarski(X0,X0) = sK1 ),
    inference(backward_demodulation,[],[f47,f96])).

fof(f96,plain,(
    ! [X0] : k1_tarski(X0) = sK1 ),
    inference(trivial_inequality_removal,[],[f93])).

fof(f93,plain,(
    ! [X0] :
      ( sK1 != sK1
      | k1_tarski(X0) = sK1 ) ),
    inference(equality_factoring,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = sK1
      | k1_tarski(X1) = sK1 ) ),
    inference(subsumption_resolution,[],[f88,f29])).

fof(f29,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK1)
        | ~ m1_subset_1(X2,sK0) )
    & k1_xboole_0 != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,X0) )
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ! [X2] :
          ( ~ r2_hidden(X2,sK1)
          | ~ m1_subset_1(X2,sK0) )
      & k1_xboole_0 != sK1
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ~ ( ! [X2] :
                ( m1_subset_1(X2,X0)
               => ~ r2_hidden(X2,X1) )
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

fof(f88,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = sK1
      | k1_tarski(X1) = sK1
      | k1_xboole_0 = sK1 ) ),
    inference(duplicate_literal_removal,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = sK1
      | k1_tarski(X1) = sK1
      | k1_xboole_0 = sK1
      | k1_tarski(X1) = sK1 ) ),
    inference(resolution,[],[f84,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(sK1,X0),sK1)
      | k1_tarski(X1) = sK1
      | k1_tarski(X0) = sK1 ) ),
    inference(resolution,[],[f77,f30])).

fof(f30,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(sK1,X0),sK0)
      | k1_tarski(X0) = sK1
      | k1_tarski(X1) = sK1 ) ),
    inference(resolution,[],[f59,f60])).

fof(f60,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(sK0)
      | k1_tarski(X1) = sK1 ) ),
    inference(resolution,[],[f55,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK1,X0),sK0)
      | k1_tarski(X0) = sK1 ) ),
    inference(subsumption_resolution,[],[f54,f29])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK1,X0),sK0)
      | k1_xboole_0 = sK1
      | k1_tarski(X0) = sK1 ) ),
    inference(resolution,[],[f51,f34])).

fof(f51,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f28,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f59,plain,(
    ! [X0] :
      ( v1_xboole_0(sK0)
      | m1_subset_1(sK2(sK1,X0),sK0)
      | k1_tarski(X0) = sK1 ) ),
    inference(resolution,[],[f55,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f21])).

% (15947)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f191,plain,(
    ! [X0] : ~ r2_hidden(X0,sK1) ),
    inference(resolution,[],[f182,f30])).

fof(f182,plain,(
    ! [X0] : m1_subset_1(X0,sK0) ),
    inference(resolution,[],[f125,f126])).

fof(f126,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f110,f36])).

fof(f110,plain,(
    ! [X0] : r2_hidden(X0,sK0) ),
    inference(resolution,[],[f108,f51])).

fof(f125,plain,(
    ! [X0] :
      ( v1_xboole_0(sK0)
      | m1_subset_1(X0,sK0) ) ),
    inference(resolution,[],[f110,f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:53:30 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (15938)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.55  % (15960)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (15948)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.56  % (15952)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.56  % (15948)Refutation not found, incomplete strategy% (15948)------------------------------
% 0.22/0.56  % (15948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (15948)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (15948)Memory used [KB]: 10746
% 0.22/0.56  % (15948)Time elapsed: 0.128 s
% 0.22/0.56  % (15948)------------------------------
% 0.22/0.56  % (15948)------------------------------
% 0.22/0.57  % (15941)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.57  % (15952)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % (15961)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.57  % (15944)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.57  % (15940)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f194,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(subsumption_resolution,[],[f191,f108])).
% 0.22/0.57  fof(f108,plain,(
% 0.22/0.57    ( ! [X0] : (r2_hidden(X0,sK1)) )),
% 0.22/0.57    inference(resolution,[],[f101,f50])).
% 0.22/0.57  fof(f50,plain,(
% 0.22/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.57    inference(equality_resolution,[],[f43])).
% 0.22/0.57  fof(f43,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.22/0.57    inference(cnf_transformation,[],[f27])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.57    inference(flattening,[],[f26])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.57    inference(nnf_transformation,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.57  % (15942)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.57  fof(f101,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(sK1,X1) | r2_hidden(X0,X1)) )),
% 0.22/0.57    inference(superposition,[],[f31,f99])).
% 0.22/0.57  fof(f99,plain,(
% 0.22/0.57    ( ! [X0] : (k2_tarski(X0,X0) = sK1) )),
% 0.22/0.57    inference(backward_demodulation,[],[f47,f96])).
% 0.22/0.57  fof(f96,plain,(
% 0.22/0.57    ( ! [X0] : (k1_tarski(X0) = sK1) )),
% 0.22/0.57    inference(trivial_inequality_removal,[],[f93])).
% 0.22/0.57  fof(f93,plain,(
% 0.22/0.57    ( ! [X0] : (sK1 != sK1 | k1_tarski(X0) = sK1) )),
% 0.22/0.57    inference(equality_factoring,[],[f89])).
% 0.22/0.57  fof(f89,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k1_tarski(X0) = sK1 | k1_tarski(X1) = sK1) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f88,f29])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    k1_xboole_0 != sK1),
% 0.22/0.57    inference(cnf_transformation,[],[f20])).
% 0.22/0.57  fof(f20,plain,(
% 0.22/0.57    ! [X2] : (~r2_hidden(X2,sK1) | ~m1_subset_1(X2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f19])).
% 0.22/0.57  fof(f19,plain,(
% 0.22/0.57    ? [X0,X1] : (! [X2] : (~r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (! [X2] : (~r2_hidden(X2,sK1) | ~m1_subset_1(X2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f14,plain,(
% 0.22/0.57    ? [X0,X1] : (! [X2] : (~r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.57    inference(flattening,[],[f13])).
% 0.22/0.57  fof(f13,plain,(
% 0.22/0.57    ? [X0,X1] : ((! [X2] : (~r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f12])).
% 0.22/0.57  fof(f12,negated_conjecture,(
% 0.22/0.57    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 0.22/0.57    inference(negated_conjecture,[],[f11])).
% 0.22/0.57  fof(f11,conjecture,(
% 0.22/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).
% 0.22/0.57  fof(f88,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k1_tarski(X0) = sK1 | k1_tarski(X1) = sK1 | k1_xboole_0 = sK1) )),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f87])).
% 0.22/0.57  fof(f87,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k1_tarski(X0) = sK1 | k1_tarski(X1) = sK1 | k1_xboole_0 = sK1 | k1_tarski(X1) = sK1) )),
% 0.22/0.57    inference(resolution,[],[f84,f34])).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ! [X0,X1] : ((sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f23])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f15,plain,(
% 0.22/0.57    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.22/0.57    inference(ennf_transformation,[],[f8])).
% 0.22/0.57  fof(f8,axiom,(
% 0.22/0.57    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 0.22/0.57  fof(f84,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r2_hidden(sK2(sK1,X0),sK1) | k1_tarski(X1) = sK1 | k1_tarski(X0) = sK1) )),
% 0.22/0.57    inference(resolution,[],[f77,f30])).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ( ! [X2] : (~m1_subset_1(X2,sK0) | ~r2_hidden(X2,sK1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f20])).
% 0.22/0.57  fof(f77,plain,(
% 0.22/0.57    ( ! [X0,X1] : (m1_subset_1(sK2(sK1,X0),sK0) | k1_tarski(X0) = sK1 | k1_tarski(X1) = sK1) )),
% 0.22/0.57    inference(resolution,[],[f59,f60])).
% 0.22/0.57  fof(f60,plain,(
% 0.22/0.57    ( ! [X1] : (~v1_xboole_0(sK0) | k1_tarski(X1) = sK1) )),
% 0.22/0.57    inference(resolution,[],[f55,f36])).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_xboole_0(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f16])).
% 0.22/0.57  fof(f16,plain,(
% 0.22/0.57    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f2])).
% 0.22/0.57  fof(f2,axiom,(
% 0.22/0.57    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).
% 0.22/0.57  fof(f55,plain,(
% 0.22/0.57    ( ! [X0] : (r2_hidden(sK2(sK1,X0),sK0) | k1_tarski(X0) = sK1) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f54,f29])).
% 0.22/0.57  fof(f54,plain,(
% 0.22/0.57    ( ! [X0] : (r2_hidden(sK2(sK1,X0),sK0) | k1_xboole_0 = sK1 | k1_tarski(X0) = sK1) )),
% 0.22/0.57    inference(resolution,[],[f51,f34])).
% 0.22/0.57  fof(f51,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) )),
% 0.22/0.57    inference(resolution,[],[f28,f37])).
% 0.22/0.57  fof(f37,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f17])).
% 0.22/0.57  fof(f17,plain,(
% 0.22/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,axiom,(
% 0.22/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.57    inference(cnf_transformation,[],[f20])).
% 0.22/0.57  fof(f59,plain,(
% 0.22/0.57    ( ! [X0] : (v1_xboole_0(sK0) | m1_subset_1(sK2(sK1,X0),sK0) | k1_tarski(X0) = sK1) )),
% 0.22/0.57    inference(resolution,[],[f55,f39])).
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f25])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.22/0.57    inference(nnf_transformation,[],[f18])).
% 0.22/0.57  fof(f18,plain,(
% 0.22/0.57    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f9])).
% 0.22/0.57  fof(f9,axiom,(
% 0.22/0.57    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.57  fof(f47,plain,(
% 0.22/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f3])).
% 0.22/0.57  fof(f3,axiom,(
% 0.22/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X0,X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f22])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.22/0.57    inference(flattening,[],[f21])).
% 0.22/0.57  % (15947)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.22/0.57    inference(nnf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.22/0.57  fof(f191,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(X0,sK1)) )),
% 0.22/0.57    inference(resolution,[],[f182,f30])).
% 0.22/0.57  fof(f182,plain,(
% 0.22/0.57    ( ! [X0] : (m1_subset_1(X0,sK0)) )),
% 0.22/0.57    inference(resolution,[],[f125,f126])).
% 0.22/0.57  fof(f126,plain,(
% 0.22/0.57    ~v1_xboole_0(sK0)),
% 0.22/0.57    inference(resolution,[],[f110,f36])).
% 0.22/0.57  fof(f110,plain,(
% 0.22/0.57    ( ! [X0] : (r2_hidden(X0,sK0)) )),
% 0.22/0.57    inference(resolution,[],[f108,f51])).
% 0.22/0.57  fof(f125,plain,(
% 0.22/0.57    ( ! [X0] : (v1_xboole_0(sK0) | m1_subset_1(X0,sK0)) )),
% 0.22/0.57    inference(resolution,[],[f110,f39])).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (15952)------------------------------
% 0.22/0.57  % (15952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (15952)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (15953)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.57  % (15952)Memory used [KB]: 1791
% 0.22/0.57  % (15952)Time elapsed: 0.141 s
% 0.22/0.57  % (15952)------------------------------
% 0.22/0.57  % (15952)------------------------------
% 0.22/0.58  % (15943)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.58  % (15937)Success in time 0.212 s
%------------------------------------------------------------------------------
