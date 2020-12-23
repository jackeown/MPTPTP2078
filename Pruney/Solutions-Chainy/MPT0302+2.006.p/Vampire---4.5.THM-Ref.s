%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:59 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 110 expanded)
%              Number of leaves         :    9 (  29 expanded)
%              Depth                    :   13
%              Number of atoms          :  128 ( 357 expanded)
%              Number of equality atoms :   45 ( 165 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f86,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f79,f25,f85,f45])).

fof(f45,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,X2)
      | X2 = X3
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f34,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f34,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f28,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f85,plain,(
    r1_tarski(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f70,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK1,X0),sK0)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f65,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f63,f23])).

fof(f23,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( sK0 != sK1
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) )
   => ( sK0 != sK1
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
       => ( X0 = X1
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).

fof(f63,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK0)
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f55,f26])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f41,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X1,sK0) ) ),
    inference(superposition,[],[f32,f22])).

fof(f22,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f25,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f79,plain,(
    r1_tarski(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f76])).

fof(f76,plain,
    ( r1_tarski(sK0,sK1)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f61,f30])).

fof(f61,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK0,X0),sK1)
      | r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f54,f29])).

fof(f54,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f52,f24])).

fof(f24,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f51,f26])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK1)
      | r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f40,f33])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f31,f22])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:12:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (810975232)
% 0.20/0.39  ipcrm: permission denied for id (811073566)
% 0.20/0.40  ipcrm: permission denied for id (811139108)
% 0.20/0.40  ipcrm: permission denied for id (811204647)
% 0.20/0.45  ipcrm: permission denied for id (811401291)
% 0.20/0.45  ipcrm: permission denied for id (811466830)
% 0.20/0.46  ipcrm: permission denied for id (811532377)
% 0.20/0.50  ipcrm: permission denied for id (811630706)
% 0.20/0.51  ipcrm: permission denied for id (811696252)
% 0.20/0.51  ipcrm: permission denied for id (811729021)
% 0.38/0.65  % (4675)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.38/0.65  % (4678)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.38/0.66  % (4685)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.38/0.66  % (4674)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.38/0.66  % (4702)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.38/0.66  % (4702)Refutation found. Thanks to Tanya!
% 0.38/0.66  % SZS status Theorem for theBenchmark
% 0.38/0.66  % SZS output start Proof for theBenchmark
% 0.38/0.66  fof(f86,plain,(
% 0.38/0.66    $false),
% 0.38/0.66    inference(unit_resulting_resolution,[],[f79,f25,f85,f45])).
% 0.38/0.66  fof(f45,plain,(
% 0.38/0.66    ( ! [X2,X3] : (~r1_tarski(X3,X2) | X2 = X3 | ~r1_tarski(X2,X3)) )),
% 0.38/0.66    inference(superposition,[],[f34,f28])).
% 0.38/0.66  fof(f28,plain,(
% 0.38/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.38/0.66    inference(cnf_transformation,[],[f12])).
% 0.38/0.66  fof(f12,plain,(
% 0.38/0.66    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.38/0.66    inference(ennf_transformation,[],[f4])).
% 0.38/0.66  fof(f4,axiom,(
% 0.38/0.66    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.38/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.38/0.66  fof(f34,plain,(
% 0.38/0.66    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) )),
% 0.38/0.66    inference(superposition,[],[f28,f27])).
% 0.38/0.66  fof(f27,plain,(
% 0.38/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.38/0.66    inference(cnf_transformation,[],[f1])).
% 0.38/0.66  fof(f1,axiom,(
% 0.38/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.38/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.38/0.66  fof(f85,plain,(
% 0.38/0.66    r1_tarski(sK1,sK0)),
% 0.38/0.66    inference(duplicate_literal_removal,[],[f82])).
% 0.38/0.66  fof(f82,plain,(
% 0.38/0.66    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0)),
% 0.38/0.66    inference(resolution,[],[f70,f30])).
% 0.38/0.66  fof(f30,plain,(
% 0.38/0.66    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.38/0.66    inference(cnf_transformation,[],[f19])).
% 0.38/0.66  fof(f19,plain,(
% 0.38/0.66    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.38/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f18])).
% 0.38/0.66  fof(f18,plain,(
% 0.38/0.66    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.38/0.66    introduced(choice_axiom,[])).
% 0.38/0.66  fof(f13,plain,(
% 0.38/0.66    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.38/0.66    inference(ennf_transformation,[],[f8])).
% 0.38/0.66  fof(f8,plain,(
% 0.38/0.66    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.38/0.66    inference(unused_predicate_definition_removal,[],[f2])).
% 0.38/0.66  fof(f2,axiom,(
% 0.38/0.66    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.38/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.38/0.66  fof(f70,plain,(
% 0.38/0.66    ( ! [X0] : (r2_hidden(sK3(sK1,X0),sK0) | r1_tarski(sK1,X0)) )),
% 0.38/0.66    inference(resolution,[],[f65,f29])).
% 0.38/0.66  fof(f29,plain,(
% 0.38/0.66    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.38/0.66    inference(cnf_transformation,[],[f19])).
% 0.38/0.66  fof(f65,plain,(
% 0.38/0.66    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) )),
% 0.38/0.66    inference(subsumption_resolution,[],[f63,f23])).
% 0.38/0.66  fof(f23,plain,(
% 0.38/0.66    k1_xboole_0 != sK0),
% 0.38/0.66    inference(cnf_transformation,[],[f15])).
% 0.38/0.66  fof(f15,plain,(
% 0.38/0.66    sK0 != sK1 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 0.38/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f14])).
% 0.38/0.66  fof(f14,plain,(
% 0.38/0.66    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)) => (sK0 != sK1 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0))),
% 0.38/0.66    introduced(choice_axiom,[])).
% 0.38/0.66  fof(f10,plain,(
% 0.38/0.66    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 0.38/0.66    inference(flattening,[],[f9])).
% 0.38/0.66  fof(f9,plain,(
% 0.38/0.66    ? [X0,X1] : ((X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 0.38/0.66    inference(ennf_transformation,[],[f7])).
% 0.38/0.66  fof(f7,negated_conjecture,(
% 0.38/0.66    ~! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.38/0.66    inference(negated_conjecture,[],[f6])).
% 0.38/0.66  fof(f6,conjecture,(
% 0.38/0.66    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.38/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).
% 0.38/0.66  fof(f63,plain,(
% 0.38/0.66    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0) | k1_xboole_0 = sK0) )),
% 0.38/0.66    inference(resolution,[],[f55,f26])).
% 0.38/0.66  fof(f26,plain,(
% 0.38/0.66    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.38/0.66    inference(cnf_transformation,[],[f17])).
% 0.38/0.66  fof(f17,plain,(
% 0.38/0.66    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.38/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f16])).
% 0.38/0.66  fof(f16,plain,(
% 0.38/0.66    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.38/0.66    introduced(choice_axiom,[])).
% 0.38/0.66  fof(f11,plain,(
% 0.38/0.66    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.38/0.66    inference(ennf_transformation,[],[f3])).
% 0.38/0.66  fof(f3,axiom,(
% 0.38/0.66    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.38/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.38/0.66  fof(f55,plain,(
% 0.38/0.66    ( ! [X0,X1] : (~r2_hidden(X1,sK0) | ~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) )),
% 0.38/0.66    inference(resolution,[],[f41,f33])).
% 0.38/0.66  fof(f33,plain,(
% 0.38/0.66    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.38/0.66    inference(cnf_transformation,[],[f21])).
% 0.38/0.66  fof(f21,plain,(
% 0.38/0.66    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.38/0.66    inference(flattening,[],[f20])).
% 0.38/0.66  fof(f20,plain,(
% 0.38/0.66    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.38/0.66    inference(nnf_transformation,[],[f5])).
% 0.38/0.66  fof(f5,axiom,(
% 0.38/0.66    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.38/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.38/0.66  fof(f41,plain,(
% 0.38/0.66    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X1,sK0)) )),
% 0.38/0.66    inference(superposition,[],[f32,f22])).
% 0.38/0.66  fof(f22,plain,(
% 0.38/0.66    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 0.38/0.66    inference(cnf_transformation,[],[f15])).
% 0.38/0.66  fof(f32,plain,(
% 0.38/0.66    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.38/0.66    inference(cnf_transformation,[],[f21])).
% 0.38/0.66  fof(f25,plain,(
% 0.38/0.66    sK0 != sK1),
% 0.38/0.66    inference(cnf_transformation,[],[f15])).
% 0.38/0.66  fof(f79,plain,(
% 0.38/0.66    r1_tarski(sK0,sK1)),
% 0.38/0.66    inference(duplicate_literal_removal,[],[f76])).
% 0.38/0.66  fof(f76,plain,(
% 0.38/0.66    r1_tarski(sK0,sK1) | r1_tarski(sK0,sK1)),
% 0.38/0.66    inference(resolution,[],[f61,f30])).
% 0.38/0.66  fof(f61,plain,(
% 0.38/0.66    ( ! [X0] : (r2_hidden(sK3(sK0,X0),sK1) | r1_tarski(sK0,X0)) )),
% 0.38/0.66    inference(resolution,[],[f54,f29])).
% 0.38/0.66  fof(f54,plain,(
% 0.38/0.66    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(X0,sK1)) )),
% 0.38/0.66    inference(subsumption_resolution,[],[f52,f24])).
% 0.38/0.66  fof(f24,plain,(
% 0.38/0.66    k1_xboole_0 != sK1),
% 0.38/0.66    inference(cnf_transformation,[],[f15])).
% 0.38/0.66  fof(f52,plain,(
% 0.38/0.66    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0) | k1_xboole_0 = sK1) )),
% 0.38/0.66    inference(resolution,[],[f51,f26])).
% 0.38/0.66  fof(f51,plain,(
% 0.38/0.66    ( ! [X0,X1] : (~r2_hidden(X1,sK1) | r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 0.38/0.66    inference(resolution,[],[f40,f33])).
% 0.38/0.66  fof(f40,plain,(
% 0.38/0.66    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X0,sK1)) )),
% 0.38/0.66    inference(superposition,[],[f31,f22])).
% 0.38/0.66  fof(f31,plain,(
% 0.38/0.66    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.38/0.66    inference(cnf_transformation,[],[f21])).
% 0.38/0.66  % SZS output end Proof for theBenchmark
% 0.38/0.66  % (4702)------------------------------
% 0.38/0.66  % (4702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.66  % (4702)Termination reason: Refutation
% 0.38/0.66  
% 0.38/0.66  % (4702)Memory used [KB]: 1791
% 0.38/0.66  % (4702)Time elapsed: 0.105 s
% 0.38/0.66  % (4702)------------------------------
% 0.38/0.66  % (4702)------------------------------
% 0.38/0.66  % (4693)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.38/0.67  % (4694)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.38/0.67  % (4504)Success in time 0.319 s
%------------------------------------------------------------------------------
