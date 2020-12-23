%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:29 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   42 (  75 expanded)
%              Number of leaves         :   10 (  21 expanded)
%              Depth                    :   13
%              Number of atoms          :   98 ( 219 expanded)
%              Number of equality atoms :   31 (  39 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f96,plain,(
    $false ),
    inference(subsumption_resolution,[],[f31,f95])).

fof(f95,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f94,f39])).

fof(f39,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f94,plain,(
    ! [X0] : k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f59,f93])).

fof(f93,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f92,f55])).

fof(f55,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f53,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f53,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f47,f37])).

fof(f37,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f92,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f90,f38])).

fof(f38,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f90,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k1_relat_1(k1_xboole_0),X0)
      | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f35,f54])).

fof(f54,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f53,f43])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK2(X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK2(X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f59,plain,(
    ! [X0] : k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k7_relat_1(k1_xboole_0,X0)) ),
    inference(resolution,[],[f33,f54])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f31,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f22])).

fof(f22,plain,
    ( ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:22:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (13920)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (13897)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (13896)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.45/0.55  % (13897)Refutation found. Thanks to Tanya!
% 1.45/0.55  % SZS status Theorem for theBenchmark
% 1.45/0.55  % SZS output start Proof for theBenchmark
% 1.45/0.55  fof(f96,plain,(
% 1.45/0.55    $false),
% 1.45/0.55    inference(subsumption_resolution,[],[f31,f95])).
% 1.45/0.55  fof(f95,plain,(
% 1.45/0.55    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 1.45/0.55    inference(forward_demodulation,[],[f94,f39])).
% 1.45/0.55  fof(f39,plain,(
% 1.45/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.45/0.55    inference(cnf_transformation,[],[f9])).
% 1.45/0.55  fof(f9,axiom,(
% 1.45/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.45/0.55  fof(f94,plain,(
% 1.45/0.55    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)) )),
% 1.45/0.55    inference(backward_demodulation,[],[f59,f93])).
% 1.45/0.55  fof(f93,plain,(
% 1.45/0.55    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 1.45/0.55    inference(subsumption_resolution,[],[f92,f55])).
% 1.45/0.55  fof(f55,plain,(
% 1.45/0.55    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.45/0.55    inference(resolution,[],[f53,f45])).
% 1.45/0.55  fof(f45,plain,(
% 1.45/0.55    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f30])).
% 1.45/0.55  fof(f30,plain,(
% 1.45/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.45/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f29])).
% 1.45/0.55  fof(f29,plain,(
% 1.45/0.55    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.45/0.55    introduced(choice_axiom,[])).
% 1.45/0.55  fof(f21,plain,(
% 1.45/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.45/0.55    inference(ennf_transformation,[],[f14])).
% 1.45/0.55  fof(f14,plain,(
% 1.45/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.45/0.55    inference(rectify,[],[f1])).
% 1.45/0.55  fof(f1,axiom,(
% 1.45/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.45/0.55  fof(f53,plain,(
% 1.45/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.45/0.55    inference(condensation,[],[f52])).
% 1.45/0.55  fof(f52,plain,(
% 1.45/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 1.45/0.55    inference(resolution,[],[f47,f37])).
% 1.45/0.55  fof(f37,plain,(
% 1.45/0.55    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f6])).
% 1.45/0.55  fof(f6,axiom,(
% 1.45/0.55    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.45/0.55  fof(f47,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f30])).
% 1.45/0.55  fof(f92,plain,(
% 1.45/0.55    ( ! [X0] : (~r1_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 1.45/0.55    inference(forward_demodulation,[],[f90,f38])).
% 1.45/0.55  fof(f38,plain,(
% 1.45/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.45/0.55    inference(cnf_transformation,[],[f9])).
% 1.45/0.55  fof(f90,plain,(
% 1.45/0.55    ( ! [X0] : (~r1_xboole_0(k1_relat_1(k1_xboole_0),X0) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 1.45/0.55    inference(resolution,[],[f35,f54])).
% 1.45/0.55  fof(f54,plain,(
% 1.45/0.55    v1_relat_1(k1_xboole_0)),
% 1.45/0.55    inference(resolution,[],[f53,f43])).
% 1.45/0.55  fof(f43,plain,(
% 1.45/0.55    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_relat_1(X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f28])).
% 1.45/0.55  fof(f28,plain,(
% 1.45/0.55    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK2(X0) & r2_hidden(sK2(X0),X0)))),
% 1.45/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f27])).
% 1.45/0.55  fof(f27,plain,(
% 1.45/0.55    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK2(X0) & r2_hidden(sK2(X0),X0)))),
% 1.45/0.55    introduced(choice_axiom,[])).
% 1.45/0.55  fof(f20,plain,(
% 1.45/0.55    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.45/0.55    inference(ennf_transformation,[],[f15])).
% 1.45/0.55  fof(f15,plain,(
% 1.45/0.55    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 1.45/0.55    inference(unused_predicate_definition_removal,[],[f7])).
% 1.45/0.55  fof(f7,axiom,(
% 1.45/0.55    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 1.45/0.55  fof(f35,plain,(
% 1.45/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f24])).
% 1.45/0.55  fof(f24,plain,(
% 1.45/0.55    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.45/0.55    inference(nnf_transformation,[],[f18])).
% 1.45/0.55  fof(f18,plain,(
% 1.45/0.55    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.45/0.55    inference(ennf_transformation,[],[f10])).
% 1.45/0.55  fof(f10,axiom,(
% 1.45/0.55    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 1.45/0.55  fof(f59,plain,(
% 1.45/0.55    ( ! [X0] : (k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k7_relat_1(k1_xboole_0,X0))) )),
% 1.45/0.55    inference(resolution,[],[f33,f54])).
% 1.45/0.55  fof(f33,plain,(
% 1.45/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f17])).
% 1.45/0.55  fof(f17,plain,(
% 1.45/0.55    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.45/0.55    inference(ennf_transformation,[],[f8])).
% 1.45/0.55  fof(f8,axiom,(
% 1.45/0.55    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.45/0.55  fof(f31,plain,(
% 1.45/0.55    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 1.45/0.55    inference(cnf_transformation,[],[f23])).
% 1.45/0.55  fof(f23,plain,(
% 1.45/0.55    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 1.45/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f22])).
% 1.45/0.55  fof(f22,plain,(
% 1.45/0.55    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 1.45/0.55    introduced(choice_axiom,[])).
% 1.45/0.55  fof(f16,plain,(
% 1.45/0.55    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 1.45/0.55    inference(ennf_transformation,[],[f12])).
% 1.45/0.55  fof(f12,negated_conjecture,(
% 1.45/0.55    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 1.45/0.55    inference(negated_conjecture,[],[f11])).
% 1.45/0.55  fof(f11,conjecture,(
% 1.45/0.55    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 1.45/0.55  % SZS output end Proof for theBenchmark
% 1.45/0.55  % (13897)------------------------------
% 1.45/0.55  % (13897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (13897)Termination reason: Refutation
% 1.45/0.55  
% 1.45/0.55  % (13897)Memory used [KB]: 6268
% 1.45/0.55  % (13897)Time elapsed: 0.127 s
% 1.45/0.55  % (13897)------------------------------
% 1.45/0.55  % (13897)------------------------------
% 1.45/0.56  % (13896)Refutation not found, incomplete strategy% (13896)------------------------------
% 1.45/0.56  % (13896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (13896)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (13891)Success in time 0.193 s
%------------------------------------------------------------------------------
