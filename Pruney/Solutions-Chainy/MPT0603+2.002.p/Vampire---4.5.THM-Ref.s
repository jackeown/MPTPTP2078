%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   51 (  70 expanded)
%              Number of leaves         :   11 (  17 expanded)
%              Depth                    :   11
%              Number of atoms          :  119 ( 183 expanded)
%              Number of equality atoms :   35 (  56 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f212,plain,(
    $false ),
    inference(subsumption_resolution,[],[f211,f154])).

fof(f154,plain,(
    k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0) ),
    inference(resolution,[],[f150,f52])).

fof(f52,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    & r1_xboole_0(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f47])).

fof(f47,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
        & r1_xboole_0(X0,X1)
        & v1_relat_1(X2) )
   => ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
      & r1_xboole_0(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_xboole_0(X0,X1)
         => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f29,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

fof(f150,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    inference(condensation,[],[f149])).

fof(f149,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 = X3
      | ~ v1_relat_1(X4)
      | k1_xboole_0 = k7_relat_1(X4,k1_xboole_0) ) ),
    inference(resolution,[],[f128,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f128,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k7_relat_1(X1,k1_xboole_0))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f127,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_xboole_0(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & v1_relat_1(X0) )
     => ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc16_relat_1)).

fof(f127,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f126,f93])).

fof(f93,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f74,f59])).

fof(f59,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f126,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ r1_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f101,f65])).

fof(f65,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => r2_xboole_0(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_xboole_1)).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | v1_xboole_0(X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f73,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f211,plain,(
    k1_xboole_0 != k7_relat_1(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f204,f104])).

fof(f104,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f79,f53])).

fof(f53,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f204,plain,(
    k1_xboole_0 != k7_relat_1(sK2,k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f54,f202])).

fof(f202,plain,(
    ! [X10,X9] : k7_relat_1(k7_relat_1(sK2,X9),X10) = k7_relat_1(sK2,k3_xboole_0(X9,X10)) ),
    inference(resolution,[],[f84,f52])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f54,plain,(
    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:50:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (10217)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (10214)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (10217)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (10211)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (10230)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (10210)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (10220)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (10221)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (10238)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.27/0.52  % (10232)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.27/0.52  % SZS output start Proof for theBenchmark
% 1.27/0.52  fof(f212,plain,(
% 1.27/0.52    $false),
% 1.27/0.52    inference(subsumption_resolution,[],[f211,f154])).
% 1.27/0.52  fof(f154,plain,(
% 1.27/0.52    k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0)),
% 1.27/0.52    inference(resolution,[],[f150,f52])).
% 1.27/0.52  fof(f52,plain,(
% 1.27/0.52    v1_relat_1(sK2)),
% 1.27/0.52    inference(cnf_transformation,[],[f48])).
% 1.27/0.52  fof(f48,plain,(
% 1.27/0.52    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) & r1_xboole_0(sK0,sK1) & v1_relat_1(sK2)),
% 1.27/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f47])).
% 1.27/0.52  fof(f47,plain,(
% 1.27/0.52    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1) & v1_relat_1(X2)) => (k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) & r1_xboole_0(sK0,sK1) & v1_relat_1(sK2))),
% 1.27/0.52    introduced(choice_axiom,[])).
% 1.27/0.52  fof(f34,plain,(
% 1.27/0.52    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1) & v1_relat_1(X2))),
% 1.27/0.52    inference(flattening,[],[f33])).
% 1.27/0.52  fof(f33,plain,(
% 1.27/0.52    ? [X0,X1,X2] : ((k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1)) & v1_relat_1(X2))),
% 1.27/0.52    inference(ennf_transformation,[],[f30])).
% 1.27/0.52  fof(f30,negated_conjecture,(
% 1.27/0.52    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 1.27/0.52    inference(negated_conjecture,[],[f29])).
% 1.27/0.52  fof(f29,conjecture,(
% 1.27/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).
% 1.27/0.52  fof(f150,plain,(
% 1.27/0.52    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)) )),
% 1.27/0.52    inference(condensation,[],[f149])).
% 1.27/0.52  fof(f149,plain,(
% 1.27/0.52    ( ! [X4,X3] : (k1_xboole_0 = X3 | ~v1_relat_1(X4) | k1_xboole_0 = k7_relat_1(X4,k1_xboole_0)) )),
% 1.27/0.52    inference(resolution,[],[f128,f62])).
% 1.27/0.52  fof(f62,plain,(
% 1.27/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.27/0.52    inference(cnf_transformation,[],[f35])).
% 1.27/0.52  fof(f35,plain,(
% 1.27/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.27/0.52    inference(ennf_transformation,[],[f9])).
% 1.27/0.52  fof(f9,axiom,(
% 1.27/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).
% 1.27/0.52  fof(f128,plain,(
% 1.27/0.52    ( ! [X0,X1] : (v1_xboole_0(k7_relat_1(X1,k1_xboole_0)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 1.27/0.52    inference(resolution,[],[f127,f75])).
% 1.27/0.52  fof(f75,plain,(
% 1.27/0.52    ( ! [X0,X1] : (~v1_xboole_0(X1) | v1_xboole_0(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f44])).
% 1.27/0.52  fof(f44,plain,(
% 1.27/0.52    ! [X0,X1] : ((v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))) | ~v1_xboole_0(X1) | ~v1_relat_1(X0))),
% 1.27/0.52    inference(flattening,[],[f43])).
% 1.27/0.52  fof(f43,plain,(
% 1.27/0.52    ! [X0,X1] : ((v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))) | (~v1_xboole_0(X1) | ~v1_relat_1(X0)))),
% 1.27/0.52    inference(ennf_transformation,[],[f23])).
% 1.27/0.52  fof(f23,axiom,(
% 1.27/0.52    ! [X0,X1] : ((v1_xboole_0(X1) & v1_relat_1(X0)) => (v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))))),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc16_relat_1)).
% 1.27/0.52  fof(f127,plain,(
% 1.27/0.52    ( ! [X0] : (v1_xboole_0(k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.27/0.52    inference(subsumption_resolution,[],[f126,f93])).
% 1.27/0.52  fof(f93,plain,(
% 1.27/0.52    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.27/0.52    inference(resolution,[],[f74,f59])).
% 1.27/0.52  fof(f59,plain,(
% 1.27/0.52    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f7])).
% 1.27/0.52  fof(f7,axiom,(
% 1.27/0.52    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.27/0.52  fof(f74,plain,(
% 1.27/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f42])).
% 1.27/0.52  fof(f42,plain,(
% 1.27/0.52    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.27/0.52    inference(ennf_transformation,[],[f4])).
% 1.27/0.52  fof(f4,axiom,(
% 1.27/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.27/0.52  fof(f126,plain,(
% 1.27/0.52    ( ! [X0] : (v1_xboole_0(k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0) )),
% 1.27/0.52    inference(resolution,[],[f101,f65])).
% 1.27/0.52  fof(f65,plain,(
% 1.27/0.52    ( ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0) )),
% 1.27/0.52    inference(cnf_transformation,[],[f37])).
% 1.27/0.52  fof(f37,plain,(
% 1.27/0.52    ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0)),
% 1.27/0.52    inference(ennf_transformation,[],[f6])).
% 1.27/0.52  fof(f6,axiom,(
% 1.27/0.52    ! [X0] : (k1_xboole_0 != X0 => r2_xboole_0(k1_xboole_0,X0))),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_xboole_1)).
% 1.27/0.52  fof(f101,plain,(
% 1.27/0.52    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | v1_xboole_0(X0) | ~r1_xboole_0(X0,X1)) )),
% 1.27/0.52    inference(resolution,[],[f73,f77])).
% 1.27/0.52  fof(f77,plain,(
% 1.27/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f45])).
% 1.27/0.52  fof(f45,plain,(
% 1.27/0.52    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1))),
% 1.27/0.52    inference(ennf_transformation,[],[f32])).
% 1.27/0.52  fof(f32,plain,(
% 1.27/0.52    ! [X0,X1] : (r2_xboole_0(X0,X1) => (X0 != X1 & r1_tarski(X0,X1)))),
% 1.27/0.52    inference(unused_predicate_definition_removal,[],[f2])).
% 1.27/0.52  fof(f2,axiom,(
% 1.27/0.52    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 1.27/0.52  fof(f73,plain,(
% 1.27/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0) | v1_xboole_0(X1)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f41])).
% 1.27/0.52  fof(f41,plain,(
% 1.27/0.52    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.27/0.52    inference(flattening,[],[f40])).
% 1.27/0.52  fof(f40,plain,(
% 1.27/0.52    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.27/0.52    inference(ennf_transformation,[],[f8])).
% 1.27/0.52  fof(f8,axiom,(
% 1.27/0.52    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 1.27/0.52  fof(f211,plain,(
% 1.27/0.52    k1_xboole_0 != k7_relat_1(sK2,k1_xboole_0)),
% 1.27/0.52    inference(forward_demodulation,[],[f204,f104])).
% 1.27/0.52  fof(f104,plain,(
% 1.27/0.52    k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 1.27/0.52    inference(resolution,[],[f79,f53])).
% 1.27/0.52  fof(f53,plain,(
% 1.27/0.52    r1_xboole_0(sK0,sK1)),
% 1.27/0.52    inference(cnf_transformation,[],[f48])).
% 1.27/0.52  fof(f79,plain,(
% 1.27/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.27/0.52    inference(cnf_transformation,[],[f50])).
% 1.27/0.52  fof(f50,plain,(
% 1.27/0.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.27/0.52    inference(nnf_transformation,[],[f1])).
% 1.27/0.52  fof(f1,axiom,(
% 1.27/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.27/0.52  fof(f204,plain,(
% 1.27/0.52    k1_xboole_0 != k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),
% 1.27/0.52    inference(superposition,[],[f54,f202])).
% 1.27/0.52  fof(f202,plain,(
% 1.27/0.52    ( ! [X10,X9] : (k7_relat_1(k7_relat_1(sK2,X9),X10) = k7_relat_1(sK2,k3_xboole_0(X9,X10))) )),
% 1.27/0.52    inference(resolution,[],[f84,f52])).
% 1.27/0.52  fof(f84,plain,(
% 1.27/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 1.27/0.52    inference(cnf_transformation,[],[f46])).
% 1.27/0.52  fof(f46,plain,(
% 1.27/0.52    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.27/0.52    inference(ennf_transformation,[],[f25])).
% 1.27/0.52  fof(f25,axiom,(
% 1.27/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 1.27/0.52  fof(f54,plain,(
% 1.27/0.52    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 1.27/0.52    inference(cnf_transformation,[],[f48])).
% 1.27/0.52  % SZS output end Proof for theBenchmark
% 1.27/0.52  % (10217)------------------------------
% 1.27/0.52  % (10217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.52  % (10217)Termination reason: Refutation
% 1.27/0.52  
% 1.27/0.52  % (10217)Memory used [KB]: 6268
% 1.27/0.52  % (10217)Time elapsed: 0.102 s
% 1.27/0.52  % (10217)------------------------------
% 1.27/0.52  % (10217)------------------------------
% 1.27/0.52  % (10209)Success in time 0.163 s
%------------------------------------------------------------------------------
