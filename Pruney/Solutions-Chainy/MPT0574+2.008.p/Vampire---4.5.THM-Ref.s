%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:43 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   39 (  58 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :   11
%              Number of atoms          :   89 ( 150 expanded)
%              Number of equality atoms :   20 (  27 expanded)
%              Maximal formula depth    :    7 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f134,plain,(
    $false ),
    inference(subsumption_resolution,[],[f133,f19])).

fof(f19,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f14])).

% (6590)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

fof(f133,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f129,f18])).

fof(f18,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f129,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f93,f20])).

fof(f20,plain,(
    ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f93,plain,(
    ! [X14,X15,X16] :
      ( r1_tarski(k10_relat_1(X16,X14),k10_relat_1(X16,X15))
      | ~ v1_relat_1(X16)
      | ~ r1_tarski(X14,X15) ) ),
    inference(superposition,[],[f42,f65])).

fof(f65,plain,(
    ! [X6,X5] :
      ( k2_xboole_0(X6,X5) = X5
      | ~ r1_tarski(X6,X5) ) ),
    inference(superposition,[],[f55,f39])).

fof(f39,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f31,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f23,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X1,X0) ) ),
    inference(subsumption_resolution,[],[f51,f29])).

fof(f29,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f35,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f35,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_xboole_0(X1,X2),X1)
      | k2_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f26,f21])).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X6,X4,X5] :
      ( r1_tarski(k10_relat_1(X4,X5),k10_relat_1(X4,k2_xboole_0(X5,X6)))
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f21,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:22:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.36  ipcrm: permission denied for id (1226604547)
% 0.20/0.47  ipcrm: permission denied for id (1226637412)
% 0.46/0.64  % (6593)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.46/0.64  % (6584)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.46/0.65  % (6591)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.46/0.66  % (6609)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.46/0.66  % (6601)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.46/0.66  % (6594)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.46/0.66  % (6591)Refutation found. Thanks to Tanya!
% 0.46/0.66  % SZS status Theorem for theBenchmark
% 0.46/0.66  % (6610)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.46/0.66  % (6602)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.46/0.67  % (6599)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.46/0.67  % (6610)Refutation not found, incomplete strategy% (6610)------------------------------
% 0.46/0.67  % (6610)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.46/0.67  % (6589)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.46/0.67  % (6610)Termination reason: Refutation not found, incomplete strategy
% 0.46/0.67  
% 0.46/0.67  % (6610)Memory used [KB]: 10618
% 0.46/0.67  % (6610)Time elapsed: 0.101 s
% 0.46/0.67  % (6610)------------------------------
% 0.46/0.67  % (6610)------------------------------
% 0.46/0.67  % (6607)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.46/0.67  % (6582)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.46/0.67  % SZS output start Proof for theBenchmark
% 0.46/0.67  fof(f134,plain,(
% 0.46/0.67    $false),
% 0.46/0.67    inference(subsumption_resolution,[],[f133,f19])).
% 0.46/0.67  fof(f19,plain,(
% 0.46/0.67    r1_tarski(sK0,sK1)),
% 0.46/0.67    inference(cnf_transformation,[],[f15])).
% 0.46/0.67  fof(f15,plain,(
% 0.46/0.67    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.46/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f14])).
% 0.46/0.67  % (6590)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.46/0.67  fof(f14,plain,(
% 0.46/0.67    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.46/0.67    introduced(choice_axiom,[])).
% 0.46/0.67  fof(f10,plain,(
% 0.46/0.67    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.46/0.67    inference(flattening,[],[f9])).
% 0.46/0.67  fof(f9,plain,(
% 0.46/0.67    ? [X0,X1,X2] : ((~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.46/0.67    inference(ennf_transformation,[],[f8])).
% 0.46/0.67  fof(f8,negated_conjecture,(
% 0.46/0.67    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.46/0.67    inference(negated_conjecture,[],[f7])).
% 0.46/0.67  fof(f7,conjecture,(
% 0.46/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.46/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).
% 0.46/0.67  fof(f133,plain,(
% 0.46/0.67    ~r1_tarski(sK0,sK1)),
% 0.46/0.67    inference(subsumption_resolution,[],[f129,f18])).
% 0.46/0.67  fof(f18,plain,(
% 0.46/0.67    v1_relat_1(sK2)),
% 0.46/0.67    inference(cnf_transformation,[],[f15])).
% 0.46/0.67  fof(f129,plain,(
% 0.46/0.67    ~v1_relat_1(sK2) | ~r1_tarski(sK0,sK1)),
% 0.46/0.67    inference(resolution,[],[f93,f20])).
% 0.46/0.67  fof(f20,plain,(
% 0.46/0.67    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.46/0.67    inference(cnf_transformation,[],[f15])).
% 0.46/0.67  fof(f93,plain,(
% 0.46/0.67    ( ! [X14,X15,X16] : (r1_tarski(k10_relat_1(X16,X14),k10_relat_1(X16,X15)) | ~v1_relat_1(X16) | ~r1_tarski(X14,X15)) )),
% 0.46/0.67    inference(superposition,[],[f42,f65])).
% 0.46/0.67  fof(f65,plain,(
% 0.46/0.67    ( ! [X6,X5] : (k2_xboole_0(X6,X5) = X5 | ~r1_tarski(X6,X5)) )),
% 0.46/0.67    inference(superposition,[],[f55,f39])).
% 0.46/0.67  fof(f39,plain,(
% 0.46/0.67    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 0.46/0.67    inference(superposition,[],[f31,f23])).
% 0.46/0.67  fof(f23,plain,(
% 0.46/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.46/0.67    inference(cnf_transformation,[],[f5])).
% 0.46/0.67  fof(f5,axiom,(
% 0.46/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.46/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.46/0.67  fof(f31,plain,(
% 0.46/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))) )),
% 0.46/0.67    inference(superposition,[],[f23,f22])).
% 0.46/0.67  fof(f22,plain,(
% 0.46/0.67    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.46/0.67    inference(cnf_transformation,[],[f4])).
% 0.46/0.67  fof(f4,axiom,(
% 0.46/0.67    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.46/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.46/0.67  fof(f55,plain,(
% 0.46/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X0 | ~r1_tarski(X1,X0)) )),
% 0.46/0.67    inference(subsumption_resolution,[],[f51,f29])).
% 0.46/0.67  fof(f29,plain,(
% 0.46/0.67    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.46/0.67    inference(equality_resolution,[],[f25])).
% 0.46/0.67  fof(f25,plain,(
% 0.46/0.67    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.46/0.67    inference(cnf_transformation,[],[f17])).
% 0.46/0.67  fof(f17,plain,(
% 0.46/0.67    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.46/0.67    inference(flattening,[],[f16])).
% 0.46/0.67  fof(f16,plain,(
% 0.46/0.67    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.46/0.67    inference(nnf_transformation,[],[f1])).
% 0.46/0.67  fof(f1,axiom,(
% 0.46/0.67    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.46/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.46/0.67  fof(f51,plain,(
% 0.46/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0)) )),
% 0.46/0.67    inference(resolution,[],[f35,f28])).
% 0.46/0.67  fof(f28,plain,(
% 0.46/0.67    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.46/0.67    inference(cnf_transformation,[],[f13])).
% 0.46/0.67  fof(f13,plain,(
% 0.46/0.67    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.46/0.67    inference(flattening,[],[f12])).
% 0.46/0.67  fof(f12,plain,(
% 0.46/0.67    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.46/0.67    inference(ennf_transformation,[],[f3])).
% 0.46/0.67  fof(f3,axiom,(
% 0.46/0.67    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.46/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.46/0.67  fof(f35,plain,(
% 0.46/0.67    ( ! [X2,X1] : (~r1_tarski(k2_xboole_0(X1,X2),X1) | k2_xboole_0(X1,X2) = X1) )),
% 0.46/0.67    inference(resolution,[],[f26,f21])).
% 0.46/0.67  fof(f21,plain,(
% 0.46/0.67    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.46/0.67    inference(cnf_transformation,[],[f2])).
% 0.46/0.67  fof(f2,axiom,(
% 0.46/0.67    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.46/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.46/0.67  fof(f26,plain,(
% 0.46/0.67    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.46/0.67    inference(cnf_transformation,[],[f17])).
% 0.46/0.67  fof(f42,plain,(
% 0.46/0.67    ( ! [X6,X4,X5] : (r1_tarski(k10_relat_1(X4,X5),k10_relat_1(X4,k2_xboole_0(X5,X6))) | ~v1_relat_1(X4)) )),
% 0.46/0.67    inference(superposition,[],[f21,f27])).
% 0.46/0.67  fof(f27,plain,(
% 0.46/0.67    ( ! [X2,X0,X1] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.46/0.67    inference(cnf_transformation,[],[f11])).
% 0.46/0.67  fof(f11,plain,(
% 0.46/0.67    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.46/0.67    inference(ennf_transformation,[],[f6])).
% 0.46/0.67  fof(f6,axiom,(
% 0.46/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.46/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).
% 0.46/0.67  % SZS output end Proof for theBenchmark
% 0.46/0.67  % (6591)------------------------------
% 0.46/0.67  % (6591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.46/0.67  % (6591)Termination reason: Refutation
% 0.46/0.67  
% 0.46/0.67  % (6591)Memory used [KB]: 1791
% 0.46/0.67  % (6591)Time elapsed: 0.101 s
% 0.46/0.67  % (6591)------------------------------
% 0.46/0.67  % (6591)------------------------------
% 0.46/0.67  % (6592)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.46/0.67  % (6447)Success in time 0.318 s
%------------------------------------------------------------------------------
