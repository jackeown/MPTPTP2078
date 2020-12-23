%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:10 EST 2020

% Result     : Theorem 3.08s
% Output     : Refutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 165 expanded)
%              Number of leaves         :   12 (  48 expanded)
%              Depth                    :   18
%              Number of atoms          :  155 ( 538 expanded)
%              Number of equality atoms :   19 (  39 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2778,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2777,f57])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2777,plain,(
    ~ r1_tarski(k3_relat_1(sK1),k3_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f2768,f333])).

fof(f333,plain,(
    k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f321,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f321,plain,(
    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(superposition,[],[f184,f67])).

fof(f67,plain,(
    k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(resolution,[],[f41,f44])).

fof(f44,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f41,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
          & r1_tarski(sK0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
        & r1_tarski(sK0,X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(f184,plain,(
    ! [X0] : r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),X0)) ),
    inference(superposition,[],[f99,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f99,plain,(
    ! [X0] : r1_tarski(k1_relat_1(sK0),k2_xboole_0(X0,k1_relat_1(sK1))) ),
    inference(resolution,[],[f75,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f75,plain,(
    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f74,f40])).

fof(f40,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f74,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f68,f41])).

fof(f68,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f42,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f42,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f2768,plain,(
    ~ r1_tarski(k2_xboole_0(k1_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1)) ),
    inference(resolution,[],[f2610,f351])).

fof(f351,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k4_xboole_0(k3_relat_1(sK0),X2),X3)
      | ~ r1_tarski(k2_xboole_0(X2,X3),k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f133,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f133,plain,(
    ! [X2] :
      ( ~ r1_tarski(k3_relat_1(sK0),X2)
      | ~ r1_tarski(X2,k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f78,f52])).

fof(f78,plain,(
    ! [X0] : ~ r1_tarski(k2_xboole_0(k3_relat_1(sK0),X0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f43,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f43,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f2610,plain,(
    r1_tarski(k4_xboole_0(k3_relat_1(sK0),k1_relat_1(sK0)),k3_relat_1(sK1)) ),
    inference(resolution,[],[f2398,f633])).

fof(f633,plain,(
    r1_tarski(k4_xboole_0(k3_relat_1(sK0),k1_relat_1(sK0)),k2_relat_1(sK0)) ),
    inference(resolution,[],[f145,f57])).

fof(f145,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k3_relat_1(sK0))
      | r1_tarski(k4_xboole_0(X2,k1_relat_1(sK0)),k2_relat_1(sK0)) ) ),
    inference(superposition,[],[f50,f62])).

fof(f62,plain,(
    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(resolution,[],[f40,f44])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f2398,plain,(
    ! [X4] :
      ( ~ r1_tarski(X4,k2_relat_1(sK0))
      | r1_tarski(X4,k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f51,f1882])).

fof(f1882,plain,(
    k3_relat_1(sK1) = k2_xboole_0(k3_relat_1(sK1),k2_relat_1(sK0)) ),
    inference(superposition,[],[f206,f53])).

fof(f206,plain,(
    k3_relat_1(sK1) = k2_xboole_0(k2_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f201,f52])).

fof(f201,plain,(
    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f196,f41])).

fof(f196,plain,
    ( r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f105,f44])).

fof(f105,plain,(
    ! [X0] : r1_tarski(k2_relat_1(sK0),k2_xboole_0(X0,k2_relat_1(sK1))) ),
    inference(resolution,[],[f77,f51])).

fof(f77,plain,(
    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f76,f40])).

fof(f76,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f69,f41])).

fof(f69,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f42,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:18:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (6101)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (6118)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (6109)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (6122)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (6102)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (6103)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (6104)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (6123)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (6100)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (6114)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (6120)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (6128)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (6099)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (6124)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (6106)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (6130)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (6111)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (6117)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (6105)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.55  % (6111)Refutation not found, incomplete strategy% (6111)------------------------------
% 0.20/0.55  % (6111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (6126)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  % (6111)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (6111)Memory used [KB]: 10618
% 0.20/0.55  % (6111)Time elapsed: 0.129 s
% 0.20/0.55  % (6111)------------------------------
% 0.20/0.55  % (6111)------------------------------
% 0.20/0.55  % (6129)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.56  % (6119)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.56  % (6125)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.56  % (6131)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.56  % (6124)Refutation not found, incomplete strategy% (6124)------------------------------
% 0.20/0.56  % (6124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (6124)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (6124)Memory used [KB]: 10746
% 0.20/0.56  % (6124)Time elapsed: 0.155 s
% 0.20/0.56  % (6124)------------------------------
% 0.20/0.56  % (6124)------------------------------
% 1.55/0.57  % (6121)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.55/0.57  % (6115)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.55/0.57  % (6112)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.55/0.57  % (6112)Refutation not found, incomplete strategy% (6112)------------------------------
% 1.55/0.57  % (6112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (6112)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.57  
% 1.55/0.57  % (6112)Memory used [KB]: 10618
% 1.55/0.57  % (6112)Time elapsed: 0.159 s
% 1.55/0.57  % (6112)------------------------------
% 1.55/0.57  % (6112)------------------------------
% 1.55/0.57  % (6113)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.55/0.57  % (6107)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.55/0.58  % (6127)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 2.13/0.66  % (6172)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.13/0.69  % (6173)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.13/0.70  % (6174)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.08/0.83  % (6104)Time limit reached!
% 3.08/0.83  % (6104)------------------------------
% 3.08/0.83  % (6104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.08/0.83  % (6104)Termination reason: Time limit
% 3.08/0.83  
% 3.08/0.83  % (6104)Memory used [KB]: 9338
% 3.08/0.83  % (6104)Time elapsed: 0.415 s
% 3.08/0.83  % (6104)------------------------------
% 3.08/0.83  % (6104)------------------------------
% 3.08/0.85  % (6172)Refutation found. Thanks to Tanya!
% 3.08/0.85  % SZS status Theorem for theBenchmark
% 3.08/0.85  % SZS output start Proof for theBenchmark
% 3.08/0.85  fof(f2778,plain,(
% 3.08/0.85    $false),
% 3.08/0.85    inference(subsumption_resolution,[],[f2777,f57])).
% 3.08/0.85  fof(f57,plain,(
% 3.08/0.85    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.08/0.85    inference(equality_resolution,[],[f45])).
% 3.08/0.85  fof(f45,plain,(
% 3.08/0.85    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.08/0.85    inference(cnf_transformation,[],[f39])).
% 3.08/0.85  fof(f39,plain,(
% 3.08/0.85    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.08/0.85    inference(flattening,[],[f38])).
% 3.08/0.85  fof(f38,plain,(
% 3.08/0.85    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.08/0.85    inference(nnf_transformation,[],[f4])).
% 3.08/0.85  fof(f4,axiom,(
% 3.08/0.85    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.08/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.08/0.85  fof(f2777,plain,(
% 3.08/0.85    ~r1_tarski(k3_relat_1(sK1),k3_relat_1(sK1))),
% 3.08/0.85    inference(forward_demodulation,[],[f2768,f333])).
% 3.08/0.85  fof(f333,plain,(
% 3.08/0.85    k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK0),k3_relat_1(sK1))),
% 3.08/0.85    inference(resolution,[],[f321,f52])).
% 3.08/0.85  fof(f52,plain,(
% 3.08/0.85    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.08/0.85    inference(cnf_transformation,[],[f32])).
% 3.08/0.85  fof(f32,plain,(
% 3.08/0.85    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.08/0.85    inference(ennf_transformation,[],[f7])).
% 3.08/0.85  fof(f7,axiom,(
% 3.08/0.85    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.08/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 3.08/0.85  fof(f321,plain,(
% 3.08/0.85    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 3.08/0.85    inference(superposition,[],[f184,f67])).
% 3.08/0.85  fof(f67,plain,(
% 3.08/0.85    k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1))),
% 3.08/0.85    inference(resolution,[],[f41,f44])).
% 3.08/0.85  fof(f44,plain,(
% 3.08/0.85    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.08/0.85    inference(cnf_transformation,[],[f27])).
% 3.08/0.85  fof(f27,plain,(
% 3.08/0.85    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.08/0.85    inference(ennf_transformation,[],[f20])).
% 3.08/0.85  fof(f20,axiom,(
% 3.08/0.85    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 3.08/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 3.08/0.85  fof(f41,plain,(
% 3.08/0.85    v1_relat_1(sK1)),
% 3.08/0.85    inference(cnf_transformation,[],[f37])).
% 3.08/0.85  fof(f37,plain,(
% 3.08/0.85    (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 3.08/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f36,f35])).
% 3.08/0.85  fof(f35,plain,(
% 3.08/0.85    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 3.08/0.85    introduced(choice_axiom,[])).
% 3.08/0.85  fof(f36,plain,(
% 3.08/0.85    ? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1))),
% 3.08/0.85    introduced(choice_axiom,[])).
% 3.08/0.85  fof(f26,plain,(
% 3.08/0.85    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.08/0.85    inference(flattening,[],[f25])).
% 3.08/0.85  fof(f25,plain,(
% 3.08/0.85    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.08/0.85    inference(ennf_transformation,[],[f24])).
% 3.08/0.85  fof(f24,negated_conjecture,(
% 3.08/0.85    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 3.08/0.85    inference(negated_conjecture,[],[f23])).
% 3.08/0.85  fof(f23,conjecture,(
% 3.08/0.85    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 3.08/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).
% 3.08/0.85  fof(f184,plain,(
% 3.08/0.85    ( ! [X0] : (r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),X0))) )),
% 3.08/0.85    inference(superposition,[],[f99,f53])).
% 3.08/0.85  fof(f53,plain,(
% 3.08/0.85    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.08/0.85    inference(cnf_transformation,[],[f1])).
% 3.08/0.85  fof(f1,axiom,(
% 3.08/0.85    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.08/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 3.08/0.85  fof(f99,plain,(
% 3.08/0.85    ( ! [X0] : (r1_tarski(k1_relat_1(sK0),k2_xboole_0(X0,k1_relat_1(sK1)))) )),
% 3.08/0.85    inference(resolution,[],[f75,f51])).
% 3.08/0.85  fof(f51,plain,(
% 3.08/0.85    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.08/0.85    inference(cnf_transformation,[],[f31])).
% 3.08/0.85  fof(f31,plain,(
% 3.08/0.85    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.08/0.85    inference(ennf_transformation,[],[f5])).
% 3.08/0.85  fof(f5,axiom,(
% 3.08/0.85    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 3.08/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 3.08/0.85  fof(f75,plain,(
% 3.08/0.85    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))),
% 3.08/0.85    inference(subsumption_resolution,[],[f74,f40])).
% 3.08/0.85  fof(f40,plain,(
% 3.08/0.85    v1_relat_1(sK0)),
% 3.08/0.85    inference(cnf_transformation,[],[f37])).
% 3.08/0.85  fof(f74,plain,(
% 3.08/0.85    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) | ~v1_relat_1(sK0)),
% 3.08/0.85    inference(subsumption_resolution,[],[f68,f41])).
% 3.08/0.85  fof(f68,plain,(
% 3.08/0.85    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 3.08/0.85    inference(resolution,[],[f42,f54])).
% 3.08/0.85  fof(f54,plain,(
% 3.08/0.85    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.08/0.85    inference(cnf_transformation,[],[f34])).
% 3.08/0.85  fof(f34,plain,(
% 3.08/0.85    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.08/0.85    inference(flattening,[],[f33])).
% 3.08/0.85  fof(f33,plain,(
% 3.08/0.85    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.08/0.85    inference(ennf_transformation,[],[f22])).
% 3.08/0.85  fof(f22,axiom,(
% 3.08/0.85    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 3.08/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 3.08/0.85  fof(f42,plain,(
% 3.08/0.85    r1_tarski(sK0,sK1)),
% 3.08/0.85    inference(cnf_transformation,[],[f37])).
% 3.08/0.85  fof(f2768,plain,(
% 3.08/0.85    ~r1_tarski(k2_xboole_0(k1_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1))),
% 3.08/0.85    inference(resolution,[],[f2610,f351])).
% 3.08/0.85  fof(f351,plain,(
% 3.08/0.85    ( ! [X2,X3] : (~r1_tarski(k4_xboole_0(k3_relat_1(sK0),X2),X3) | ~r1_tarski(k2_xboole_0(X2,X3),k3_relat_1(sK1))) )),
% 3.08/0.85    inference(resolution,[],[f133,f48])).
% 3.08/0.85  fof(f48,plain,(
% 3.08/0.85    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 3.08/0.85    inference(cnf_transformation,[],[f28])).
% 3.08/0.85  fof(f28,plain,(
% 3.08/0.85    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.08/0.85    inference(ennf_transformation,[],[f13])).
% 3.08/0.85  fof(f13,axiom,(
% 3.08/0.85    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.08/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 3.08/0.85  fof(f133,plain,(
% 3.08/0.85    ( ! [X2] : (~r1_tarski(k3_relat_1(sK0),X2) | ~r1_tarski(X2,k3_relat_1(sK1))) )),
% 3.08/0.85    inference(superposition,[],[f78,f52])).
% 3.08/0.85  fof(f78,plain,(
% 3.08/0.85    ( ! [X0] : (~r1_tarski(k2_xboole_0(k3_relat_1(sK0),X0),k3_relat_1(sK1))) )),
% 3.08/0.85    inference(resolution,[],[f43,f49])).
% 3.08/0.85  fof(f49,plain,(
% 3.08/0.85    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 3.08/0.85    inference(cnf_transformation,[],[f29])).
% 3.08/0.85  fof(f29,plain,(
% 3.08/0.85    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 3.08/0.85    inference(ennf_transformation,[],[f6])).
% 3.08/0.85  fof(f6,axiom,(
% 3.08/0.85    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 3.08/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 3.08/0.85  fof(f43,plain,(
% 3.08/0.85    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 3.08/0.85    inference(cnf_transformation,[],[f37])).
% 3.08/0.85  fof(f2610,plain,(
% 3.08/0.85    r1_tarski(k4_xboole_0(k3_relat_1(sK0),k1_relat_1(sK0)),k3_relat_1(sK1))),
% 3.08/0.85    inference(resolution,[],[f2398,f633])).
% 3.08/0.85  fof(f633,plain,(
% 3.08/0.85    r1_tarski(k4_xboole_0(k3_relat_1(sK0),k1_relat_1(sK0)),k2_relat_1(sK0))),
% 3.08/0.85    inference(resolution,[],[f145,f57])).
% 3.08/0.85  fof(f145,plain,(
% 3.08/0.85    ( ! [X2] : (~r1_tarski(X2,k3_relat_1(sK0)) | r1_tarski(k4_xboole_0(X2,k1_relat_1(sK0)),k2_relat_1(sK0))) )),
% 3.08/0.85    inference(superposition,[],[f50,f62])).
% 3.08/0.85  fof(f62,plain,(
% 3.08/0.85    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))),
% 3.08/0.85    inference(resolution,[],[f40,f44])).
% 3.08/0.85  fof(f50,plain,(
% 3.08/0.85    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 3.08/0.85    inference(cnf_transformation,[],[f30])).
% 3.08/0.85  fof(f30,plain,(
% 3.08/0.85    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.08/0.85    inference(ennf_transformation,[],[f12])).
% 3.08/0.85  fof(f12,axiom,(
% 3.08/0.85    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.08/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 3.08/0.85  fof(f2398,plain,(
% 3.08/0.85    ( ! [X4] : (~r1_tarski(X4,k2_relat_1(sK0)) | r1_tarski(X4,k3_relat_1(sK1))) )),
% 3.08/0.85    inference(superposition,[],[f51,f1882])).
% 3.08/0.85  fof(f1882,plain,(
% 3.08/0.85    k3_relat_1(sK1) = k2_xboole_0(k3_relat_1(sK1),k2_relat_1(sK0))),
% 3.08/0.85    inference(superposition,[],[f206,f53])).
% 3.08/0.85  fof(f206,plain,(
% 3.08/0.85    k3_relat_1(sK1) = k2_xboole_0(k2_relat_1(sK0),k3_relat_1(sK1))),
% 3.08/0.85    inference(resolution,[],[f201,f52])).
% 3.08/0.85  fof(f201,plain,(
% 3.08/0.85    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))),
% 3.08/0.85    inference(subsumption_resolution,[],[f196,f41])).
% 3.08/0.85  fof(f196,plain,(
% 3.08/0.85    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 3.08/0.85    inference(superposition,[],[f105,f44])).
% 3.08/0.85  fof(f105,plain,(
% 3.08/0.85    ( ! [X0] : (r1_tarski(k2_relat_1(sK0),k2_xboole_0(X0,k2_relat_1(sK1)))) )),
% 3.08/0.85    inference(resolution,[],[f77,f51])).
% 3.08/0.85  fof(f77,plain,(
% 3.08/0.85    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 3.08/0.85    inference(subsumption_resolution,[],[f76,f40])).
% 3.08/0.85  fof(f76,plain,(
% 3.08/0.85    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | ~v1_relat_1(sK0)),
% 3.08/0.85    inference(subsumption_resolution,[],[f69,f41])).
% 3.08/0.85  fof(f69,plain,(
% 3.08/0.85    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 3.08/0.85    inference(resolution,[],[f42,f55])).
% 3.08/0.85  fof(f55,plain,(
% 3.08/0.85    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.08/0.85    inference(cnf_transformation,[],[f34])).
% 3.08/0.85  % SZS output end Proof for theBenchmark
% 3.08/0.85  % (6172)------------------------------
% 3.08/0.85  % (6172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.08/0.85  % (6172)Termination reason: Refutation
% 3.08/0.85  
% 3.08/0.85  % (6172)Memory used [KB]: 8571
% 3.08/0.85  % (6172)Time elapsed: 0.221 s
% 3.08/0.85  % (6172)------------------------------
% 3.08/0.85  % (6172)------------------------------
% 3.08/0.85  % (6093)Success in time 0.493 s
%------------------------------------------------------------------------------
