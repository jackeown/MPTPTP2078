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
% DateTime   : Thu Dec  3 12:54:45 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   48 (  83 expanded)
%              Number of leaves         :   10 (  21 expanded)
%              Depth                    :   13
%              Number of atoms          :  126 ( 236 expanded)
%              Number of equality atoms :   24 (  26 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f69,plain,(
    $false ),
    inference(subsumption_resolution,[],[f68,f23])).

fof(f23,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).

fof(f68,plain,(
    ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f67,f24])).

fof(f24,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f67,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f66,f51])).

fof(f51,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f49,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f49,plain,(
    ~ r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f48,f28])).

fof(f28,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f48,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f47,f27])).

fof(f27,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f47,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f44,f23])).

fof(f44,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f25,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

fof(f25,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f66,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f62,f38])).

fof(f38,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f62,plain,
    ( ~ r1_tarski(k1_tarski(k1_funct_1(sK1,sK0)),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f43,f56])).

% (8826)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
fof(f56,plain,(
    ! [X4,X3] :
      ( k1_tarski(k1_funct_1(X3,X4)) = k9_relat_1(X3,k1_tarski(X4))
      | ~ r2_hidden(X4,k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(forward_demodulation,[],[f55,f29])).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f55,plain,(
    ! [X4,X3] :
      ( k1_tarski(k1_funct_1(X3,X4)) = k9_relat_1(X3,k2_tarski(X4,X4))
      | ~ r2_hidden(X4,k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f52])).

fof(f52,plain,(
    ! [X4,X3] :
      ( k1_tarski(k1_funct_1(X3,X4)) = k9_relat_1(X3,k2_tarski(X4,X4))
      | ~ r2_hidden(X4,k1_relat_1(X3))
      | ~ r2_hidden(X4,k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f37,f29])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).

fof(f43,plain,(
    ~ r1_tarski(k9_relat_1(sK1,k1_tarski(sK0)),k1_tarski(k1_funct_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f42,f23])).

fof(f42,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k1_tarski(sK0)),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f25,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:53:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.55  % (8825)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.51/0.56  % (8833)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.51/0.56  % (8834)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.51/0.57  % (8842)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.51/0.57  % (8830)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.51/0.58  % (8827)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.51/0.58  % (8834)Refutation found. Thanks to Tanya!
% 1.51/0.58  % SZS status Theorem for theBenchmark
% 1.51/0.58  % SZS output start Proof for theBenchmark
% 1.51/0.58  fof(f69,plain,(
% 1.51/0.58    $false),
% 1.51/0.58    inference(subsumption_resolution,[],[f68,f23])).
% 1.51/0.58  fof(f23,plain,(
% 1.51/0.58    v1_relat_1(sK1)),
% 1.51/0.58    inference(cnf_transformation,[],[f20])).
% 1.51/0.58  fof(f20,plain,(
% 1.51/0.58    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.51/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f19])).
% 1.51/0.58  fof(f19,plain,(
% 1.51/0.58    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.51/0.58    introduced(choice_axiom,[])).
% 1.51/0.58  fof(f13,plain,(
% 1.51/0.58    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.51/0.58    inference(flattening,[],[f12])).
% 1.51/0.58  fof(f12,plain,(
% 1.51/0.58    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.51/0.58    inference(ennf_transformation,[],[f11])).
% 1.51/0.58  fof(f11,negated_conjecture,(
% 1.51/0.58    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 1.51/0.58    inference(negated_conjecture,[],[f10])).
% 1.51/0.58  fof(f10,conjecture,(
% 1.51/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 1.51/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).
% 1.51/0.58  fof(f68,plain,(
% 1.51/0.58    ~v1_relat_1(sK1)),
% 1.51/0.58    inference(subsumption_resolution,[],[f67,f24])).
% 1.51/0.58  fof(f24,plain,(
% 1.51/0.58    v1_funct_1(sK1)),
% 1.51/0.58    inference(cnf_transformation,[],[f20])).
% 1.51/0.58  fof(f67,plain,(
% 1.51/0.58    ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.51/0.58    inference(subsumption_resolution,[],[f66,f51])).
% 1.51/0.58  fof(f51,plain,(
% 1.51/0.58    r2_hidden(sK0,k1_relat_1(sK1))),
% 1.51/0.58    inference(resolution,[],[f49,f33])).
% 1.51/0.58  fof(f33,plain,(
% 1.51/0.58    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.51/0.58    inference(cnf_transformation,[],[f16])).
% 1.51/0.58  fof(f16,plain,(
% 1.51/0.58    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.51/0.58    inference(ennf_transformation,[],[f5])).
% 1.51/0.58  fof(f5,axiom,(
% 1.51/0.58    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.51/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.51/0.58  fof(f49,plain,(
% 1.51/0.58    ~r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1))),
% 1.51/0.58    inference(subsumption_resolution,[],[f48,f28])).
% 1.51/0.58  fof(f28,plain,(
% 1.51/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.51/0.58    inference(cnf_transformation,[],[f2])).
% 1.51/0.58  fof(f2,axiom,(
% 1.51/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.51/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.51/0.58  fof(f48,plain,(
% 1.51/0.58    ~r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(sK1,sK0))) | ~r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1))),
% 1.51/0.58    inference(forward_demodulation,[],[f47,f27])).
% 1.51/0.58  fof(f27,plain,(
% 1.51/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.51/0.58    inference(cnf_transformation,[],[f8])).
% 1.51/0.58  fof(f8,axiom,(
% 1.51/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.51/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.51/0.58  fof(f47,plain,(
% 1.51/0.58    ~r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1(sK1,sK0))) | ~r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1))),
% 1.51/0.58    inference(subsumption_resolution,[],[f44,f23])).
% 1.51/0.58  fof(f44,plain,(
% 1.51/0.58    ~r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1(sK1,sK0))) | ~r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 1.51/0.58    inference(superposition,[],[f25,f30])).
% 1.64/0.58  fof(f30,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f14])).
% 1.64/0.58  fof(f14,plain,(
% 1.64/0.58    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.64/0.58    inference(ennf_transformation,[],[f7])).
% 1.64/0.58  fof(f7,axiom,(
% 1.64/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).
% 1.64/0.58  fof(f25,plain,(
% 1.64/0.58    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),
% 1.64/0.58    inference(cnf_transformation,[],[f20])).
% 1.64/0.58  fof(f66,plain,(
% 1.64/0.58    ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.64/0.58    inference(subsumption_resolution,[],[f62,f38])).
% 1.64/0.58  fof(f38,plain,(
% 1.64/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.64/0.58    inference(equality_resolution,[],[f35])).
% 1.64/0.58  fof(f35,plain,(
% 1.64/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.64/0.58    inference(cnf_transformation,[],[f22])).
% 1.64/0.58  fof(f22,plain,(
% 1.64/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.64/0.58    inference(flattening,[],[f21])).
% 1.64/0.58  fof(f21,plain,(
% 1.64/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.64/0.58    inference(nnf_transformation,[],[f1])).
% 1.64/0.58  fof(f1,axiom,(
% 1.64/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.64/0.58  fof(f62,plain,(
% 1.64/0.58    ~r1_tarski(k1_tarski(k1_funct_1(sK1,sK0)),k1_tarski(k1_funct_1(sK1,sK0))) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.64/0.58    inference(superposition,[],[f43,f56])).
% 1.64/0.58  % (8826)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.64/0.58  fof(f56,plain,(
% 1.64/0.58    ( ! [X4,X3] : (k1_tarski(k1_funct_1(X3,X4)) = k9_relat_1(X3,k1_tarski(X4)) | ~r2_hidden(X4,k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 1.64/0.58    inference(forward_demodulation,[],[f55,f29])).
% 1.64/0.58  fof(f29,plain,(
% 1.64/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f3])).
% 1.64/0.58  fof(f3,axiom,(
% 1.64/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.64/0.58  fof(f55,plain,(
% 1.64/0.58    ( ! [X4,X3] : (k1_tarski(k1_funct_1(X3,X4)) = k9_relat_1(X3,k2_tarski(X4,X4)) | ~r2_hidden(X4,k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 1.64/0.58    inference(duplicate_literal_removal,[],[f52])).
% 1.64/0.58  fof(f52,plain,(
% 1.64/0.58    ( ! [X4,X3] : (k1_tarski(k1_funct_1(X3,X4)) = k9_relat_1(X3,k2_tarski(X4,X4)) | ~r2_hidden(X4,k1_relat_1(X3)) | ~r2_hidden(X4,k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 1.64/0.58    inference(superposition,[],[f37,f29])).
% 1.64/0.58  fof(f37,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f18])).
% 1.64/0.58  fof(f18,plain,(
% 1.64/0.58    ! [X0,X1,X2] : (k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.64/0.58    inference(flattening,[],[f17])).
% 1.64/0.58  fof(f17,plain,(
% 1.64/0.58    ! [X0,X1,X2] : ((k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | (~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.64/0.58    inference(ennf_transformation,[],[f9])).
% 1.64/0.58  fof(f9,axiom,(
% 1.64/0.58    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X1,k1_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).
% 1.64/0.58  fof(f43,plain,(
% 1.64/0.58    ~r1_tarski(k9_relat_1(sK1,k1_tarski(sK0)),k1_tarski(k1_funct_1(sK1,sK0)))),
% 1.64/0.58    inference(subsumption_resolution,[],[f42,f23])).
% 1.64/0.58  fof(f42,plain,(
% 1.64/0.58    ~r1_tarski(k9_relat_1(sK1,k1_tarski(sK0)),k1_tarski(k1_funct_1(sK1,sK0))) | ~v1_relat_1(sK1)),
% 1.64/0.58    inference(superposition,[],[f25,f32])).
% 1.64/0.58  fof(f32,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f15])).
% 1.64/0.58  fof(f15,plain,(
% 1.64/0.58    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.64/0.58    inference(ennf_transformation,[],[f6])).
% 1.64/0.58  fof(f6,axiom,(
% 1.64/0.58    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.64/0.58  % SZS output end Proof for theBenchmark
% 1.64/0.58  % (8834)------------------------------
% 1.64/0.58  % (8834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.58  % (8834)Termination reason: Refutation
% 1.64/0.58  
% 1.64/0.58  % (8834)Memory used [KB]: 1663
% 1.64/0.58  % (8834)Time elapsed: 0.151 s
% 1.64/0.58  % (8834)------------------------------
% 1.64/0.58  % (8834)------------------------------
% 1.64/0.58  % (8824)Success in time 0.216 s
%------------------------------------------------------------------------------
