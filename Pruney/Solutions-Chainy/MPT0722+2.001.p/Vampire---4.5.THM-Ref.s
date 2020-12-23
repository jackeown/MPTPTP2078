%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 100 expanded)
%              Number of leaves         :    7 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  130 ( 462 expanded)
%              Number of equality atoms :   27 (  99 expanded)
%              Maximal formula depth    :    7 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f54,plain,(
    $false ),
    inference(subsumption_resolution,[],[f53,f43])).

fof(f43,plain,(
    sK1 = k10_relat_1(sK0,k9_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f40,f23])).

fof(f23,plain,(
    r1_tarski(sK1,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1))
    & r1_tarski(sK1,k1_relat_1(sK0))
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1
            & r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,X1)) != X1
          & r1_tarski(X1,k1_relat_1(sK0))
          & v2_funct_1(sK0) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,X1)) != X1
        & r1_tarski(X1,k1_relat_1(sK0))
        & v2_funct_1(sK0) )
   => ( sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1))
      & r1_tarski(sK1,k1_relat_1(sK0))
      & v2_funct_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1
          & r1_tarski(X1,k1_relat_1(X0))
          & v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1
          & r1_tarski(X1,k1_relat_1(X0))
          & v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( r1_tarski(X1,k1_relat_1(X0))
              & v2_funct_1(X0) )
           => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
         => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

fof(f40,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK0))
      | k10_relat_1(sK0,k9_relat_1(sK0,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f36,f39])).

fof(f39,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK0,k9_relat_1(sK0,X0)),X0) ),
    inference(subsumption_resolution,[],[f38,f20])).

fof(f20,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK0,k9_relat_1(sK0,X0)),X0)
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f37,f21])).

fof(f21,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK0,k9_relat_1(sK0,X0)),X0)
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f26,f22])).

fof(f22,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(f36,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK0))
      | ~ r1_tarski(k10_relat_1(sK0,k9_relat_1(sK0,X0)),X0)
      | k10_relat_1(sK0,k9_relat_1(sK0,X0)) = X0 ) ),
    inference(resolution,[],[f35,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

fof(f35,plain,(
    ! [X0] :
      ( r1_tarski(X0,k10_relat_1(sK0,k9_relat_1(sK0,X0)))
      | ~ r1_tarski(X0,k1_relat_1(sK0)) ) ),
    inference(resolution,[],[f25,f20])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f53,plain,(
    sK1 != k10_relat_1(sK0,k9_relat_1(sK0,sK1)) ),
    inference(superposition,[],[f24,f52])).

fof(f52,plain,(
    ! [X0] : k10_relat_1(sK0,X0) = k9_relat_1(k2_funct_1(sK0),X0) ),
    inference(subsumption_resolution,[],[f51,f20])).

fof(f51,plain,(
    ! [X0] :
      ( k10_relat_1(sK0,X0) = k9_relat_1(k2_funct_1(sK0),X0)
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f50,f21])).

fof(f50,plain,(
    ! [X0] :
      ( k10_relat_1(sK0,X0) = k9_relat_1(k2_funct_1(sK0),X0)
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f27,f22])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f24,plain,(
    sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:21:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (3814)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.45  % (3814)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(subsumption_resolution,[],[f53,f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    sK1 = k10_relat_1(sK0,k9_relat_1(sK0,sK1))),
% 0.20/0.47    inference(resolution,[],[f40,f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    r1_tarski(sK1,k1_relat_1(sK0))),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    (sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1)) & r1_tarski(sK1,k1_relat_1(sK0)) & v2_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f16,f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1 & r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,X1)) != X1 & r1_tarski(X1,k1_relat_1(sK0)) & v2_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ? [X1] : (k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,X1)) != X1 & r1_tarski(X1,k1_relat_1(sK0)) & v2_funct_1(sK0)) => (sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1)) & r1_tarski(sK1,k1_relat_1(sK0)) & v2_funct_1(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1 & r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f7])).
% 0.20/0.47  fof(f7,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1 & (r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,negated_conjecture,(
% 0.20/0.47    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 0.20/0.47    inference(negated_conjecture,[],[f5])).
% 0.20/0.47  fof(f5,conjecture,(
% 0.20/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK0)) | k10_relat_1(sK0,k9_relat_1(sK0,X0)) = X0) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f36,f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X0] : (r1_tarski(k10_relat_1(sK0,k9_relat_1(sK0,X0)),X0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f38,f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    v1_relat_1(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X0] : (r1_tarski(k10_relat_1(sK0,k9_relat_1(sK0,X0)),X0) | ~v1_relat_1(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f37,f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    v1_funct_1(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X0] : (r1_tarski(k10_relat_1(sK0,k9_relat_1(sK0,X0)),X0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)) )),
% 0.20/0.47    inference(resolution,[],[f26,f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    v2_funct_1(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v2_funct_1(X1) | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK0)) | ~r1_tarski(k10_relat_1(sK0,k9_relat_1(sK0,X0)),X0) | k10_relat_1(sK0,k9_relat_1(sK0,X0)) = X0) )),
% 0.20/0.47    inference(resolution,[],[f35,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.47    inference(flattening,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.47    inference(nnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X0] : (r1_tarski(X0,k10_relat_1(sK0,k9_relat_1(sK0,X0))) | ~r1_tarski(X0,k1_relat_1(sK0))) )),
% 0.20/0.47    inference(resolution,[],[f25,f20])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    sK1 != k10_relat_1(sK0,k9_relat_1(sK0,sK1))),
% 0.20/0.47    inference(superposition,[],[f24,f52])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X0] : (k10_relat_1(sK0,X0) = k9_relat_1(k2_funct_1(sK0),X0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f51,f20])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ( ! [X0] : (k10_relat_1(sK0,X0) = k9_relat_1(k2_funct_1(sK0),X0) | ~v1_relat_1(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f50,f21])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X0] : (k10_relat_1(sK0,X0) = k9_relat_1(k2_funct_1(sK0),X0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)) )),
% 0.20/0.47    inference(resolution,[],[f27,f22])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v2_funct_1(X1) | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (3814)------------------------------
% 0.20/0.47  % (3814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (3814)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (3814)Memory used [KB]: 6140
% 0.20/0.47  % (3814)Time elapsed: 0.066 s
% 0.20/0.47  % (3814)------------------------------
% 0.20/0.47  % (3814)------------------------------
% 0.20/0.47  % (3810)Success in time 0.115 s
%------------------------------------------------------------------------------
