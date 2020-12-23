%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 139 expanded)
%              Number of leaves         :    9 (  46 expanded)
%              Depth                    :   15
%              Number of atoms          :  120 ( 407 expanded)
%              Number of equality atoms :   29 ( 125 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f205,plain,(
    $false ),
    inference(subsumption_resolution,[],[f204,f22])).

fof(f22,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k1_relat_1(k5_relat_1(sK0,X1)) != k10_relat_1(sK0,k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( k1_relat_1(k5_relat_1(sK0,X1)) != k10_relat_1(sK0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f204,plain,(
    ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f201,f123])).

fof(f123,plain,(
    ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))) ),
    inference(subsumption_resolution,[],[f122,f24])).

fof(f24,plain,(
    k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f122,plain,
    ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1)))
    | k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f120,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f120,plain,(
    r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(superposition,[],[f117,f36])).

fof(f36,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(resolution,[],[f25,f23])).

fof(f23,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f117,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X0)),k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f116,f22])).

fof(f116,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X0)),k1_relat_1(k5_relat_1(sK0,sK1)))
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f115,f23])).

fof(f115,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X0)),k1_relat_1(k5_relat_1(sK0,sK1)))
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f72,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f72,plain,(
    ! [X1] :
      ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
      | r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X1)),k1_relat_1(k5_relat_1(sK0,sK1))) ) ),
    inference(superposition,[],[f26,f59])).

fof(f59,plain,(
    ! [X1] : k10_relat_1(k5_relat_1(sK0,sK1),X1) = k10_relat_1(sK0,k10_relat_1(sK1,X1)) ),
    inference(resolution,[],[f55,f23])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(k5_relat_1(sK0,X0),X1) = k10_relat_1(sK0,k10_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f27,f22])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f201,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f47,f147])).

fof(f147,plain,(
    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1)))) ),
    inference(superposition,[],[f141,f59])).

fof(f141,plain,(
    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(k5_relat_1(sK0,sK1),k2_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(resolution,[],[f104,f23])).

fof(f104,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(sK0,X0)) = k10_relat_1(k5_relat_1(sK0,X0),k2_relat_1(k5_relat_1(sK0,X0))) ) ),
    inference(resolution,[],[f37,f22])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(k5_relat_1(X0,X1),k2_relat_1(k5_relat_1(X0,X1))) ) ),
    inference(resolution,[],[f25,f28])).

fof(f47,plain,(
    ! [X2,X3] :
      ( r1_tarski(k10_relat_1(X2,k10_relat_1(sK1,X3)),k10_relat_1(X2,k1_relat_1(sK1)))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f43,f23])).

fof(f43,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | r1_tarski(k10_relat_1(X2,k10_relat_1(X3,X4)),k10_relat_1(X2,k1_relat_1(X3))) ) ),
    inference(resolution,[],[f32,f26])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:36:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (26415)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (26401)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (26393)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (26399)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (26396)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.56  % (26412)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.56  % (26395)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.57  % (26392)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.57  % (26395)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f205,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(subsumption_resolution,[],[f204,f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    v1_relat_1(sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    (k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f18,f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : (k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (k1_relat_1(k5_relat_1(sK0,X1)) != k10_relat_1(sK0,k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ? [X1] : (k1_relat_1(k5_relat_1(sK0,X1)) != k10_relat_1(sK0,k1_relat_1(X1)) & v1_relat_1(X1)) => (k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f9,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : (k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,negated_conjecture,(
% 0.21/0.57    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.21/0.57    inference(negated_conjecture,[],[f7])).
% 0.21/0.57  fof(f7,conjecture,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.21/0.57  fof(f204,plain,(
% 0.21/0.57    ~v1_relat_1(sK0)),
% 0.21/0.57    inference(subsumption_resolution,[],[f201,f123])).
% 0.21/0.57  fof(f123,plain,(
% 0.21/0.57    ~r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1)))),
% 0.21/0.57    inference(subsumption_resolution,[],[f122,f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1))),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f122,plain,(
% 0.21/0.57    ~r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))) | k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1))),
% 0.21/0.57    inference(resolution,[],[f120,f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.57    inference(flattening,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.57  fof(f120,plain,(
% 0.21/0.57    r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))),
% 0.21/0.57    inference(superposition,[],[f117,f36])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 0.21/0.57    inference(resolution,[],[f25,f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    v1_relat_1(sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,plain,(
% 0.21/0.57    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.21/0.57  fof(f117,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X0)),k1_relat_1(k5_relat_1(sK0,sK1)))) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f116,f22])).
% 0.21/0.57  fof(f116,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X0)),k1_relat_1(k5_relat_1(sK0,sK1))) | ~v1_relat_1(sK0)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f115,f23])).
% 0.21/0.57  fof(f115,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X0)),k1_relat_1(k5_relat_1(sK0,sK1))) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)) )),
% 0.21/0.57    inference(resolution,[],[f72,f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(flattening,[],[f13])).
% 0.21/0.57  fof(f13,plain,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.21/0.57  fof(f72,plain,(
% 0.21/0.57    ( ! [X1] : (~v1_relat_1(k5_relat_1(sK0,sK1)) | r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X1)),k1_relat_1(k5_relat_1(sK0,sK1)))) )),
% 0.21/0.57    inference(superposition,[],[f26,f59])).
% 0.21/0.57  fof(f59,plain,(
% 0.21/0.57    ( ! [X1] : (k10_relat_1(k5_relat_1(sK0,sK1),X1) = k10_relat_1(sK0,k10_relat_1(sK1,X1))) )),
% 0.21/0.57    inference(resolution,[],[f55,f23])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | k10_relat_1(k5_relat_1(sK0,X0),X1) = k10_relat_1(sK0,k10_relat_1(X0,X1))) )),
% 0.21/0.57    inference(resolution,[],[f27,f22])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,plain,(
% 0.21/0.57    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,plain,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 0.21/0.57  fof(f201,plain,(
% 0.21/0.57    r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))) | ~v1_relat_1(sK0)),
% 0.21/0.57    inference(superposition,[],[f47,f147])).
% 0.21/0.57  fof(f147,plain,(
% 0.21/0.57    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1))))),
% 0.21/0.57    inference(superposition,[],[f141,f59])).
% 0.21/0.57  fof(f141,plain,(
% 0.21/0.57    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(k5_relat_1(sK0,sK1),k2_relat_1(k5_relat_1(sK0,sK1)))),
% 0.21/0.57    inference(resolution,[],[f104,f23])).
% 0.21/0.57  fof(f104,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(sK0,X0)) = k10_relat_1(k5_relat_1(sK0,X0),k2_relat_1(k5_relat_1(sK0,X0)))) )),
% 0.21/0.57    inference(resolution,[],[f37,f22])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(k5_relat_1(X0,X1),k2_relat_1(k5_relat_1(X0,X1)))) )),
% 0.21/0.57    inference(resolution,[],[f25,f28])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    ( ! [X2,X3] : (r1_tarski(k10_relat_1(X2,k10_relat_1(sK1,X3)),k10_relat_1(X2,k1_relat_1(sK1))) | ~v1_relat_1(X2)) )),
% 0.21/0.57    inference(resolution,[],[f43,f23])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ( ! [X4,X2,X3] : (~v1_relat_1(X3) | ~v1_relat_1(X2) | r1_tarski(k10_relat_1(X2,k10_relat_1(X3,X4)),k10_relat_1(X2,k1_relat_1(X3)))) )),
% 0.21/0.57    inference(resolution,[],[f32,f26])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.57    inference(flattening,[],[f15])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.57    inference(ennf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (26395)------------------------------
% 0.21/0.57  % (26395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (26395)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (26395)Memory used [KB]: 6396
% 0.21/0.57  % (26395)Time elapsed: 0.139 s
% 0.21/0.57  % (26395)------------------------------
% 0.21/0.57  % (26395)------------------------------
% 0.21/0.57  % (26407)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.57  % (26397)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.57  % (26403)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.57  % (26398)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.58  % (26404)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.58  % (26394)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.58  % (26409)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.59  % (26391)Success in time 0.225 s
%------------------------------------------------------------------------------
