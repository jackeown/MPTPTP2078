%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:53 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  69 expanded)
%              Number of leaves         :    6 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  122 ( 318 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f38,plain,(
    $false ),
    inference(global_subsumption,[],[f22,f21,f19,f37])).

fof(f37,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(forward_demodulation,[],[f36,f35])).

fof(f35,plain,(
    sK1 = k8_relat_1(sK0,sK1) ),
    inference(global_subsumption,[],[f19,f32])).

fof(f32,plain,
    ( ~ v1_relat_1(sK1)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(resolution,[],[f31,f20])).

fof(f20,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK2),sK0)
    & r2_hidden(sK2,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v5_relat_1(sK1,sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f14,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_hidden(k1_funct_1(X1,X2),X0)
            & r2_hidden(X2,k1_relat_1(X1)) )
        & v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(sK1,X2),sK0)
          & r2_hidden(X2,k1_relat_1(sK1)) )
      & v1_funct_1(sK1)
      & v5_relat_1(sK1,sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X2] :
        ( ~ r2_hidden(k1_funct_1(sK1,X2),sK0)
        & r2_hidden(X2,k1_relat_1(sK1)) )
   => ( ~ r2_hidden(k1_funct_1(sK1,sK2),sK0)
      & r2_hidden(sK2,k1_relat_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),X0)
          & r2_hidden(X2,k1_relat_1(X1)) )
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),X0)
          & r2_hidden(X2,k1_relat_1(X1)) )
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v5_relat_1(X1,X0)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( r2_hidden(X2,k1_relat_1(X1))
           => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = X1 ) ),
    inference(duplicate_literal_removal,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f24,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f36,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(k8_relat_1(sK0,sK1)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f28,f23])).

fof(f23,plain,(
    ~ r2_hidden(k1_funct_1(sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X2,X0),X1)
      | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f21,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f22,plain,(
    r2_hidden(sK2,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:09:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (10798)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.13/0.41  % (10799)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.13/0.41  % (10800)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.13/0.41  % (10798)Refutation found. Thanks to Tanya!
% 0.13/0.41  % SZS status Theorem for theBenchmark
% 0.13/0.41  % SZS output start Proof for theBenchmark
% 0.13/0.41  fof(f38,plain,(
% 0.13/0.41    $false),
% 0.13/0.41    inference(global_subsumption,[],[f22,f21,f19,f37])).
% 0.13/0.41  fof(f37,plain,(
% 0.13/0.41    ~r2_hidden(sK2,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.13/0.41    inference(forward_demodulation,[],[f36,f35])).
% 0.13/0.41  fof(f35,plain,(
% 0.13/0.41    sK1 = k8_relat_1(sK0,sK1)),
% 0.13/0.41    inference(global_subsumption,[],[f19,f32])).
% 0.13/0.41  fof(f32,plain,(
% 0.13/0.41    ~v1_relat_1(sK1) | sK1 = k8_relat_1(sK0,sK1)),
% 0.13/0.41    inference(resolution,[],[f31,f20])).
% 0.13/0.41  fof(f20,plain,(
% 0.13/0.41    v5_relat_1(sK1,sK0)),
% 0.13/0.41    inference(cnf_transformation,[],[f15])).
% 0.13/0.41  fof(f15,plain,(
% 0.13/0.41    (~r2_hidden(k1_funct_1(sK1,sK2),sK0) & r2_hidden(sK2,k1_relat_1(sK1))) & v1_funct_1(sK1) & v5_relat_1(sK1,sK0) & v1_relat_1(sK1)),
% 0.13/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f14,f13])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    ? [X0,X1] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),X0) & r2_hidden(X2,k1_relat_1(X1))) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => (? [X2] : (~r2_hidden(k1_funct_1(sK1,X2),sK0) & r2_hidden(X2,k1_relat_1(sK1))) & v1_funct_1(sK1) & v5_relat_1(sK1,sK0) & v1_relat_1(sK1))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    ? [X2] : (~r2_hidden(k1_funct_1(sK1,X2),sK0) & r2_hidden(X2,k1_relat_1(sK1))) => (~r2_hidden(k1_funct_1(sK1,sK2),sK0) & r2_hidden(sK2,k1_relat_1(sK1)))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f7,plain,(
% 0.21/0.41    ? [X0,X1] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),X0) & r2_hidden(X2,k1_relat_1(X1))) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1))),
% 0.21/0.41    inference(flattening,[],[f6])).
% 0.21/0.41  fof(f6,plain,(
% 0.21/0.41    ? [X0,X1] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),X0) & r2_hidden(X2,k1_relat_1(X1))) & (v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)))),
% 0.21/0.41    inference(ennf_transformation,[],[f5])).
% 0.21/0.41  fof(f5,negated_conjecture,(
% 0.21/0.41    ~! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 0.21/0.41    inference(negated_conjecture,[],[f4])).
% 0.21/0.41  fof(f4,conjecture,(
% 0.21/0.41    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).
% 0.21/0.41  fof(f31,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | k8_relat_1(X0,X1) = X1) )),
% 0.21/0.41    inference(duplicate_literal_removal,[],[f30])).
% 0.21/0.41  fof(f30,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.41    inference(resolution,[],[f24,f25])).
% 0.21/0.41  fof(f25,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f16])).
% 0.21/0.41  fof(f16,plain,(
% 0.21/0.41    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.41    inference(nnf_transformation,[],[f10])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.41  fof(f24,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f9])).
% 0.21/0.41  fof(f9,plain,(
% 0.21/0.41    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.41    inference(flattening,[],[f8])).
% 0.21/0.41  fof(f8,plain,(
% 0.21/0.41    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 0.21/0.41  fof(f36,plain,(
% 0.21/0.41    ~r2_hidden(sK2,k1_relat_1(k8_relat_1(sK0,sK1))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.41    inference(resolution,[],[f28,f23])).
% 0.21/0.41  fof(f23,plain,(
% 0.21/0.41    ~r2_hidden(k1_funct_1(sK1,sK2),sK0)),
% 0.21/0.41    inference(cnf_transformation,[],[f15])).
% 0.21/0.41  fof(f28,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f18])).
% 0.21/0.41  fof(f18,plain,(
% 0.21/0.41    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | ~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.41    inference(flattening,[],[f17])).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | (~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.41    inference(nnf_transformation,[],[f12])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.41    inference(flattening,[],[f11])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.41    inference(ennf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).
% 0.21/0.41  fof(f19,plain,(
% 0.21/0.41    v1_relat_1(sK1)),
% 0.21/0.41    inference(cnf_transformation,[],[f15])).
% 0.21/0.41  fof(f21,plain,(
% 0.21/0.41    v1_funct_1(sK1)),
% 0.21/0.41    inference(cnf_transformation,[],[f15])).
% 0.21/0.41  fof(f22,plain,(
% 0.21/0.41    r2_hidden(sK2,k1_relat_1(sK1))),
% 0.21/0.41    inference(cnf_transformation,[],[f15])).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (10798)------------------------------
% 0.21/0.41  % (10798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (10798)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (10798)Memory used [KB]: 6140
% 0.21/0.41  % (10798)Time elapsed: 0.005 s
% 0.21/0.41  % (10798)------------------------------
% 0.21/0.41  % (10798)------------------------------
% 0.21/0.41  % (10793)Success in time 0.061 s
%------------------------------------------------------------------------------
