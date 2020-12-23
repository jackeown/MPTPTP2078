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
% DateTime   : Thu Dec  3 12:55:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   42 (  80 expanded)
%              Number of leaves         :    7 (  19 expanded)
%              Depth                    :   13
%              Number of atoms          :  137 ( 349 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f50,plain,(
    $false ),
    inference(global_subsumption,[],[f25,f49])).

fof(f49,plain,(
    ~ r2_hidden(sK1,k1_relat_1(sK2)) ),
    inference(resolution,[],[f48,f35])).

fof(f35,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK1),sK0) ),
    inference(resolution,[],[f30,f26])).

fof(f26,plain,(
    ~ m1_subset_1(k1_funct_1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ m1_subset_1(k1_funct_1(sK2,sK1),sK0)
    & r2_hidden(sK1,k1_relat_1(sK2))
    & v1_funct_1(sK2)
    & v5_relat_1(sK2,sK0)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ~ m1_subset_1(k1_funct_1(X2,X1),X0)
        & r2_hidden(X1,k1_relat_1(X2))
        & v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
   => ( ~ m1_subset_1(k1_funct_1(sK2,sK1),sK0)
      & r2_hidden(sK1,k1_relat_1(sK2))
      & v1_funct_1(sK2)
      & v5_relat_1(sK2,sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_subset_1(k1_funct_1(X2,X1),X0)
      & r2_hidden(X1,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v5_relat_1(X2,X0)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_subset_1(k1_funct_1(X2,X1),X0)
      & r2_hidden(X1,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v5_relat_1(X2,X0)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
       => ( r2_hidden(X1,k1_relat_1(X2))
         => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f48,plain,(
    ! [X6] :
      ( r2_hidden(k1_funct_1(sK2,X6),sK0)
      | ~ r2_hidden(X6,k1_relat_1(sK2)) ) ),
    inference(global_subsumption,[],[f24,f22,f47])).

fof(f47,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,k1_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | r2_hidden(k1_funct_1(sK2,X6),sK0) ) ),
    inference(resolution,[],[f31,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK2))
      | r2_hidden(X0,sK0) ) ),
    inference(global_subsumption,[],[f22,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK2))
      | r2_hidden(X0,sK0)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f32,f41])).

fof(f41,plain,(
    sK2 = k8_relat_1(sK0,sK2) ),
    inference(global_subsumption,[],[f22,f38])).

fof(f38,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k8_relat_1(sK0,sK2) ),
    inference(resolution,[],[f37,f23])).

fof(f23,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = X1 ) ),
    inference(duplicate_literal_removal,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f27,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      | r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(X0,k2_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k2_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(X0,k2_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k2_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(X0,k2_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(X0,k2_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_relat_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(f22,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f24,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f25,plain,(
    r2_hidden(sK1,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:26:15 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.43  % (1262)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.43  % (1265)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.43  % (1262)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f50,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(global_subsumption,[],[f25,f49])).
% 0.22/0.43  fof(f49,plain,(
% 0.22/0.43    ~r2_hidden(sK1,k1_relat_1(sK2))),
% 0.22/0.43    inference(resolution,[],[f48,f35])).
% 0.22/0.43  fof(f35,plain,(
% 0.22/0.43    ~r2_hidden(k1_funct_1(sK2,sK1),sK0)),
% 0.22/0.43    inference(resolution,[],[f30,f26])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ~m1_subset_1(k1_funct_1(sK2,sK1),sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f18])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ~m1_subset_1(k1_funct_1(sK2,sK1),sK0) & r2_hidden(sK1,k1_relat_1(sK2)) & v1_funct_1(sK2) & v5_relat_1(sK2,sK0) & v1_relat_1(sK2)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f17])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ? [X0,X1,X2] : (~m1_subset_1(k1_funct_1(X2,X1),X0) & r2_hidden(X1,k1_relat_1(X2)) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (~m1_subset_1(k1_funct_1(sK2,sK1),sK0) & r2_hidden(sK1,k1_relat_1(sK2)) & v1_funct_1(sK2) & v5_relat_1(sK2,sK0) & v1_relat_1(sK2))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ? [X0,X1,X2] : (~m1_subset_1(k1_funct_1(X2,X1),X0) & r2_hidden(X1,k1_relat_1(X2)) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2))),
% 0.22/0.43    inference(flattening,[],[f8])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ? [X0,X1,X2] : ((~m1_subset_1(k1_funct_1(X2,X1),X0) & r2_hidden(X1,k1_relat_1(X2))) & (v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)))),
% 0.22/0.43    inference(ennf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 0.22/0.43    inference(negated_conjecture,[],[f6])).
% 0.22/0.43  fof(f6,conjecture,(
% 0.22/0.43    ! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.43  fof(f48,plain,(
% 0.22/0.43    ( ! [X6] : (r2_hidden(k1_funct_1(sK2,X6),sK0) | ~r2_hidden(X6,k1_relat_1(sK2))) )),
% 0.22/0.43    inference(global_subsumption,[],[f24,f22,f47])).
% 0.22/0.43  fof(f47,plain,(
% 0.22/0.43    ( ! [X6] : (~r2_hidden(X6,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | r2_hidden(k1_funct_1(sK2,X6),sK0)) )),
% 0.22/0.43    inference(resolution,[],[f31,f43])).
% 0.22/0.43  fof(f43,plain,(
% 0.22/0.43    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | r2_hidden(X0,sK0)) )),
% 0.22/0.43    inference(global_subsumption,[],[f22,f42])).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | r2_hidden(X0,sK0) | ~v1_relat_1(sK2)) )),
% 0.22/0.43    inference(superposition,[],[f32,f41])).
% 0.22/0.43  fof(f41,plain,(
% 0.22/0.43    sK2 = k8_relat_1(sK0,sK2)),
% 0.22/0.43    inference(global_subsumption,[],[f22,f38])).
% 0.22/0.43  fof(f38,plain,(
% 0.22/0.43    ~v1_relat_1(sK2) | sK2 = k8_relat_1(sK0,sK2)),
% 0.22/0.43    inference(resolution,[],[f37,f23])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    v5_relat_1(sK2,sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f18])).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | k8_relat_1(X0,X1) = X1) )),
% 0.22/0.43    inference(duplicate_literal_removal,[],[f36])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(resolution,[],[f27,f28])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f19])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(nnf_transformation,[],[f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(flattening,[],[f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) | r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f21])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (((r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) | ~r2_hidden(X0,k2_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k2_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))))) | ~v1_relat_1(X2))),
% 0.22/0.43    inference(flattening,[],[f20])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (((r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) | (~r2_hidden(X0,k2_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k2_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))))) | ~v1_relat_1(X2))),
% 0.22/0.43    inference(nnf_transformation,[],[f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ! [X0,X1,X2] : ((r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(X0,k2_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.22/0.43    inference(ennf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(X0,k2_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_relat_1)).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f15])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(flattening,[],[f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.43    inference(ennf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    v1_relat_1(sK2)),
% 0.22/0.43    inference(cnf_transformation,[],[f18])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    v1_funct_1(sK2)),
% 0.22/0.43    inference(cnf_transformation,[],[f18])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    r2_hidden(sK1,k1_relat_1(sK2))),
% 0.22/0.43    inference(cnf_transformation,[],[f18])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (1262)------------------------------
% 0.22/0.43  % (1262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (1262)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (1262)Memory used [KB]: 6140
% 0.22/0.43  % (1262)Time elapsed: 0.006 s
% 0.22/0.43  % (1262)------------------------------
% 0.22/0.43  % (1262)------------------------------
% 0.22/0.43  % (1257)Success in time 0.063 s
%------------------------------------------------------------------------------
