%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   31 (  63 expanded)
%              Number of leaves         :    6 (  16 expanded)
%              Depth                    :   11
%              Number of atoms          :  106 ( 353 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f33,plain,(
    $false ),
    inference(global_subsumption,[],[f18,f32])).

fof(f32,plain,(
    ~ v3_ordinal1(k1_relat_1(sK0)) ),
    inference(resolution,[],[f31,f22])).

fof(f22,plain,(
    ! [X0] :
      ( v5_ordinal1(X0)
      | ~ v3_ordinal1(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v5_ordinal1(X0)
        | ~ v3_ordinal1(k1_relat_1(X0)) )
      & ( v3_ordinal1(k1_relat_1(X0))
        | ~ v5_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v5_ordinal1(X0)
    <=> v3_ordinal1(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_ordinal1)).

fof(f31,plain,(
    ~ v5_ordinal1(sK0) ),
    inference(global_subsumption,[],[f17,f16,f28,f30])).

fof(f30,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v5_ordinal1(sK0) ),
    inference(duplicate_literal_removal,[],[f29])).

fof(f29,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v5_ordinal1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f25,f19])).

fof(f19,plain,
    ( ~ v5_relat_1(sK0,k2_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v5_ordinal1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( ~ v5_ordinal1(sK0)
      | ~ v1_funct_1(sK0)
      | ~ v5_relat_1(sK0,k2_relat_1(sK0))
      | ~ v1_relat_1(sK0) )
    & v3_ordinal1(k1_relat_1(sK0))
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ( ~ v5_ordinal1(X0)
          | ~ v1_funct_1(X0)
          | ~ v5_relat_1(X0,k2_relat_1(X0))
          | ~ v1_relat_1(X0) )
        & v3_ordinal1(k1_relat_1(X0))
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ v5_ordinal1(sK0)
        | ~ v1_funct_1(sK0)
        | ~ v5_relat_1(sK0,k2_relat_1(sK0))
        | ~ v1_relat_1(sK0) )
      & v3_ordinal1(k1_relat_1(sK0))
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ( ~ v5_ordinal1(X0)
        | ~ v1_funct_1(X0)
        | ~ v5_relat_1(X0,k2_relat_1(X0))
        | ~ v1_relat_1(X0) )
      & v3_ordinal1(k1_relat_1(X0))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ( ~ v5_ordinal1(X0)
        | ~ v1_funct_1(X0)
        | ~ v5_relat_1(X0,k2_relat_1(X0))
        | ~ v1_relat_1(X0) )
      & v3_ordinal1(k1_relat_1(X0))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v3_ordinal1(k1_relat_1(X0))
         => ( v5_ordinal1(X0)
            & v1_funct_1(X0)
            & v5_relat_1(X0,k2_relat_1(X0))
            & v1_relat_1(X0) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v3_ordinal1(k1_relat_1(X0))
       => ( v5_ordinal1(X0)
          & v1_funct_1(X0)
          & v5_relat_1(X0,k2_relat_1(X0))
          & v1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_ordinal1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f28,plain,(
    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(global_subsumption,[],[f16,f27])).

fof(f27,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f23,f26])).

fof(f26,plain,(
    sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) ),
    inference(resolution,[],[f20,f16])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).

fof(f16,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f17,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f18,plain,(
    v3_ordinal1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:08:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (16147)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.42  % (16147)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(global_subsumption,[],[f18,f32])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    ~v3_ordinal1(k1_relat_1(sK0))),
% 0.21/0.42    inference(resolution,[],[f31,f22])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ( ! [X0] : (v5_ordinal1(X0) | ~v3_ordinal1(k1_relat_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0] : ((v5_ordinal1(X0) | ~v3_ordinal1(k1_relat_1(X0))) & (v3_ordinal1(k1_relat_1(X0)) | ~v5_ordinal1(X0)))),
% 0.21/0.42    inference(nnf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0] : (v5_ordinal1(X0) <=> v3_ordinal1(k1_relat_1(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_ordinal1)).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    ~v5_ordinal1(sK0)),
% 0.21/0.42    inference(global_subsumption,[],[f17,f16,f28,f30])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v5_ordinal1(sK0)),
% 0.21/0.42    inference(duplicate_literal_removal,[],[f29])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v5_ordinal1(sK0) | ~v1_relat_1(sK0)),
% 0.21/0.42    inference(resolution,[],[f25,f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ~v5_relat_1(sK0,k2_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v5_ordinal1(sK0) | ~v1_relat_1(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    (~v5_ordinal1(sK0) | ~v1_funct_1(sK0) | ~v5_relat_1(sK0,k2_relat_1(sK0)) | ~v1_relat_1(sK0)) & v3_ordinal1(k1_relat_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ? [X0] : ((~v5_ordinal1(X0) | ~v1_funct_1(X0) | ~v5_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) & v3_ordinal1(k1_relat_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~v5_ordinal1(sK0) | ~v1_funct_1(sK0) | ~v5_relat_1(sK0,k2_relat_1(sK0)) | ~v1_relat_1(sK0)) & v3_ordinal1(k1_relat_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ? [X0] : ((~v5_ordinal1(X0) | ~v1_funct_1(X0) | ~v5_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) & v3_ordinal1(k1_relat_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.42    inference(flattening,[],[f7])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ? [X0] : (((~v5_ordinal1(X0) | ~v1_funct_1(X0) | ~v5_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) & v3_ordinal1(k1_relat_1(X0))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,negated_conjecture,(
% 0.21/0.42    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v3_ordinal1(k1_relat_1(X0)) => (v5_ordinal1(X0) & v1_funct_1(X0) & v5_relat_1(X0,k2_relat_1(X0)) & v1_relat_1(X0))))),
% 0.21/0.42    inference(negated_conjecture,[],[f5])).
% 0.21/0.42  fof(f5,conjecture,(
% 0.21/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v3_ordinal1(k1_relat_1(X0)) => (v5_ordinal1(X0) & v1_funct_1(X0) & v5_relat_1(X0,k2_relat_1(X0)) & v1_relat_1(X0))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_ordinal1)).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(nnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))),
% 0.21/0.42    inference(global_subsumption,[],[f16,f27])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | ~v1_relat_1(sK0)),
% 0.21/0.42    inference(superposition,[],[f23,f26])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    sK0 = k7_relat_1(sK0,k1_relat_1(sK0))),
% 0.21/0.42    inference(resolution,[],[f20,f16])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    v1_relat_1(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    v1_funct_1(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    v3_ordinal1(k1_relat_1(sK0))),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (16147)------------------------------
% 0.21/0.42  % (16147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (16147)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (16147)Memory used [KB]: 6012
% 0.21/0.42  % (16147)Time elapsed: 0.004 s
% 0.21/0.42  % (16147)------------------------------
% 0.21/0.42  % (16147)------------------------------
% 0.21/0.43  % (16141)Success in time 0.067 s
%------------------------------------------------------------------------------
