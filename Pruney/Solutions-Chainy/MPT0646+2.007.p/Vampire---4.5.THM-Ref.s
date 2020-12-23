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
% DateTime   : Thu Dec  3 12:52:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   37 (  80 expanded)
%              Number of leaves         :    7 (  25 expanded)
%              Depth                    :   15
%              Number of atoms          :  155 ( 444 expanded)
%              Number of equality atoms :   19 (  74 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f39,plain,(
    $false ),
    inference(resolution,[],[f38,f16])).

fof(f16,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ v2_funct_1(sK0)
    & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ~ v2_funct_1(X0)
        & ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v2_funct_1(sK0)
      & ? [X1] :
          ( k5_relat_1(sK0,X1) = k6_relat_1(k1_relat_1(sK0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X1] :
        ( k5_relat_1(sK0,X1) = k6_relat_1(k1_relat_1(sK0))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ? [X1] :
          ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ? [X1] :
          ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( ? [X1] :
              ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & v1_funct_1(X1)
              & v1_relat_1(X1) )
         => v2_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).

fof(f38,plain,(
    ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f37,f18])).

fof(f18,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f37,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f36,f17])).

fof(f17,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f35,f19])).

fof(f19,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f34,f21])).

fof(f21,plain,(
    ~ v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f34,plain,
    ( v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(duplicate_literal_removal,[],[f33])).

fof(f33,plain,
    ( v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f30,f32])).

fof(f32,plain,
    ( r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(trivial_inequality_removal,[],[f31])).

fof(f31,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f25,f28])).

fof(f28,plain,(
    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(superposition,[],[f23,f20])).

fof(f20,plain,(
    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f23,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X1,X0)) != k1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(k5_relat_1(X1,X0)) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(k5_relat_1(X1,X0)) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1)
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

fof(f30,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1))
    | v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f26,f29])).

fof(f29,plain,(
    v2_funct_1(k5_relat_1(sK0,sK1)) ),
    inference(superposition,[],[f22,f20])).

fof(f22,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => v2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:26:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (14970)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.47  % (14970)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(resolution,[],[f38,f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    v1_relat_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ~v2_funct_1(sK0) & (k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f14,f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ? [X0] : (~v2_funct_1(X0) & ? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (~v2_funct_1(sK0) & ? [X1] : (k5_relat_1(sK0,X1) = k6_relat_1(k1_relat_1(sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ? [X1] : (k5_relat_1(sK0,X1) = k6_relat_1(k1_relat_1(sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ? [X0] : (~v2_funct_1(X0) & ? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0] : ((~v2_funct_1(X0) & ? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 0.21/0.47    inference(negated_conjecture,[],[f5])).
% 0.21/0.47  fof(f5,conjecture,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ~v1_relat_1(sK0)),
% 0.21/0.47    inference(resolution,[],[f37,f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    v1_relat_1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.21/0.47    inference(resolution,[],[f36,f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    v1_funct_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(sK1)),
% 0.21/0.47    inference(resolution,[],[f35,f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    v1_funct_1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ~v1_funct_1(sK1) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK1)),
% 0.21/0.47    inference(resolution,[],[f34,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ~v2_funct_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.47    inference(resolution,[],[f30,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    k1_relat_1(sK0) != k1_relat_1(sK0) | r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.47    inference(superposition,[],[f25,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,sK1))),
% 0.21/0.47    inference(superposition,[],[f23,f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X1,X0)) != k1_relat_1(X1) | r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(k5_relat_1(X1,X0)) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(k5_relat_1(X1,X0)) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ~r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1)) | v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.47    inference(resolution,[],[f26,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    v2_funct_1(k5_relat_1(sK0,sK1))),
% 0.21/0.47    inference(superposition,[],[f22,f20])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v2_funct_1(k5_relat_1(X1,X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v2_funct_1(X1) | (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v2_funct_1(k5_relat_1(X1,X0))) => v2_funct_1(X1))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (14970)------------------------------
% 0.21/0.47  % (14970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (14970)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (14970)Memory used [KB]: 1663
% 0.21/0.47  % (14970)Time elapsed: 0.058 s
% 0.21/0.47  % (14970)------------------------------
% 0.21/0.47  % (14970)------------------------------
% 0.21/0.47  % (14964)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.48  % (14960)Success in time 0.112 s
%------------------------------------------------------------------------------
