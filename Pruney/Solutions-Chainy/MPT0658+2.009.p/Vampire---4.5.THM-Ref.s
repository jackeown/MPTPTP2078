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
% DateTime   : Thu Dec  3 12:53:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 267 expanded)
%              Number of leaves         :    7 (  63 expanded)
%              Depth                    :   31
%              Number of atoms          :  297 (1116 expanded)
%              Number of equality atoms :   96 ( 293 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f202,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f197])).

fof(f197,plain,(
    sK0 != sK0 ),
    inference(superposition,[],[f25,f152])).

fof(f152,plain,(
    sK0 = k2_funct_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f151,f22])).

fof(f22,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( sK0 != k2_funct_1(k2_funct_1(sK0))
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( k2_funct_1(k2_funct_1(X0)) != X0
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( sK0 != k2_funct_1(k2_funct_1(sK0))
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( k2_funct_1(k2_funct_1(X0)) != X0
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( k2_funct_1(k2_funct_1(X0)) != X0
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f151,plain,
    ( ~ v1_relat_1(sK0)
    | sK0 = k2_funct_1(k2_funct_1(sK0)) ),
    inference(trivial_inequality_removal,[],[f150])).

fof(f150,plain,
    ( k6_relat_1(k1_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK0))
    | sK0 = k2_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(forward_demodulation,[],[f149,f42])).

fof(f42,plain,(
    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0)) ),
    inference(resolution,[],[f41,f22])).

fof(f41,plain,
    ( ~ v1_relat_1(sK0)
    | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0)) ),
    inference(resolution,[],[f40,f23])).

fof(f23,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,
    ( ~ v1_funct_1(sK0)
    | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f30,f24])).

fof(f24,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f149,plain,
    ( k6_relat_1(k1_relat_1(sK0)) != k5_relat_1(sK0,k2_funct_1(sK0))
    | sK0 = k2_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(trivial_inequality_removal,[],[f147])).

fof(f147,plain,
    ( k6_relat_1(k1_relat_1(sK0)) != k5_relat_1(sK0,k2_funct_1(sK0))
    | sK0 = k2_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | k2_relat_1(sK0) != k2_relat_1(sK0) ),
    inference(resolution,[],[f142,f23])).

fof(f142,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k6_relat_1(k1_relat_1(sK0)) != k5_relat_1(X0,k2_funct_1(sK0))
      | k2_funct_1(k2_funct_1(sK0)) = X0
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) != k2_relat_1(sK0) ) ),
    inference(resolution,[],[f136,f22])).

fof(f136,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK0)
      | ~ v1_funct_1(X0)
      | k6_relat_1(k1_relat_1(sK0)) != k5_relat_1(X0,k2_funct_1(sK0))
      | k2_funct_1(k2_funct_1(sK0)) = X0
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) != k2_relat_1(sK0) ) ),
    inference(resolution,[],[f130,f23])).

fof(f130,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK0)
      | k2_relat_1(X0) != k2_relat_1(sK0)
      | ~ v1_funct_1(X0)
      | k6_relat_1(k1_relat_1(sK0)) != k5_relat_1(X0,k2_funct_1(sK0))
      | k2_funct_1(k2_funct_1(sK0)) = X0
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f124,f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f124,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k2_funct_1(sK0))
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) != k2_relat_1(sK0)
      | ~ v1_funct_1(X0)
      | k6_relat_1(k1_relat_1(sK0)) != k5_relat_1(X0,k2_funct_1(sK0))
      | k2_funct_1(k2_funct_1(sK0)) = X0 ) ),
    inference(resolution,[],[f116,f22])).

fof(f116,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) != k2_relat_1(sK0)
      | ~ v1_relat_1(k2_funct_1(sK0))
      | k6_relat_1(k1_relat_1(sK0)) != k5_relat_1(X0,k2_funct_1(sK0))
      | k2_funct_1(k2_funct_1(sK0)) = X0 ) ),
    inference(resolution,[],[f91,f23])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK0)
      | k2_funct_1(k2_funct_1(sK0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) != k2_relat_1(sK0)
      | ~ v1_relat_1(k2_funct_1(sK0))
      | k6_relat_1(k1_relat_1(sK0)) != k5_relat_1(X0,k2_funct_1(sK0))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f65,f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k2_funct_1(sK0))
      | k6_relat_1(k1_relat_1(sK0)) != k5_relat_1(X0,k2_funct_1(sK0))
      | k2_funct_1(k2_funct_1(sK0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) != k2_relat_1(sK0)
      | ~ v1_relat_1(k2_funct_1(sK0)) ) ),
    inference(forward_demodulation,[],[f64,f37])).

fof(f37,plain,(
    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f36,f22])).

fof(f36,plain,
    ( ~ v1_relat_1(sK0)
    | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f34,f23])).

fof(f34,plain,
    ( ~ v1_funct_1(sK0)
    | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f28,f24])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f64,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(sK0)) != k5_relat_1(X0,k2_funct_1(sK0))
      | k2_relat_1(X0) != k1_relat_1(k2_funct_1(sK0))
      | k2_funct_1(k2_funct_1(sK0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(k2_funct_1(sK0))
      | ~ v1_relat_1(k2_funct_1(sK0)) ) ),
    inference(forward_demodulation,[],[f59,f39])).

fof(f39,plain,(
    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f38,f22])).

fof(f38,plain,
    ( ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f35,f23])).

fof(f35,plain,
    ( ~ v1_funct_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f29,f24])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f59,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(k2_funct_1(sK0))) != k5_relat_1(X0,k2_funct_1(sK0))
      | k2_relat_1(X0) != k1_relat_1(k2_funct_1(sK0))
      | k2_funct_1(k2_funct_1(sK0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(k2_funct_1(sK0))
      | ~ v1_relat_1(k2_funct_1(sK0)) ) ),
    inference(resolution,[],[f57,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | k2_funct_1(X0) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f57,plain,(
    v2_funct_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f56,f22])).

fof(f56,plain,
    ( ~ v1_relat_1(sK0)
    | v2_funct_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f55,f23])).

fof(f55,plain,
    ( ~ v1_funct_1(sK0)
    | v2_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(trivial_inequality_removal,[],[f54])).

fof(f54,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k2_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | v2_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f53,f47])).

fof(f47,plain,(
    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(resolution,[],[f46,f22])).

fof(f46,plain,
    ( ~ v1_relat_1(sK0)
    | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(resolution,[],[f43,f23])).

fof(f43,plain,
    ( ~ v1_funct_1(sK0)
    | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f31,f24])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f53,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(k2_funct_1(sK0),X0)
      | ~ v1_funct_1(X0)
      | v2_funct_1(k2_funct_1(sK0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f52,f22])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK0)
      | v2_funct_1(k2_funct_1(sK0))
      | ~ v1_funct_1(X0)
      | k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(k2_funct_1(sK0),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f50,f23])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(k2_funct_1(sK0))
      | ~ v1_funct_1(X0)
      | k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(k2_funct_1(sK0),X0)
      | ~ v1_relat_1(sK0) ) ),
    inference(superposition,[],[f49,f37])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k1_relat_1(k2_funct_1(X1))) != k5_relat_1(k2_funct_1(X1),X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(k2_funct_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(k2_funct_1(X1))
      | k6_relat_1(k1_relat_1(k2_funct_1(X1))) != k5_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f45,f26])).

fof(f45,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(k2_funct_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | v2_funct_1(k2_funct_1(X1))
      | k5_relat_1(k2_funct_1(X1),X2) != k6_relat_1(k1_relat_1(k2_funct_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f32,f27])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).

fof(f25,plain,(
    sK0 != k2_funct_1(k2_funct_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:50:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (16726)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.47  % (16726)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (16736)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f202,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f197])).
% 0.21/0.48  fof(f197,plain,(
% 0.21/0.48    sK0 != sK0),
% 0.21/0.48    inference(superposition,[],[f25,f152])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    sK0 = k2_funct_1(k2_funct_1(sK0))),
% 0.21/0.48    inference(resolution,[],[f151,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    v1_relat_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    sK0 != k2_funct_1(k2_funct_1(sK0)) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ? [X0] : (k2_funct_1(k2_funct_1(X0)) != X0 & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (sK0 != k2_funct_1(k2_funct_1(sK0)) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0] : (k2_funct_1(k2_funct_1(X0)) != X0 & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0] : ((k2_funct_1(k2_funct_1(X0)) != X0 & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.21/0.48    inference(negated_conjecture,[],[f6])).
% 0.21/0.48  fof(f6,conjecture,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    ~v1_relat_1(sK0) | sK0 = k2_funct_1(k2_funct_1(sK0))),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f150])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    k6_relat_1(k1_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK0)) | sK0 = k2_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(forward_demodulation,[],[f149,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0))),
% 0.21/0.48    inference(resolution,[],[f41,f22])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ~v1_relat_1(sK0) | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0))),
% 0.21/0.48    inference(resolution,[],[f40,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    v1_funct_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ~v1_funct_1(sK0) | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0)) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(resolution,[],[f30,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    v2_funct_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_funct_1(X0) | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    k6_relat_1(k1_relat_1(sK0)) != k5_relat_1(sK0,k2_funct_1(sK0)) | sK0 = k2_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f147])).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    k6_relat_1(k1_relat_1(sK0)) != k5_relat_1(sK0,k2_funct_1(sK0)) | sK0 = k2_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | k2_relat_1(sK0) != k2_relat_1(sK0)),
% 0.21/0.48    inference(resolution,[],[f142,f23])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_1(X0) | k6_relat_1(k1_relat_1(sK0)) != k5_relat_1(X0,k2_funct_1(sK0)) | k2_funct_1(k2_funct_1(sK0)) = X0 | ~v1_relat_1(X0) | k2_relat_1(X0) != k2_relat_1(sK0)) )),
% 0.21/0.48    inference(resolution,[],[f136,f22])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(sK0) | ~v1_funct_1(X0) | k6_relat_1(k1_relat_1(sK0)) != k5_relat_1(X0,k2_funct_1(sK0)) | k2_funct_1(k2_funct_1(sK0)) = X0 | ~v1_relat_1(X0) | k2_relat_1(X0) != k2_relat_1(sK0)) )),
% 0.21/0.48    inference(resolution,[],[f130,f23])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_1(sK0) | k2_relat_1(X0) != k2_relat_1(sK0) | ~v1_funct_1(X0) | k6_relat_1(k1_relat_1(sK0)) != k5_relat_1(X0,k2_funct_1(sK0)) | k2_funct_1(k2_funct_1(sK0)) = X0 | ~v1_relat_1(X0) | ~v1_relat_1(sK0)) )),
% 0.21/0.48    inference(resolution,[],[f124,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(X0) | k2_relat_1(X0) != k2_relat_1(sK0) | ~v1_funct_1(X0) | k6_relat_1(k1_relat_1(sK0)) != k5_relat_1(X0,k2_funct_1(sK0)) | k2_funct_1(k2_funct_1(sK0)) = X0) )),
% 0.21/0.48    inference(resolution,[],[f116,f22])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) != k2_relat_1(sK0) | ~v1_relat_1(k2_funct_1(sK0)) | k6_relat_1(k1_relat_1(sK0)) != k5_relat_1(X0,k2_funct_1(sK0)) | k2_funct_1(k2_funct_1(sK0)) = X0) )),
% 0.21/0.48    inference(resolution,[],[f91,f23])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_1(sK0) | k2_funct_1(k2_funct_1(sK0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) != k2_relat_1(sK0) | ~v1_relat_1(k2_funct_1(sK0)) | k6_relat_1(k1_relat_1(sK0)) != k5_relat_1(X0,k2_funct_1(sK0)) | ~v1_relat_1(sK0)) )),
% 0.21/0.48    inference(resolution,[],[f65,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_1(k2_funct_1(sK0)) | k6_relat_1(k1_relat_1(sK0)) != k5_relat_1(X0,k2_funct_1(sK0)) | k2_funct_1(k2_funct_1(sK0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) != k2_relat_1(sK0) | ~v1_relat_1(k2_funct_1(sK0))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f64,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.21/0.48    inference(resolution,[],[f36,f22])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ~v1_relat_1(sK0) | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.21/0.48    inference(resolution,[],[f34,f23])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ~v1_funct_1(sK0) | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(resolution,[],[f28,f24])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X0] : (k6_relat_1(k1_relat_1(sK0)) != k5_relat_1(X0,k2_funct_1(sK0)) | k2_relat_1(X0) != k1_relat_1(k2_funct_1(sK0)) | k2_funct_1(k2_funct_1(sK0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(k2_funct_1(sK0))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f59,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.21/0.48    inference(resolution,[],[f38,f22])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ~v1_relat_1(sK0) | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.21/0.48    inference(resolution,[],[f35,f23])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ~v1_funct_1(sK0) | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(resolution,[],[f29,f24])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X0] : (k6_relat_1(k2_relat_1(k2_funct_1(sK0))) != k5_relat_1(X0,k2_funct_1(sK0)) | k2_relat_1(X0) != k1_relat_1(k2_funct_1(sK0)) | k2_funct_1(k2_funct_1(sK0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(k2_funct_1(sK0))) )),
% 0.21/0.48    inference(resolution,[],[f57,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v2_funct_1(X0) | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | k2_funct_1(X0) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    v2_funct_1(k2_funct_1(sK0))),
% 0.21/0.48    inference(resolution,[],[f56,f22])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ~v1_relat_1(sK0) | v2_funct_1(k2_funct_1(sK0))),
% 0.21/0.48    inference(resolution,[],[f55,f23])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ~v1_funct_1(sK0) | v2_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k2_relat_1(sK0)) | ~v1_funct_1(sK0) | v2_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(superposition,[],[f53,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))),
% 0.21/0.48    inference(resolution,[],[f46,f22])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ~v1_relat_1(sK0) | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))),
% 0.21/0.48    inference(resolution,[],[f43,f23])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ~v1_funct_1(sK0) | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(resolution,[],[f31,f24])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X0] : (k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(k2_funct_1(sK0),X0) | ~v1_funct_1(X0) | v2_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(resolution,[],[f52,f22])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(sK0) | v2_funct_1(k2_funct_1(sK0)) | ~v1_funct_1(X0) | k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(k2_funct_1(sK0),X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(resolution,[],[f50,f23])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_1(sK0) | ~v1_relat_1(X0) | v2_funct_1(k2_funct_1(sK0)) | ~v1_funct_1(X0) | k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(k2_funct_1(sK0),X0) | ~v1_relat_1(sK0)) )),
% 0.21/0.48    inference(superposition,[],[f49,f37])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k6_relat_1(k1_relat_1(k2_funct_1(X1))) != k5_relat_1(k2_funct_1(X1),X0) | ~v1_relat_1(X0) | v2_funct_1(k2_funct_1(X1)) | ~v1_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(k2_funct_1(X1)) | k6_relat_1(k1_relat_1(k2_funct_1(X1))) != k5_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(resolution,[],[f45,f26])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~v1_relat_1(k2_funct_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | v2_funct_1(k2_funct_1(X1)) | k5_relat_1(k2_funct_1(X1),X2) != k6_relat_1(k1_relat_1(k2_funct_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(resolution,[],[f32,f27])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_funct_1(X0) | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : ((v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    sK0 != k2_funct_1(k2_funct_1(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (16726)------------------------------
% 0.21/0.48  % (16726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (16726)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (16726)Memory used [KB]: 1663
% 0.21/0.48  % (16726)Time elapsed: 0.061 s
% 0.21/0.48  % (16726)------------------------------
% 0.21/0.48  % (16726)------------------------------
% 0.21/0.49  % (16715)Success in time 0.127 s
%------------------------------------------------------------------------------
