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
% DateTime   : Thu Dec  3 12:52:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 247 expanded)
%              Number of leaves         :   10 (  60 expanded)
%              Depth                    :   17
%              Number of atoms          :  217 (1089 expanded)
%              Number of equality atoms :   95 ( 415 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f292,plain,(
    $false ),
    inference(subsumption_resolution,[],[f290,f25])).

fof(f25,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
      | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
        | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
            & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

fof(f290,plain,(
    ~ v1_relat_1(sK0) ),
    inference(equality_resolution,[],[f261])).

fof(f261,plain,(
    ! [X0] :
      ( k2_relat_1(X0) != k2_relat_1(sK0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f260,f239])).

fof(f239,plain,(
    ! [X2] :
      ( k2_relat_1(sK0) != k2_relat_1(X2)
      | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(X2,k2_funct_1(sK0)))
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f238,f32])).

fof(f32,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f238,plain,(
    ! [X2] :
      ( k1_relat_1(sK0) = k2_relat_1(k5_relat_1(X2,k2_funct_1(sK0)))
      | k2_relat_1(X2) != k2_relat_1(k6_relat_1(k2_relat_1(sK0)))
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f237,f58])).

fof(f58,plain,(
    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f57,f26])).

fof(f26,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f52,f27])).

fof(f27,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(resolution,[],[f25,f40])).

fof(f40,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f237,plain,(
    ! [X2] :
      ( k2_relat_1(k2_funct_1(sK0)) = k2_relat_1(k5_relat_1(X2,k2_funct_1(sK0)))
      | k2_relat_1(X2) != k2_relat_1(k6_relat_1(k2_relat_1(sK0)))
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f236,f29])).

fof(f29,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f236,plain,(
    ! [X2] :
      ( k2_relat_1(k2_funct_1(sK0)) = k2_relat_1(k5_relat_1(X2,k2_funct_1(sK0)))
      | k2_relat_1(X2) != k2_relat_1(k6_relat_1(k2_relat_1(sK0)))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(sK0)))
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f226,f53])).

fof(f53,plain,(
    v1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f49,f26])).

fof(f49,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(resolution,[],[f25,f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f226,plain,(
    ! [X2] :
      ( k2_relat_1(k2_funct_1(sK0)) = k2_relat_1(k5_relat_1(X2,k2_funct_1(sK0)))
      | k2_relat_1(X2) != k2_relat_1(k6_relat_1(k2_relat_1(sK0)))
      | ~ v1_relat_1(k2_funct_1(sK0))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(sK0)))
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f35,f82])).

fof(f82,plain,(
    k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0)) ),
    inference(forward_demodulation,[],[f70,f56])).

fof(f56,plain,(
    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f55,f26])).

fof(f55,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f51,f27])).

fof(f51,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(resolution,[],[f25,f39])).

fof(f39,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f70,plain,(
    k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(sK0))),k2_funct_1(sK0)) ),
    inference(resolution,[],[f53,f34])).

fof(f34,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
      | k2_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k2_relat_1(X0) = k2_relat_1(X1)
               => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_relat_1)).

fof(f260,plain,(
    ! [X0] :
      ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(sK0)))
      | k2_relat_1(X0) != k2_relat_1(sK0)
      | ~ v1_relat_1(X0) ) ),
    inference(trivial_inequality_removal,[],[f257])).

fof(f257,plain,(
    ! [X0] :
      ( k1_relat_1(sK0) != k1_relat_1(sK0)
      | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(sK0)))
      | k2_relat_1(X0) != k2_relat_1(sK0)
      | ~ v1_relat_1(X0) ) ),
    inference(backward_demodulation,[],[f68,f255])).

fof(f255,plain,(
    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(subsumption_resolution,[],[f250,f56])).

fof(f250,plain,
    ( k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f113,f53])).

fof(f113,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,X0))
      | k1_relat_1(X0) != k2_relat_1(sK0) ) ),
    inference(forward_demodulation,[],[f112,f31])).

fof(f31,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f112,plain,(
    ! [X0] :
      ( k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,X0))
      | k1_relat_1(X0) != k1_relat_1(k6_relat_1(k2_relat_1(sK0)))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f111,f29])).

fof(f111,plain,(
    ! [X0] :
      ( k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,X0))
      | k1_relat_1(X0) != k1_relat_1(k6_relat_1(k2_relat_1(sK0)))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(sK0)))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f107,f25])).

fof(f107,plain,(
    ! [X0] :
      ( k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,X0))
      | k1_relat_1(X0) != k1_relat_1(k6_relat_1(k2_relat_1(sK0)))
      | ~ v1_relat_1(sK0)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(sK0)))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f36,f41])).

fof(f41,plain,(
    sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) ),
    inference(resolution,[],[f25,f33])).

fof(f33,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k1_relat_1(X0) = k1_relat_1(X1)
               => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_relat_1)).

fof(f68,plain,(
    ! [X0] :
      ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
      | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(sK0)))
      | k2_relat_1(X0) != k2_relat_1(sK0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f67,f25])).

fof(f67,plain,(
    ! [X0] :
      ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(sK0)))
      | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
      | k2_relat_1(X0) != k2_relat_1(sK0)
      | ~ v1_relat_1(sK0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f65,f53])).

fof(f65,plain,(
    ! [X0] :
      ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(sK0)))
      | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
      | k2_relat_1(X0) != k2_relat_1(sK0)
      | ~ v1_relat_1(k2_funct_1(sK0))
      | ~ v1_relat_1(sK0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f28,f35])).

fof(f28,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:35:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (13016)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.49  % (13007)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.49  % (12999)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.49  % (13011)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.50  % (13008)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.50  % (13004)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (12999)Refutation not found, incomplete strategy% (12999)------------------------------
% 0.21/0.50  % (12999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (12999)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (12999)Memory used [KB]: 10490
% 0.21/0.50  % (12999)Time elapsed: 0.069 s
% 0.21/0.50  % (12999)------------------------------
% 0.21/0.50  % (12999)------------------------------
% 0.21/0.50  % (13000)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (13007)Refutation not found, incomplete strategy% (13007)------------------------------
% 0.21/0.50  % (13007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (13007)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (13007)Memory used [KB]: 10618
% 0.21/0.50  % (13007)Time elapsed: 0.074 s
% 0.21/0.50  % (13007)------------------------------
% 0.21/0.50  % (13007)------------------------------
% 0.21/0.51  % (13008)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f292,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f290,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    v1_relat_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    (k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0] : (((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f9])).
% 0.21/0.51  fof(f9,conjecture,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).
% 0.21/0.51  fof(f290,plain,(
% 0.21/0.51    ~v1_relat_1(sK0)),
% 0.21/0.51    inference(equality_resolution,[],[f261])).
% 0.21/0.51  fof(f261,plain,(
% 0.21/0.51    ( ! [X0] : (k2_relat_1(X0) != k2_relat_1(sK0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f260,f239])).
% 0.21/0.51  fof(f239,plain,(
% 0.21/0.51    ( ! [X2] : (k2_relat_1(sK0) != k2_relat_1(X2) | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(X2,k2_funct_1(sK0))) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f238,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.51  fof(f238,plain,(
% 0.21/0.51    ( ! [X2] : (k1_relat_1(sK0) = k2_relat_1(k5_relat_1(X2,k2_funct_1(sK0))) | k2_relat_1(X2) != k2_relat_1(k6_relat_1(k2_relat_1(sK0))) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f237,f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f57,f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    v1_funct_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f52,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    v2_funct_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0)),
% 0.21/0.51    inference(resolution,[],[f25,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.51  fof(f237,plain,(
% 0.21/0.51    ( ! [X2] : (k2_relat_1(k2_funct_1(sK0)) = k2_relat_1(k5_relat_1(X2,k2_funct_1(sK0))) | k2_relat_1(X2) != k2_relat_1(k6_relat_1(k2_relat_1(sK0))) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f236,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.21/0.51  fof(f236,plain,(
% 0.21/0.51    ( ! [X2] : (k2_relat_1(k2_funct_1(sK0)) = k2_relat_1(k5_relat_1(X2,k2_funct_1(sK0))) | k2_relat_1(X2) != k2_relat_1(k6_relat_1(k2_relat_1(sK0))) | ~v1_relat_1(k6_relat_1(k2_relat_1(sK0))) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f226,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    v1_relat_1(k2_funct_1(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f49,f26])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    v1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0)),
% 0.21/0.51    inference(resolution,[],[f25,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.51  fof(f226,plain,(
% 0.21/0.51    ( ! [X2] : (k2_relat_1(k2_funct_1(sK0)) = k2_relat_1(k5_relat_1(X2,k2_funct_1(sK0))) | k2_relat_1(X2) != k2_relat_1(k6_relat_1(k2_relat_1(sK0))) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(k6_relat_1(k2_relat_1(sK0))) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(superposition,[],[f35,f82])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0))),
% 0.21/0.51    inference(forward_demodulation,[],[f70,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f55,f26])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f51,f27])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0)),
% 0.21/0.51    inference(resolution,[],[f25,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(sK0))),k2_funct_1(sK0))),
% 0.21/0.51    inference(resolution,[],[f53,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k2_relat_1(X0) = k2_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_relat_1)).
% 0.21/0.51  fof(f260,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(sK0))) | k2_relat_1(X0) != k2_relat_1(sK0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f257])).
% 0.21/0.51  fof(f257,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(sK0) != k1_relat_1(sK0) | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(sK0))) | k2_relat_1(X0) != k2_relat_1(sK0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(backward_demodulation,[],[f68,f255])).
% 0.21/0.51  fof(f255,plain,(
% 0.21/0.51    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.51    inference(subsumption_resolution,[],[f250,f56])).
% 0.21/0.51  fof(f250,plain,(
% 0.21/0.51    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))),
% 0.21/0.51    inference(resolution,[],[f113,f53])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,X0)) | k1_relat_1(X0) != k2_relat_1(sK0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f112,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,X0)) | k1_relat_1(X0) != k1_relat_1(k6_relat_1(k2_relat_1(sK0))) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f111,f29])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,X0)) | k1_relat_1(X0) != k1_relat_1(k6_relat_1(k2_relat_1(sK0))) | ~v1_relat_1(k6_relat_1(k2_relat_1(sK0))) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f107,f25])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,X0)) | k1_relat_1(X0) != k1_relat_1(k6_relat_1(k2_relat_1(sK0))) | ~v1_relat_1(sK0) | ~v1_relat_1(k6_relat_1(k2_relat_1(sK0))) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(superposition,[],[f36,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))),
% 0.21/0.51    inference(resolution,[],[f25,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k1_relat_1(X0) = k1_relat_1(X1) => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_relat_1)).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(sK0))) | k2_relat_1(X0) != k2_relat_1(sK0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f67,f25])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k2_relat_1(X0) != k2_relat_1(sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f65,f53])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k2_relat_1(X0) != k2_relat_1(sK0) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(superposition,[],[f28,f35])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (13008)------------------------------
% 0.21/0.51  % (13008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (13008)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (13008)Memory used [KB]: 1791
% 0.21/0.51  % (13008)Time elapsed: 0.078 s
% 0.21/0.51  % (13008)------------------------------
% 0.21/0.51  % (13008)------------------------------
% 0.21/0.51  % (12993)Success in time 0.143 s
%------------------------------------------------------------------------------
