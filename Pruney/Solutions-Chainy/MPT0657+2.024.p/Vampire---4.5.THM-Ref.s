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
% DateTime   : Thu Dec  3 12:53:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 140 expanded)
%              Number of leaves         :    5 (  24 expanded)
%              Depth                    :   25
%              Number of atoms          :  265 ( 870 expanded)
%              Number of equality atoms :   97 ( 313 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f208,plain,(
    $false ),
    inference(subsumption_resolution,[],[f207,f22])).

fof(f22,plain,(
    sK1 != k2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
          & k2_relat_1(X1) = k1_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
          & k2_relat_1(X1) = k1_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
                & k2_relat_1(X1) = k1_relat_1(X0)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f207,plain,(
    sK1 = k2_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f206,f17])).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f206,plain,
    ( ~ v1_relat_1(sK1)
    | sK1 = k2_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f205,f18])).

fof(f18,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f205,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK1 = k2_funct_1(sK0) ),
    inference(trivial_inequality_removal,[],[f203])).

fof(f203,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k2_relat_1(sK0))
    | k6_relat_1(k2_relat_1(sK1)) != k6_relat_1(k2_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK1 = k2_funct_1(sK0) ),
    inference(superposition,[],[f202,f21])).

fof(f21,plain,(
    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f202,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(X0,sK0)
      | k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k2_relat_1(sK1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(sK0) = X0 ) ),
    inference(subsumption_resolution,[],[f201,f23])).

fof(f23,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f201,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k2_relat_1(sK1))
      | k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(X0,sK0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(sK0) = X0
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f200,f19])).

fof(f19,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f200,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k2_relat_1(sK1))
      | k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(X0,sK0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(sK0) = X0
      | ~ v2_funct_1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f199,f24])).

fof(f24,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f199,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k2_relat_1(sK1))
      | k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(X0,sK0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(sK0) = X0
      | ~ v1_funct_1(sK0)
      | ~ v2_funct_1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f198,f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f198,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k2_funct_1(sK0))
      | ~ v1_funct_1(X0)
      | k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k2_relat_1(sK1))
      | k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(X0,sK0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(sK0) = X0 ) ),
    inference(subsumption_resolution,[],[f197,f23])).

fof(f197,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k2_relat_1(sK1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(k2_funct_1(sK0))
      | k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(X0,sK0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(sK0) = X0
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f196,f19])).

fof(f196,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k2_relat_1(sK1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(k2_funct_1(sK0))
      | k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(X0,sK0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(sK0) = X0
      | ~ v2_funct_1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f195,f24])).

fof(f195,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k2_relat_1(sK1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(k2_funct_1(sK0))
      | k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(X0,sK0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(sK0) = X0
      | ~ v1_funct_1(sK0)
      | ~ v2_funct_1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f100,f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f100,plain,(
    ! [X1] :
      ( ~ v1_funct_1(k2_funct_1(sK0))
      | k6_relat_1(k2_relat_1(X1)) != k6_relat_1(k2_relat_1(sK1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(k2_funct_1(sK0))
      | k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(X1,sK0)
      | ~ v1_relat_1(X1)
      | k2_funct_1(sK0) = X1 ) ),
    inference(forward_demodulation,[],[f99,f37])).

fof(f37,plain,(
    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f36,f23])).

fof(f36,plain,
    ( ~ v1_relat_1(sK0)
    | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f34,f24])).

fof(f34,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f28,f19])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f99,plain,(
    ! [X1] :
      ( k6_relat_1(k2_relat_1(X1)) != k6_relat_1(k2_relat_1(sK1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(k2_funct_1(sK0))
      | ~ v1_funct_1(k2_funct_1(sK0))
      | k5_relat_1(X1,sK0) != k6_relat_1(k1_relat_1(k2_funct_1(sK0)))
      | ~ v1_relat_1(X1)
      | k2_funct_1(sK0) = X1 ) ),
    inference(subsumption_resolution,[],[f98,f24])).

fof(f98,plain,(
    ! [X1] :
      ( k6_relat_1(k2_relat_1(X1)) != k6_relat_1(k2_relat_1(sK1))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(k2_funct_1(sK0))
      | ~ v1_funct_1(k2_funct_1(sK0))
      | k5_relat_1(X1,sK0) != k6_relat_1(k1_relat_1(k2_funct_1(sK0)))
      | ~ v1_relat_1(X1)
      | k2_funct_1(sK0) = X1 ) ),
    inference(subsumption_resolution,[],[f89,f23])).

fof(f89,plain,(
    ! [X1] :
      ( k6_relat_1(k2_relat_1(X1)) != k6_relat_1(k2_relat_1(sK1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(sK0)
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(k2_funct_1(sK0))
      | ~ v1_funct_1(k2_funct_1(sK0))
      | k5_relat_1(X1,sK0) != k6_relat_1(k1_relat_1(k2_funct_1(sK0)))
      | ~ v1_relat_1(X1)
      | k2_funct_1(sK0) = X1 ) ),
    inference(superposition,[],[f33,f51])).

fof(f51,plain,(
    k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k2_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f50,f20])).

fof(f20,plain,(
    k2_relat_1(sK1) = k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f50,plain,(
    k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f49,f23])).

fof(f49,plain,
    ( ~ v1_relat_1(sK0)
    | k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f47,f24])).

fof(f47,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(resolution,[],[f30,f19])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
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
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f33,plain,(
    ! [X2,X3,X1] :
      ( k5_relat_1(X2,X3) != k6_relat_1(k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X3)
      | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
      | ~ v1_relat_1(X1)
      | X1 = X3 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X3)
      | k2_relat_1(X1) != X0
      | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
      | k5_relat_1(X2,X3) != k6_relat_1(X0)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k5_relat_1(X2,X3) != k6_relat_1(X0)
              | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
              | k2_relat_1(X1) != X0
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k5_relat_1(X2,X3) != k6_relat_1(X0)
              | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
              | k2_relat_1(X1) != X0
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_relat_1(X3) )
             => ( ( k5_relat_1(X2,X3) = k6_relat_1(X0)
                  & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
                  & k2_relat_1(X1) = X0 )
               => X1 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l72_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n015.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:21:23 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (2991)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.43  % (2991)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f208,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(subsumption_resolution,[],[f207,f22])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    sK1 != k2_funct_1(sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.43    inference(flattening,[],[f7])).
% 0.22/0.43  fof(f7,plain,(
% 0.22/0.43    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,negated_conjecture,(
% 0.22/0.43    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.43    inference(negated_conjecture,[],[f5])).
% 0.22/0.43  fof(f5,conjecture,(
% 0.22/0.43    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 0.22/0.43  fof(f207,plain,(
% 0.22/0.43    sK1 = k2_funct_1(sK0)),
% 0.22/0.43    inference(subsumption_resolution,[],[f206,f17])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    v1_relat_1(sK1)),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  fof(f206,plain,(
% 0.22/0.43    ~v1_relat_1(sK1) | sK1 = k2_funct_1(sK0)),
% 0.22/0.43    inference(subsumption_resolution,[],[f205,f18])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    v1_funct_1(sK1)),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  fof(f205,plain,(
% 0.22/0.43    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | sK1 = k2_funct_1(sK0)),
% 0.22/0.43    inference(trivial_inequality_removal,[],[f203])).
% 0.22/0.43  fof(f203,plain,(
% 0.22/0.43    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k2_relat_1(sK0)) | k6_relat_1(k2_relat_1(sK1)) != k6_relat_1(k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | sK1 = k2_funct_1(sK0)),
% 0.22/0.43    inference(superposition,[],[f202,f21])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  fof(f202,plain,(
% 0.22/0.43    ( ! [X0] : (k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(X0,sK0) | k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k2_relat_1(sK1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0) )),
% 0.22/0.43    inference(subsumption_resolution,[],[f201,f23])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    v1_relat_1(sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  fof(f201,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_funct_1(X0) | k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k2_relat_1(sK1)) | k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(X0,sK0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0 | ~v1_relat_1(sK0)) )),
% 0.22/0.43    inference(subsumption_resolution,[],[f200,f19])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    v2_funct_1(sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  fof(f200,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_funct_1(X0) | k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k2_relat_1(sK1)) | k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(X0,sK0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0 | ~v2_funct_1(sK0) | ~v1_relat_1(sK0)) )),
% 0.22/0.43    inference(subsumption_resolution,[],[f199,f24])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    v1_funct_1(sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  fof(f199,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_funct_1(X0) | k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k2_relat_1(sK1)) | k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(X0,sK0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0 | ~v1_funct_1(sK0) | ~v2_funct_1(sK0) | ~v1_relat_1(sK0)) )),
% 0.22/0.43    inference(resolution,[],[f198,f25])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.43    inference(flattening,[],[f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.22/0.43  fof(f198,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(X0) | k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k2_relat_1(sK1)) | k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(X0,sK0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0) )),
% 0.22/0.43    inference(subsumption_resolution,[],[f197,f23])).
% 0.22/0.43  fof(f197,plain,(
% 0.22/0.43    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k2_relat_1(sK1)) | ~v1_funct_1(X0) | ~v1_relat_1(k2_funct_1(sK0)) | k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(X0,sK0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0 | ~v1_relat_1(sK0)) )),
% 0.22/0.43    inference(subsumption_resolution,[],[f196,f19])).
% 0.22/0.43  fof(f196,plain,(
% 0.22/0.43    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k2_relat_1(sK1)) | ~v1_funct_1(X0) | ~v1_relat_1(k2_funct_1(sK0)) | k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(X0,sK0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0 | ~v2_funct_1(sK0) | ~v1_relat_1(sK0)) )),
% 0.22/0.43    inference(subsumption_resolution,[],[f195,f24])).
% 0.22/0.43  fof(f195,plain,(
% 0.22/0.43    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k2_relat_1(sK1)) | ~v1_funct_1(X0) | ~v1_relat_1(k2_funct_1(sK0)) | k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(X0,sK0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0 | ~v1_funct_1(sK0) | ~v2_funct_1(sK0) | ~v1_relat_1(sK0)) )),
% 0.22/0.43    inference(resolution,[],[f100,f26])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f10])).
% 0.22/0.43  fof(f100,plain,(
% 0.22/0.43    ( ! [X1] : (~v1_funct_1(k2_funct_1(sK0)) | k6_relat_1(k2_relat_1(X1)) != k6_relat_1(k2_relat_1(sK1)) | ~v1_funct_1(X1) | ~v1_relat_1(k2_funct_1(sK0)) | k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(X1,sK0) | ~v1_relat_1(X1) | k2_funct_1(sK0) = X1) )),
% 0.22/0.43    inference(forward_demodulation,[],[f99,f37])).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.22/0.43    inference(subsumption_resolution,[],[f36,f23])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    ~v1_relat_1(sK0) | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.22/0.43    inference(subsumption_resolution,[],[f34,f24])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.22/0.43    inference(resolution,[],[f28,f19])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.43    inference(flattening,[],[f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.43  fof(f99,plain,(
% 0.22/0.43    ( ! [X1] : (k6_relat_1(k2_relat_1(X1)) != k6_relat_1(k2_relat_1(sK1)) | ~v1_funct_1(X1) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(k2_funct_1(sK0)) | k5_relat_1(X1,sK0) != k6_relat_1(k1_relat_1(k2_funct_1(sK0))) | ~v1_relat_1(X1) | k2_funct_1(sK0) = X1) )),
% 0.22/0.43    inference(subsumption_resolution,[],[f98,f24])).
% 0.22/0.43  fof(f98,plain,(
% 0.22/0.43    ( ! [X1] : (k6_relat_1(k2_relat_1(X1)) != k6_relat_1(k2_relat_1(sK1)) | ~v1_funct_1(X1) | ~v1_funct_1(sK0) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(k2_funct_1(sK0)) | k5_relat_1(X1,sK0) != k6_relat_1(k1_relat_1(k2_funct_1(sK0))) | ~v1_relat_1(X1) | k2_funct_1(sK0) = X1) )),
% 0.22/0.43    inference(subsumption_resolution,[],[f89,f23])).
% 0.22/0.43  fof(f89,plain,(
% 0.22/0.43    ( ! [X1] : (k6_relat_1(k2_relat_1(X1)) != k6_relat_1(k2_relat_1(sK1)) | ~v1_funct_1(X1) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(k2_funct_1(sK0)) | k5_relat_1(X1,sK0) != k6_relat_1(k1_relat_1(k2_funct_1(sK0))) | ~v1_relat_1(X1) | k2_funct_1(sK0) = X1) )),
% 0.22/0.43    inference(superposition,[],[f33,f51])).
% 0.22/0.43  fof(f51,plain,(
% 0.22/0.43    k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k2_relat_1(sK1))),
% 0.22/0.43    inference(forward_demodulation,[],[f50,f20])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    k2_relat_1(sK1) = k1_relat_1(sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  fof(f50,plain,(
% 0.22/0.43    k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0))),
% 0.22/0.43    inference(subsumption_resolution,[],[f49,f23])).
% 0.22/0.43  fof(f49,plain,(
% 0.22/0.43    ~v1_relat_1(sK0) | k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0))),
% 0.22/0.43    inference(subsumption_resolution,[],[f47,f24])).
% 0.22/0.43  fof(f47,plain,(
% 0.22/0.43    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0))),
% 0.22/0.43    inference(resolution,[],[f30,f19])).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.43    inference(flattening,[],[f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.22/0.43  fof(f33,plain,(
% 0.22/0.43    ( ! [X2,X3,X1] : (k5_relat_1(X2,X3) != k6_relat_1(k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X3) | ~v1_funct_1(X3) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | ~v1_relat_1(X1) | X1 = X3) )),
% 0.22/0.43    inference(equality_resolution,[],[f32])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X3) | ~v1_funct_1(X3) | k2_relat_1(X1) != X0 | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k5_relat_1(X2,X3) != k6_relat_1(X0) | X1 = X3) )),
% 0.22/0.43    inference(cnf_transformation,[],[f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ! [X0,X1] : (! [X2] : (! [X3] : (X1 = X3 | k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(flattening,[],[f15])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ! [X0,X1] : (! [X2] : (! [X3] : ((X1 = X3 | (k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0)) | (~v1_funct_1(X3) | ~v1_relat_1(X3))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.43    inference(ennf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((k5_relat_1(X2,X3) = k6_relat_1(X0) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & k2_relat_1(X1) = X0) => X1 = X3))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l72_funct_1)).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (2991)------------------------------
% 0.22/0.43  % (2991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (2991)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (2991)Memory used [KB]: 1791
% 0.22/0.43  % (2991)Time elapsed: 0.007 s
% 0.22/0.43  % (2991)------------------------------
% 0.22/0.43  % (2991)------------------------------
% 0.22/0.43  % (2966)Success in time 0.065 s
%------------------------------------------------------------------------------
