%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:42 EST 2020

% Result     : Theorem 2.85s
% Output     : Refutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 216 expanded)
%              Number of leaves         :   12 (  68 expanded)
%              Depth                    :   20
%              Number of atoms          :  274 (1090 expanded)
%              Number of equality atoms :   46 ( 196 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12010,plain,(
    $false ),
    inference(subsumption_resolution,[],[f12009,f36])).

fof(f36,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f12009,plain,(
    ~ v2_funct_1(k6_relat_1(k1_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f12008,f33])).

fof(f33,plain,(
    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ v2_funct_1(sK0)
    & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f27,f26])).

fof(f26,plain,
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

fof(f27,plain,
    ( ? [X1] :
        ( k5_relat_1(sK0,X1) = k6_relat_1(k1_relat_1(sK0))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ? [X1] :
          ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ? [X1] :
          ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( ? [X1] :
              ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & v1_funct_1(X1)
              & v1_relat_1(X1) )
         => v2_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).

fof(f12008,plain,(
    ~ v2_funct_1(k5_relat_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f12002,f31])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f12002,plain,
    ( ~ v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f4090,f159])).

fof(f159,plain,(
    ! [X0] :
      ( k5_relat_1(sK0,X0) = k5_relat_1(sK0,k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f158,f29])).

fof(f29,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f158,plain,(
    ! [X0] :
      ( k5_relat_1(sK0,X0) = k5_relat_1(sK0,k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f151,f37])).

fof(f37,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f151,plain,(
    ! [X0] :
      ( k5_relat_1(sK0,X0) = k5_relat_1(sK0,k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(sK0)))
      | ~ v1_relat_1(sK0) ) ),
    inference(superposition,[],[f44,f50])).

fof(f50,plain,(
    sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) ),
    inference(resolution,[],[f29,f41])).

fof(f41,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
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
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f4090,plain,(
    ~ v2_funct_1(k5_relat_1(sK0,k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1))) ),
    inference(subsumption_resolution,[],[f4089,f280])).

fof(f280,plain,(
    ! [X2] : v1_relat_1(k5_relat_1(k6_relat_1(X2),sK1)) ),
    inference(subsumption_resolution,[],[f276,f37])).

fof(f276,plain,(
    ! [X2] :
      ( v1_relat_1(k5_relat_1(k6_relat_1(X2),sK1))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(resolution,[],[f112,f38])).

fof(f38,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f112,plain,(
    ! [X15] :
      ( ~ v1_funct_1(X15)
      | v1_relat_1(k5_relat_1(X15,sK1))
      | ~ v1_relat_1(X15) ) ),
    inference(subsumption_resolution,[],[f102,f32])).

fof(f32,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f102,plain,(
    ! [X15] :
      ( v1_relat_1(k5_relat_1(X15,sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_funct_1(X15)
      | ~ v1_relat_1(X15) ) ),
    inference(resolution,[],[f31,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f4089,plain,
    ( ~ v2_funct_1(k5_relat_1(sK0,k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1)))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1)) ),
    inference(subsumption_resolution,[],[f4071,f322])).

fof(f322,plain,(
    ! [X2] : v1_funct_1(k5_relat_1(k6_relat_1(X2),sK1)) ),
    inference(subsumption_resolution,[],[f318,f37])).

fof(f318,plain,(
    ! [X2] :
      ( v1_funct_1(k5_relat_1(k6_relat_1(X2),sK1))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(resolution,[],[f114,f38])).

fof(f114,plain,(
    ! [X17] :
      ( ~ v1_funct_1(X17)
      | v1_funct_1(k5_relat_1(X17,sK1))
      | ~ v1_relat_1(X17) ) ),
    inference(subsumption_resolution,[],[f104,f32])).

fof(f104,plain,(
    ! [X17] :
      ( v1_funct_1(k5_relat_1(X17,sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_funct_1(X17)
      | ~ v1_relat_1(X17) ) ),
    inference(resolution,[],[f31,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4071,plain,
    ( ~ v2_funct_1(k5_relat_1(sK0,k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1)))
    | ~ v1_funct_1(k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1)) ),
    inference(trivial_inequality_removal,[],[f4063])).

fof(f4063,plain,
    ( k2_relat_1(sK0) != k2_relat_1(sK0)
    | ~ v2_funct_1(k5_relat_1(sK0,k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1)))
    | ~ v1_funct_1(k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1)) ),
    inference(superposition,[],[f71,f968])).

fof(f968,plain,(
    k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1)) ),
    inference(resolution,[],[f419,f140])).

fof(f140,plain,(
    r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f139,f31])).

fof(f139,plain,
    ( r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f138,f32])).

fof(f138,plain,
    ( r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f137,f29])).

fof(f137,plain,
    ( r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f136,f30])).

fof(f30,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f136,plain,
    ( r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f129,f39])).

fof(f39,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f129,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k6_relat_1(k1_relat_1(sK0)))
    | r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f45,f33])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

fof(f419,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK1))
      | k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) = X0 ) ),
    inference(forward_demodulation,[],[f418,f39])).

fof(f418,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK1))
      | k1_relat_1(k6_relat_1(X0)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) ) ),
    inference(subsumption_resolution,[],[f414,f37])).

fof(f414,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK1))
      | k1_relat_1(k6_relat_1(X0)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f91,f40])).

fof(f40,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f91,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_relat_1(X1),k1_relat_1(sK1))
      | k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,sK1))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f31,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f71,plain,(
    ! [X11] :
      ( k2_relat_1(sK0) != k1_relat_1(X11)
      | ~ v2_funct_1(k5_relat_1(sK0,X11))
      | ~ v1_funct_1(X11)
      | ~ v1_relat_1(X11) ) ),
    inference(subsumption_resolution,[],[f70,f30])).

fof(f70,plain,(
    ! [X11] :
      ( k2_relat_1(sK0) != k1_relat_1(X11)
      | ~ v2_funct_1(k5_relat_1(sK0,X11))
      | ~ v1_funct_1(sK0)
      | ~ v1_funct_1(X11)
      | ~ v1_relat_1(X11) ) ),
    inference(subsumption_resolution,[],[f60,f34])).

fof(f34,plain,(
    ~ v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    ! [X11] :
      ( v2_funct_1(sK0)
      | k2_relat_1(sK0) != k1_relat_1(X11)
      | ~ v2_funct_1(k5_relat_1(sK0,X11))
      | ~ v1_funct_1(sK0)
      | ~ v1_funct_1(X11)
      | ~ v1_relat_1(X11) ) ),
    inference(resolution,[],[f29,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:47:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (27211)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.48  % (27209)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.49  % (27202)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (27212)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (27204)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.51  % (27213)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.51  % (27201)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (27208)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.52  % (27221)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.52  % (27210)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.52  % (27207)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (27220)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.53  % (27205)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.53  % (27218)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.53  % (27203)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.53  % (27223)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.53  % (27215)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.53  % (27203)Refutation not found, incomplete strategy% (27203)------------------------------
% 0.21/0.53  % (27203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (27203)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (27203)Memory used [KB]: 10618
% 0.21/0.53  % (27203)Time elapsed: 0.091 s
% 0.21/0.53  % (27203)------------------------------
% 0.21/0.53  % (27203)------------------------------
% 0.21/0.54  % (27199)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.54  % (27206)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.54  % (27222)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.55  % (27224)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.55  % (27219)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.56  % (27214)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.56  % (27217)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.57  % (27224)Refutation not found, incomplete strategy% (27224)------------------------------
% 0.21/0.57  % (27224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (27224)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (27224)Memory used [KB]: 10618
% 0.21/0.57  % (27224)Time elapsed: 0.158 s
% 0.21/0.57  % (27224)------------------------------
% 0.21/0.57  % (27224)------------------------------
% 2.08/0.65  % (27223)Refutation not found, incomplete strategy% (27223)------------------------------
% 2.08/0.65  % (27223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.65  % (27223)Termination reason: Refutation not found, incomplete strategy
% 2.08/0.65  
% 2.08/0.65  % (27223)Memory used [KB]: 1663
% 2.08/0.65  % (27223)Time elapsed: 0.194 s
% 2.08/0.65  % (27223)------------------------------
% 2.08/0.65  % (27223)------------------------------
% 2.85/0.72  % (27211)Refutation found. Thanks to Tanya!
% 2.85/0.72  % SZS status Theorem for theBenchmark
% 2.85/0.72  % SZS output start Proof for theBenchmark
% 2.85/0.72  fof(f12010,plain,(
% 2.85/0.72    $false),
% 2.85/0.72    inference(subsumption_resolution,[],[f12009,f36])).
% 2.85/0.72  fof(f36,plain,(
% 2.85/0.72    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.85/0.72    inference(cnf_transformation,[],[f8])).
% 2.85/0.72  fof(f8,axiom,(
% 2.85/0.72    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.85/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 2.85/0.72  fof(f12009,plain,(
% 2.85/0.72    ~v2_funct_1(k6_relat_1(k1_relat_1(sK0)))),
% 2.85/0.72    inference(forward_demodulation,[],[f12008,f33])).
% 2.85/0.72  fof(f33,plain,(
% 2.85/0.72    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1)),
% 2.85/0.72    inference(cnf_transformation,[],[f28])).
% 2.85/0.72  fof(f28,plain,(
% 2.85/0.72    ~v2_funct_1(sK0) & (k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 2.85/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f27,f26])).
% 2.85/0.72  fof(f26,plain,(
% 2.85/0.72    ? [X0] : (~v2_funct_1(X0) & ? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (~v2_funct_1(sK0) & ? [X1] : (k5_relat_1(sK0,X1) = k6_relat_1(k1_relat_1(sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 2.85/0.72    introduced(choice_axiom,[])).
% 2.85/0.72  fof(f27,plain,(
% 2.85/0.72    ? [X1] : (k5_relat_1(sK0,X1) = k6_relat_1(k1_relat_1(sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 2.85/0.72    introduced(choice_axiom,[])).
% 2.85/0.72  fof(f14,plain,(
% 2.85/0.72    ? [X0] : (~v2_funct_1(X0) & ? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.85/0.72    inference(flattening,[],[f13])).
% 2.85/0.72  fof(f13,plain,(
% 2.85/0.72    ? [X0] : ((~v2_funct_1(X0) & ? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.85/0.72    inference(ennf_transformation,[],[f12])).
% 2.85/0.72  fof(f12,negated_conjecture,(
% 2.85/0.72    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 2.85/0.72    inference(negated_conjecture,[],[f11])).
% 2.85/0.72  fof(f11,conjecture,(
% 2.85/0.72    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 2.85/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).
% 2.85/0.72  fof(f12008,plain,(
% 2.85/0.72    ~v2_funct_1(k5_relat_1(sK0,sK1))),
% 2.85/0.72    inference(subsumption_resolution,[],[f12002,f31])).
% 2.85/0.72  fof(f31,plain,(
% 2.85/0.72    v1_relat_1(sK1)),
% 2.85/0.72    inference(cnf_transformation,[],[f28])).
% 2.85/0.72  fof(f12002,plain,(
% 2.85/0.72    ~v2_funct_1(k5_relat_1(sK0,sK1)) | ~v1_relat_1(sK1)),
% 2.85/0.72    inference(superposition,[],[f4090,f159])).
% 2.85/0.72  fof(f159,plain,(
% 2.85/0.72    ( ! [X0] : (k5_relat_1(sK0,X0) = k5_relat_1(sK0,k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)) | ~v1_relat_1(X0)) )),
% 2.85/0.72    inference(subsumption_resolution,[],[f158,f29])).
% 2.85/0.72  fof(f29,plain,(
% 2.85/0.72    v1_relat_1(sK0)),
% 2.85/0.72    inference(cnf_transformation,[],[f28])).
% 2.85/0.72  fof(f158,plain,(
% 2.85/0.72    ( ! [X0] : (k5_relat_1(sK0,X0) = k5_relat_1(sK0,k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)) | ~v1_relat_1(X0) | ~v1_relat_1(sK0)) )),
% 2.85/0.72    inference(subsumption_resolution,[],[f151,f37])).
% 2.85/0.72  fof(f37,plain,(
% 2.85/0.72    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.85/0.72    inference(cnf_transformation,[],[f7])).
% 2.85/0.72  fof(f7,axiom,(
% 2.85/0.72    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.85/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 2.85/0.72  fof(f151,plain,(
% 2.85/0.72    ( ! [X0] : (k5_relat_1(sK0,X0) = k5_relat_1(sK0,k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k6_relat_1(k2_relat_1(sK0))) | ~v1_relat_1(sK0)) )),
% 2.85/0.72    inference(superposition,[],[f44,f50])).
% 2.85/0.72  fof(f50,plain,(
% 2.85/0.72    sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))),
% 2.85/0.72    inference(resolution,[],[f29,f41])).
% 2.85/0.72  fof(f41,plain,(
% 2.85/0.72    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 2.85/0.72    inference(cnf_transformation,[],[f15])).
% 2.85/0.72  fof(f15,plain,(
% 2.85/0.72    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 2.85/0.72    inference(ennf_transformation,[],[f5])).
% 2.85/0.72  fof(f5,axiom,(
% 2.85/0.72    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 2.85/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 2.85/0.72  fof(f44,plain,(
% 2.85/0.72    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.85/0.72    inference(cnf_transformation,[],[f19])).
% 2.85/0.72  fof(f19,plain,(
% 2.85/0.72    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.85/0.72    inference(ennf_transformation,[],[f2])).
% 2.85/0.72  fof(f2,axiom,(
% 2.85/0.72    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.85/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 2.85/0.72  fof(f4090,plain,(
% 2.85/0.72    ~v2_funct_1(k5_relat_1(sK0,k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1)))),
% 2.85/0.72    inference(subsumption_resolution,[],[f4089,f280])).
% 2.85/0.72  fof(f280,plain,(
% 2.85/0.72    ( ! [X2] : (v1_relat_1(k5_relat_1(k6_relat_1(X2),sK1))) )),
% 2.85/0.72    inference(subsumption_resolution,[],[f276,f37])).
% 2.85/0.72  fof(f276,plain,(
% 2.85/0.72    ( ! [X2] : (v1_relat_1(k5_relat_1(k6_relat_1(X2),sK1)) | ~v1_relat_1(k6_relat_1(X2))) )),
% 2.85/0.72    inference(resolution,[],[f112,f38])).
% 2.85/0.72  fof(f38,plain,(
% 2.85/0.72    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 2.85/0.72    inference(cnf_transformation,[],[f7])).
% 2.85/0.72  fof(f112,plain,(
% 2.85/0.72    ( ! [X15] : (~v1_funct_1(X15) | v1_relat_1(k5_relat_1(X15,sK1)) | ~v1_relat_1(X15)) )),
% 2.85/0.72    inference(subsumption_resolution,[],[f102,f32])).
% 2.85/0.72  fof(f32,plain,(
% 2.85/0.72    v1_funct_1(sK1)),
% 2.85/0.72    inference(cnf_transformation,[],[f28])).
% 2.85/0.72  fof(f102,plain,(
% 2.85/0.72    ( ! [X15] : (v1_relat_1(k5_relat_1(X15,sK1)) | ~v1_funct_1(sK1) | ~v1_funct_1(X15) | ~v1_relat_1(X15)) )),
% 2.85/0.72    inference(resolution,[],[f31,f48])).
% 2.85/0.72  fof(f48,plain,(
% 2.85/0.72    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.85/0.72    inference(cnf_transformation,[],[f25])).
% 2.85/0.72  fof(f25,plain,(
% 2.85/0.72    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.85/0.72    inference(flattening,[],[f24])).
% 2.85/0.72  fof(f24,plain,(
% 2.85/0.72    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.85/0.72    inference(ennf_transformation,[],[f6])).
% 2.85/0.72  fof(f6,axiom,(
% 2.85/0.72    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 2.85/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).
% 2.85/0.72  fof(f4089,plain,(
% 2.85/0.72    ~v2_funct_1(k5_relat_1(sK0,k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1))) | ~v1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1))),
% 2.85/0.72    inference(subsumption_resolution,[],[f4071,f322])).
% 2.85/0.72  fof(f322,plain,(
% 2.85/0.72    ( ! [X2] : (v1_funct_1(k5_relat_1(k6_relat_1(X2),sK1))) )),
% 2.85/0.72    inference(subsumption_resolution,[],[f318,f37])).
% 2.85/0.72  fof(f318,plain,(
% 2.85/0.72    ( ! [X2] : (v1_funct_1(k5_relat_1(k6_relat_1(X2),sK1)) | ~v1_relat_1(k6_relat_1(X2))) )),
% 2.85/0.72    inference(resolution,[],[f114,f38])).
% 2.85/0.72  fof(f114,plain,(
% 2.85/0.72    ( ! [X17] : (~v1_funct_1(X17) | v1_funct_1(k5_relat_1(X17,sK1)) | ~v1_relat_1(X17)) )),
% 2.85/0.72    inference(subsumption_resolution,[],[f104,f32])).
% 2.85/0.72  fof(f104,plain,(
% 2.85/0.72    ( ! [X17] : (v1_funct_1(k5_relat_1(X17,sK1)) | ~v1_funct_1(sK1) | ~v1_funct_1(X17) | ~v1_relat_1(X17)) )),
% 2.85/0.72    inference(resolution,[],[f31,f49])).
% 2.85/0.72  fof(f49,plain,(
% 2.85/0.72    ( ! [X0,X1] : (v1_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.85/0.72    inference(cnf_transformation,[],[f25])).
% 2.85/0.72  fof(f4071,plain,(
% 2.85/0.72    ~v2_funct_1(k5_relat_1(sK0,k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1))) | ~v1_funct_1(k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1)) | ~v1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1))),
% 2.85/0.72    inference(trivial_inequality_removal,[],[f4063])).
% 2.85/0.72  fof(f4063,plain,(
% 2.85/0.72    k2_relat_1(sK0) != k2_relat_1(sK0) | ~v2_funct_1(k5_relat_1(sK0,k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1))) | ~v1_funct_1(k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1)) | ~v1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1))),
% 2.85/0.72    inference(superposition,[],[f71,f968])).
% 2.85/0.72  fof(f968,plain,(
% 2.85/0.72    k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1))),
% 2.85/0.72    inference(resolution,[],[f419,f140])).
% 2.85/0.72  fof(f140,plain,(
% 2.85/0.72    r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1))),
% 2.85/0.72    inference(subsumption_resolution,[],[f139,f31])).
% 2.85/0.72  fof(f139,plain,(
% 2.85/0.72    r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 2.85/0.72    inference(subsumption_resolution,[],[f138,f32])).
% 2.85/0.72  fof(f138,plain,(
% 2.85/0.72    r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 2.85/0.72    inference(subsumption_resolution,[],[f137,f29])).
% 2.85/0.72  fof(f137,plain,(
% 2.85/0.72    r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1)) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 2.85/0.72    inference(subsumption_resolution,[],[f136,f30])).
% 2.85/0.72  fof(f30,plain,(
% 2.85/0.72    v1_funct_1(sK0)),
% 2.85/0.72    inference(cnf_transformation,[],[f28])).
% 2.85/0.72  fof(f136,plain,(
% 2.85/0.72    r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 2.85/0.72    inference(subsumption_resolution,[],[f129,f39])).
% 2.85/0.72  fof(f39,plain,(
% 2.85/0.72    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.85/0.72    inference(cnf_transformation,[],[f3])).
% 2.85/0.72  fof(f3,axiom,(
% 2.85/0.72    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.85/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 2.85/0.72  fof(f129,plain,(
% 2.85/0.72    k1_relat_1(sK0) != k1_relat_1(k6_relat_1(k1_relat_1(sK0))) | r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 2.85/0.72    inference(superposition,[],[f45,f33])).
% 2.85/0.72  fof(f45,plain,(
% 2.85/0.72    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.85/0.72    inference(cnf_transformation,[],[f21])).
% 2.85/0.72  fof(f21,plain,(
% 2.85/0.72    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.85/0.72    inference(flattening,[],[f20])).
% 2.85/0.72  fof(f20,plain,(
% 2.85/0.72    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.85/0.72    inference(ennf_transformation,[],[f9])).
% 2.85/0.72  fof(f9,axiom,(
% 2.85/0.72    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 2.85/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).
% 2.85/0.72  fof(f419,plain,(
% 2.85/0.72    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) = X0) )),
% 2.85/0.72    inference(forward_demodulation,[],[f418,f39])).
% 2.85/0.72  fof(f418,plain,(
% 2.85/0.72    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k1_relat_1(k6_relat_1(X0)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1))) )),
% 2.85/0.72    inference(subsumption_resolution,[],[f414,f37])).
% 2.85/0.72  fof(f414,plain,(
% 2.85/0.72    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k1_relat_1(k6_relat_1(X0)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 2.85/0.72    inference(superposition,[],[f91,f40])).
% 2.85/0.72  fof(f40,plain,(
% 2.85/0.72    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.85/0.72    inference(cnf_transformation,[],[f3])).
% 2.85/0.72  fof(f91,plain,(
% 2.85/0.72    ( ! [X1] : (~r1_tarski(k2_relat_1(X1),k1_relat_1(sK1)) | k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,sK1)) | ~v1_relat_1(X1)) )),
% 2.85/0.72    inference(resolution,[],[f31,f43])).
% 2.85/0.72  fof(f43,plain,(
% 2.85/0.72    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.85/0.72    inference(cnf_transformation,[],[f18])).
% 2.85/0.72  fof(f18,plain,(
% 2.85/0.72    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.85/0.72    inference(flattening,[],[f17])).
% 2.85/0.72  fof(f17,plain,(
% 2.85/0.72    ! [X0] : (! [X1] : ((k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.85/0.72    inference(ennf_transformation,[],[f1])).
% 2.85/0.72  fof(f1,axiom,(
% 2.85/0.72    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0))))),
% 2.85/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 2.85/0.72  fof(f71,plain,(
% 2.85/0.72    ( ! [X11] : (k2_relat_1(sK0) != k1_relat_1(X11) | ~v2_funct_1(k5_relat_1(sK0,X11)) | ~v1_funct_1(X11) | ~v1_relat_1(X11)) )),
% 2.85/0.72    inference(subsumption_resolution,[],[f70,f30])).
% 2.85/0.72  fof(f70,plain,(
% 2.85/0.72    ( ! [X11] : (k2_relat_1(sK0) != k1_relat_1(X11) | ~v2_funct_1(k5_relat_1(sK0,X11)) | ~v1_funct_1(sK0) | ~v1_funct_1(X11) | ~v1_relat_1(X11)) )),
% 2.85/0.72    inference(subsumption_resolution,[],[f60,f34])).
% 2.85/0.72  fof(f34,plain,(
% 2.85/0.72    ~v2_funct_1(sK0)),
% 2.85/0.72    inference(cnf_transformation,[],[f28])).
% 2.85/0.72  fof(f60,plain,(
% 2.85/0.72    ( ! [X11] : (v2_funct_1(sK0) | k2_relat_1(sK0) != k1_relat_1(X11) | ~v2_funct_1(k5_relat_1(sK0,X11)) | ~v1_funct_1(sK0) | ~v1_funct_1(X11) | ~v1_relat_1(X11)) )),
% 2.85/0.72    inference(resolution,[],[f29,f46])).
% 2.85/0.72  fof(f46,plain,(
% 2.85/0.72    ( ! [X0,X1] : (v2_funct_1(X1) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.85/0.72    inference(cnf_transformation,[],[f23])).
% 2.85/0.72  fof(f23,plain,(
% 2.85/0.72    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.85/0.72    inference(flattening,[],[f22])).
% 2.85/0.72  fof(f22,plain,(
% 2.85/0.72    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.85/0.72    inference(ennf_transformation,[],[f10])).
% 2.85/0.72  fof(f10,axiom,(
% 2.85/0.72    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 2.85/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).
% 2.85/0.72  % SZS output end Proof for theBenchmark
% 2.85/0.72  % (27211)------------------------------
% 2.85/0.72  % (27211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.85/0.72  % (27211)Termination reason: Refutation
% 2.85/0.72  
% 2.85/0.72  % (27211)Memory used [KB]: 9083
% 2.85/0.72  % (27211)Time elapsed: 0.275 s
% 2.85/0.72  % (27211)------------------------------
% 2.85/0.72  % (27211)------------------------------
% 2.85/0.72  % (27198)Success in time 0.364 s
%------------------------------------------------------------------------------
