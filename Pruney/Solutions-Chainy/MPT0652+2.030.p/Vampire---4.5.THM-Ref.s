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
% DateTime   : Thu Dec  3 12:52:57 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 206 expanded)
%              Number of leaves         :   16 (  48 expanded)
%              Depth                    :   17
%              Number of atoms          :  247 ( 711 expanded)
%              Number of equality atoms :   78 ( 242 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f465,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f78,f86,f88,f141,f175,f219,f464])).

fof(f464,plain,(
    spl1_2 ),
    inference(avatar_contradiction_clause,[],[f463])).

fof(f463,plain,
    ( $false
    | spl1_2 ),
    inference(trivial_inequality_removal,[],[f454])).

fof(f454,plain,
    ( k2_relat_1(sK0) != k2_relat_1(sK0)
    | spl1_2 ),
    inference(superposition,[],[f43,f446])).

fof(f446,plain,(
    k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(forward_demodulation,[],[f445,f54])).

fof(f54,plain,(
    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(global_subsumption,[],[f24,f25,f53])).

fof(f53,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f36,f26])).

fof(f26,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
            & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

fof(f36,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
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

fof(f25,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f445,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(forward_demodulation,[],[f442,f97])).

fof(f97,plain,(
    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) ),
    inference(global_subsumption,[],[f24,f96])).

fof(f96,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(forward_demodulation,[],[f94,f56])).

fof(f56,plain,(
    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(global_subsumption,[],[f24,f25,f55])).

fof(f55,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f37,f26])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f94,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0))))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f47,f25])).

fof(f47,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | k2_funct_1(X1) = k5_relat_1(k2_funct_1(X1),k6_relat_1(k2_relat_1(k2_funct_1(X1))))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f30,f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f442,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0)))) ),
    inference(resolution,[],[f430,f24])).

fof(f430,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(X0)))) ) ),
    inference(global_subsumption,[],[f24,f424])).

fof(f424,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(X0))))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f413,f25])).

fof(f413,plain,(
    ! [X4,X3] :
      ( ~ v1_funct_1(X4)
      | ~ v1_relat_1(X3)
      | k1_relat_1(k5_relat_1(k2_funct_1(X4),X3)) = k1_relat_1(k5_relat_1(k2_funct_1(X4),k6_relat_1(k1_relat_1(X3))))
      | ~ v1_relat_1(X4) ) ),
    inference(global_subsumption,[],[f293])).

fof(f293,plain,(
    ! [X4,X3] :
      ( ~ v1_relat_1(X3)
      | k1_relat_1(k5_relat_1(k2_funct_1(X4),X3)) = k1_relat_1(k5_relat_1(k2_funct_1(X4),k6_relat_1(k1_relat_1(X3))))
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f150,f34])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(k5_relat_1(X0,k6_relat_1(k1_relat_1(X1)))) ) ),
    inference(resolution,[],[f106,f27])).

fof(f27,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k6_relat_1(k1_relat_1(X0)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(k5_relat_1(X1,k6_relat_1(k1_relat_1(X0)))) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X1) != X0
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k6_relat_1(X0))
      | k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(k5_relat_1(X2,k6_relat_1(X0))) ) ),
    inference(superposition,[],[f32,f28])).

fof(f28,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
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
             => ( k1_relat_1(X0) = k1_relat_1(X1)
               => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_relat_1)).

fof(f43,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl1_2
  <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f219,plain,
    ( spl1_1
    | ~ spl1_13 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | spl1_1
    | ~ spl1_13 ),
    inference(trivial_inequality_removal,[],[f212])).

fof(f212,plain,
    ( k2_relat_1(sK0) != k2_relat_1(sK0)
    | spl1_1
    | ~ spl1_13 ),
    inference(superposition,[],[f40,f211])).

fof(f211,plain,
    ( k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ spl1_13 ),
    inference(forward_demodulation,[],[f208,f49])).

fof(f49,plain,(
    sK0 = k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0) ),
    inference(resolution,[],[f31,f24])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f208,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0))
    | ~ spl1_13 ),
    inference(resolution,[],[f138,f24])).

fof(f138,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) = k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),X0)) )
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl1_13
  <=> ! [X0] :
        ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) = k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f40,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl1_1
  <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f175,plain,
    ( ~ spl1_3
    | spl1_13
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f172,f134,f137,f64])).

fof(f64,plain,
    ( spl1_3
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f134,plain,
    ( spl1_12
  <=> v1_relat_1(k6_relat_1(k1_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f172,plain,(
    ! [X2] :
      ( ~ v1_relat_1(k6_relat_1(k1_relat_1(sK0)))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k2_funct_1(sK0))
      | k2_relat_1(k5_relat_1(k2_funct_1(sK0),X2)) = k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),X2)) ) ),
    inference(superposition,[],[f117,f56])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k6_relat_1(k2_relat_1(X0)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(X0)),X1)) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X1) != X0
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k6_relat_1(X0))
      | k2_relat_1(k5_relat_1(X1,X2)) = k2_relat_1(k5_relat_1(k6_relat_1(X0),X2)) ) ),
    inference(superposition,[],[f33,f29])).

fof(f29,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k2_relat_1(X0) = k2_relat_1(X1)
               => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_relat_1)).

fof(f141,plain,(
    spl1_12 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | spl1_12 ),
    inference(resolution,[],[f135,f27])).

fof(f135,plain,
    ( ~ v1_relat_1(k6_relat_1(k1_relat_1(sK0)))
    | spl1_12 ),
    inference(avatar_component_clause,[],[f134])).

fof(f88,plain,(
    spl1_6 ),
    inference(avatar_contradiction_clause,[],[f87])).

fof(f87,plain,
    ( $false
    | spl1_6 ),
    inference(resolution,[],[f77,f25])).

fof(f77,plain,
    ( ~ v1_funct_1(sK0)
    | spl1_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl1_6
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f86,plain,(
    spl1_5 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | spl1_5 ),
    inference(resolution,[],[f74,f24])).

fof(f74,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl1_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f78,plain,
    ( ~ spl1_5
    | ~ spl1_6
    | spl1_3 ),
    inference(avatar_split_clause,[],[f71,f64,f76,f73])).

fof(f71,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_3 ),
    inference(resolution,[],[f65,f34])).

fof(f65,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | spl1_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f44,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f23,f42,f39])).

fof(f23,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n016.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 10:24:49 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.23/0.52  % (30430)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.23/0.52  % (30428)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.23/0.52  % (30427)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.23/0.52  % (30431)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.23/0.53  % (30429)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 1.23/0.53  % (30435)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.23/0.53  % (30426)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.23/0.53  % (30448)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.23/0.53  % (30440)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.23/0.54  % (30441)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.23/0.54  % (30433)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.23/0.54  % (30436)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.23/0.54  % (30437)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.23/0.54  % (30436)Refutation not found, incomplete strategy% (30436)------------------------------
% 1.23/0.54  % (30436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.54  % (30433)Refutation not found, incomplete strategy% (30433)------------------------------
% 1.23/0.54  % (30433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.54  % (30432)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.23/0.54  % (30434)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.23/0.54  % (30438)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.23/0.54  % (30445)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 1.23/0.54  % (30447)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.23/0.54  % (30446)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.23/0.54  % (30443)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.23/0.55  % (30429)Refutation not found, incomplete strategy% (30429)------------------------------
% 1.23/0.55  % (30429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.55  % (30429)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.55  
% 1.23/0.55  % (30429)Memory used [KB]: 10490
% 1.23/0.55  % (30429)Time elapsed: 0.111 s
% 1.23/0.55  % (30429)------------------------------
% 1.23/0.55  % (30429)------------------------------
% 1.23/0.55  % (30439)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.23/0.55  % (30436)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.55  
% 1.23/0.55  % (30436)Memory used [KB]: 10618
% 1.23/0.55  % (30436)Time elapsed: 0.106 s
% 1.23/0.55  % (30436)------------------------------
% 1.23/0.55  % (30436)------------------------------
% 1.23/0.55  % (30444)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.23/0.55  % (30433)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.55  
% 1.23/0.55  % (30433)Memory used [KB]: 6140
% 1.23/0.55  % (30433)Time elapsed: 0.096 s
% 1.23/0.55  % (30433)------------------------------
% 1.23/0.55  % (30433)------------------------------
% 1.23/0.55  % (30449)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.23/0.55  % (30449)Refutation not found, incomplete strategy% (30449)------------------------------
% 1.23/0.55  % (30449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.55  % (30449)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.55  
% 1.23/0.55  % (30449)Memory used [KB]: 10618
% 1.23/0.55  % (30449)Time elapsed: 0.115 s
% 1.23/0.55  % (30449)------------------------------
% 1.23/0.55  % (30449)------------------------------
% 1.40/0.55  % (30438)Refutation found. Thanks to Tanya!
% 1.40/0.55  % SZS status Theorem for theBenchmark
% 1.40/0.55  % SZS output start Proof for theBenchmark
% 1.40/0.55  fof(f465,plain,(
% 1.40/0.55    $false),
% 1.40/0.55    inference(avatar_sat_refutation,[],[f44,f78,f86,f88,f141,f175,f219,f464])).
% 1.40/0.55  fof(f464,plain,(
% 1.40/0.55    spl1_2),
% 1.40/0.55    inference(avatar_contradiction_clause,[],[f463])).
% 1.40/0.55  fof(f463,plain,(
% 1.40/0.55    $false | spl1_2),
% 1.40/0.55    inference(trivial_inequality_removal,[],[f454])).
% 1.40/0.55  fof(f454,plain,(
% 1.40/0.55    k2_relat_1(sK0) != k2_relat_1(sK0) | spl1_2),
% 1.40/0.55    inference(superposition,[],[f43,f446])).
% 1.40/0.55  fof(f446,plain,(
% 1.40/0.55    k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 1.40/0.55    inference(forward_demodulation,[],[f445,f54])).
% 1.40/0.55  fof(f54,plain,(
% 1.40/0.55    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 1.40/0.55    inference(global_subsumption,[],[f24,f25,f53])).
% 1.40/0.55  fof(f53,plain,(
% 1.40/0.55    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 1.40/0.55    inference(resolution,[],[f36,f26])).
% 1.40/0.55  fof(f26,plain,(
% 1.40/0.55    v2_funct_1(sK0)),
% 1.40/0.55    inference(cnf_transformation,[],[f12])).
% 1.40/0.55  fof(f12,plain,(
% 1.40/0.55    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.40/0.55    inference(flattening,[],[f11])).
% 1.40/0.55  fof(f11,plain,(
% 1.40/0.55    ? [X0] : (((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.40/0.55    inference(ennf_transformation,[],[f10])).
% 1.40/0.55  fof(f10,negated_conjecture,(
% 1.40/0.55    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 1.40/0.55    inference(negated_conjecture,[],[f9])).
% 1.40/0.55  fof(f9,conjecture,(
% 1.40/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).
% 1.40/0.55  fof(f36,plain,(
% 1.40/0.55    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 1.40/0.55    inference(cnf_transformation,[],[f22])).
% 1.40/0.55  fof(f22,plain,(
% 1.40/0.55    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.40/0.55    inference(flattening,[],[f21])).
% 1.40/0.55  fof(f21,plain,(
% 1.40/0.55    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.40/0.55    inference(ennf_transformation,[],[f8])).
% 1.40/0.55  fof(f8,axiom,(
% 1.40/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.40/0.55  fof(f25,plain,(
% 1.40/0.55    v1_funct_1(sK0)),
% 1.40/0.55    inference(cnf_transformation,[],[f12])).
% 1.40/0.55  fof(f24,plain,(
% 1.40/0.55    v1_relat_1(sK0)),
% 1.40/0.55    inference(cnf_transformation,[],[f12])).
% 1.40/0.55  fof(f445,plain,(
% 1.40/0.55    k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k1_relat_1(k2_funct_1(sK0))),
% 1.40/0.55    inference(forward_demodulation,[],[f442,f97])).
% 1.40/0.56  fof(f97,plain,(
% 1.40/0.56    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0)))),
% 1.40/0.56    inference(global_subsumption,[],[f24,f96])).
% 1.40/0.56  fof(f96,plain,(
% 1.40/0.56    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) | ~v1_relat_1(sK0)),
% 1.40/0.56    inference(forward_demodulation,[],[f94,f56])).
% 1.40/0.56  fof(f56,plain,(
% 1.40/0.56    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 1.40/0.56    inference(global_subsumption,[],[f24,f25,f55])).
% 1.40/0.56  fof(f55,plain,(
% 1.40/0.56    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 1.40/0.56    inference(resolution,[],[f37,f26])).
% 1.40/0.56  fof(f37,plain,(
% 1.40/0.56    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 1.40/0.56    inference(cnf_transformation,[],[f22])).
% 1.40/0.56  fof(f94,plain,(
% 1.40/0.56    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) | ~v1_relat_1(sK0)),
% 1.40/0.56    inference(resolution,[],[f47,f25])).
% 1.40/0.56  fof(f47,plain,(
% 1.40/0.56    ( ! [X1] : (~v1_funct_1(X1) | k2_funct_1(X1) = k5_relat_1(k2_funct_1(X1),k6_relat_1(k2_relat_1(k2_funct_1(X1)))) | ~v1_relat_1(X1)) )),
% 1.40/0.56    inference(resolution,[],[f30,f34])).
% 1.40/0.56  fof(f34,plain,(
% 1.40/0.56    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f20])).
% 1.40/0.56  fof(f20,plain,(
% 1.40/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.40/0.56    inference(flattening,[],[f19])).
% 1.40/0.56  fof(f19,plain,(
% 1.40/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.40/0.56    inference(ennf_transformation,[],[f7])).
% 1.40/0.56  fof(f7,axiom,(
% 1.40/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.40/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.40/0.56  fof(f30,plain,(
% 1.40/0.56    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 1.40/0.56    inference(cnf_transformation,[],[f13])).
% 1.40/0.56  fof(f13,plain,(
% 1.40/0.56    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.40/0.56    inference(ennf_transformation,[],[f6])).
% 1.40/0.56  fof(f6,axiom,(
% 1.40/0.56    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.40/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 1.40/0.56  fof(f442,plain,(
% 1.40/0.56    k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))))),
% 1.40/0.56    inference(resolution,[],[f430,f24])).
% 1.40/0.56  fof(f430,plain,(
% 1.40/0.56    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(X0))))) )),
% 1.40/0.56    inference(global_subsumption,[],[f24,f424])).
% 1.40/0.56  fof(f424,plain,(
% 1.40/0.56    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(X0)))) | ~v1_relat_1(sK0)) )),
% 1.40/0.56    inference(resolution,[],[f413,f25])).
% 1.40/0.56  fof(f413,plain,(
% 1.40/0.56    ( ! [X4,X3] : (~v1_funct_1(X4) | ~v1_relat_1(X3) | k1_relat_1(k5_relat_1(k2_funct_1(X4),X3)) = k1_relat_1(k5_relat_1(k2_funct_1(X4),k6_relat_1(k1_relat_1(X3)))) | ~v1_relat_1(X4)) )),
% 1.40/0.56    inference(global_subsumption,[],[f293])).
% 1.40/0.56  fof(f293,plain,(
% 1.40/0.56    ( ! [X4,X3] : (~v1_relat_1(X3) | k1_relat_1(k5_relat_1(k2_funct_1(X4),X3)) = k1_relat_1(k5_relat_1(k2_funct_1(X4),k6_relat_1(k1_relat_1(X3)))) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) )),
% 1.40/0.56    inference(resolution,[],[f150,f34])).
% 1.40/0.56  fof(f150,plain,(
% 1.40/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(k5_relat_1(X0,k6_relat_1(k1_relat_1(X1))))) )),
% 1.40/0.56    inference(resolution,[],[f106,f27])).
% 1.40/0.56  fof(f27,plain,(
% 1.40/0.56    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.40/0.56    inference(cnf_transformation,[],[f1])).
% 1.40/0.56  fof(f1,axiom,(
% 1.40/0.56    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.40/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.40/0.56  fof(f106,plain,(
% 1.40/0.56    ( ! [X0,X1] : (~v1_relat_1(k6_relat_1(k1_relat_1(X0))) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(k5_relat_1(X1,k6_relat_1(k1_relat_1(X0))))) )),
% 1.40/0.56    inference(equality_resolution,[],[f57])).
% 1.40/0.56  fof(f57,plain,(
% 1.40/0.56    ( ! [X2,X0,X1] : (k1_relat_1(X1) != X0 | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(k6_relat_1(X0)) | k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(k5_relat_1(X2,k6_relat_1(X0)))) )),
% 1.40/0.56    inference(superposition,[],[f32,f28])).
% 1.40/0.56  fof(f28,plain,(
% 1.40/0.56    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.40/0.56    inference(cnf_transformation,[],[f4])).
% 1.40/0.56  fof(f4,axiom,(
% 1.40/0.56    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.40/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.40/0.56  fof(f32,plain,(
% 1.40/0.56    ( ! [X2,X0,X1] : (k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))) )),
% 1.40/0.56    inference(cnf_transformation,[],[f16])).
% 1.40/0.56  fof(f16,plain,(
% 1.40/0.56    ! [X0] : (! [X1] : (! [X2] : (k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.40/0.56    inference(flattening,[],[f15])).
% 1.40/0.56  fof(f15,plain,(
% 1.40/0.56    ! [X0] : (! [X1] : (! [X2] : ((k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.40/0.56    inference(ennf_transformation,[],[f2])).
% 1.40/0.56  fof(f2,axiom,(
% 1.40/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k1_relat_1(X0) = k1_relat_1(X1) => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))))))),
% 1.40/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_relat_1)).
% 1.40/0.56  fof(f43,plain,(
% 1.40/0.56    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | spl1_2),
% 1.40/0.56    inference(avatar_component_clause,[],[f42])).
% 1.40/0.56  fof(f42,plain,(
% 1.40/0.56    spl1_2 <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 1.40/0.56  fof(f219,plain,(
% 1.40/0.56    spl1_1 | ~spl1_13),
% 1.40/0.56    inference(avatar_contradiction_clause,[],[f218])).
% 1.40/0.56  fof(f218,plain,(
% 1.40/0.56    $false | (spl1_1 | ~spl1_13)),
% 1.40/0.56    inference(trivial_inequality_removal,[],[f212])).
% 1.40/0.56  fof(f212,plain,(
% 1.40/0.56    k2_relat_1(sK0) != k2_relat_1(sK0) | (spl1_1 | ~spl1_13)),
% 1.40/0.56    inference(superposition,[],[f40,f211])).
% 1.40/0.56  fof(f211,plain,(
% 1.40/0.56    k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | ~spl1_13),
% 1.40/0.56    inference(forward_demodulation,[],[f208,f49])).
% 1.40/0.56  fof(f49,plain,(
% 1.40/0.56    sK0 = k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0)),
% 1.40/0.56    inference(resolution,[],[f31,f24])).
% 1.40/0.56  fof(f31,plain,(
% 1.40/0.56    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 1.40/0.56    inference(cnf_transformation,[],[f14])).
% 1.40/0.56  fof(f14,plain,(
% 1.40/0.56    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 1.40/0.56    inference(ennf_transformation,[],[f5])).
% 1.40/0.56  fof(f5,axiom,(
% 1.40/0.56    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 1.40/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 1.40/0.56  fof(f208,plain,(
% 1.40/0.56    k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0)) | ~spl1_13),
% 1.40/0.56    inference(resolution,[],[f138,f24])).
% 1.40/0.56  fof(f138,plain,(
% 1.40/0.56    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) = k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),X0))) ) | ~spl1_13),
% 1.40/0.56    inference(avatar_component_clause,[],[f137])).
% 1.40/0.56  fof(f137,plain,(
% 1.40/0.56    spl1_13 <=> ! [X0] : (k2_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) = k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),X0)) | ~v1_relat_1(X0))),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 1.40/0.56  fof(f40,plain,(
% 1.40/0.56    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | spl1_1),
% 1.40/0.56    inference(avatar_component_clause,[],[f39])).
% 1.40/0.56  fof(f39,plain,(
% 1.40/0.56    spl1_1 <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 1.40/0.56  fof(f175,plain,(
% 1.40/0.56    ~spl1_3 | spl1_13 | ~spl1_12),
% 1.40/0.56    inference(avatar_split_clause,[],[f172,f134,f137,f64])).
% 1.40/0.56  fof(f64,plain,(
% 1.40/0.56    spl1_3 <=> v1_relat_1(k2_funct_1(sK0))),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 1.40/0.56  fof(f134,plain,(
% 1.40/0.56    spl1_12 <=> v1_relat_1(k6_relat_1(k1_relat_1(sK0)))),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 1.40/0.56  fof(f172,plain,(
% 1.40/0.56    ( ! [X2] : (~v1_relat_1(k6_relat_1(k1_relat_1(sK0))) | ~v1_relat_1(X2) | ~v1_relat_1(k2_funct_1(sK0)) | k2_relat_1(k5_relat_1(k2_funct_1(sK0),X2)) = k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),X2))) )),
% 1.40/0.56    inference(superposition,[],[f117,f56])).
% 1.40/0.56  fof(f117,plain,(
% 1.40/0.56    ( ! [X0,X1] : (~v1_relat_1(k6_relat_1(k2_relat_1(X0))) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(X0)),X1))) )),
% 1.40/0.56    inference(equality_resolution,[],[f79])).
% 1.40/0.56  fof(f79,plain,(
% 1.40/0.56    ( ! [X2,X0,X1] : (k2_relat_1(X1) != X0 | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(k6_relat_1(X0)) | k2_relat_1(k5_relat_1(X1,X2)) = k2_relat_1(k5_relat_1(k6_relat_1(X0),X2))) )),
% 1.40/0.56    inference(superposition,[],[f33,f29])).
% 1.40/0.56  fof(f29,plain,(
% 1.40/0.56    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.40/0.56    inference(cnf_transformation,[],[f4])).
% 1.40/0.56  fof(f33,plain,(
% 1.40/0.56    ( ! [X2,X0,X1] : (k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))) )),
% 1.40/0.56    inference(cnf_transformation,[],[f18])).
% 1.40/0.56  fof(f18,plain,(
% 1.40/0.56    ! [X0] : (! [X1] : (! [X2] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.40/0.56    inference(flattening,[],[f17])).
% 1.40/0.56  fof(f17,plain,(
% 1.40/0.56    ! [X0] : (! [X1] : (! [X2] : ((k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.40/0.56    inference(ennf_transformation,[],[f3])).
% 1.40/0.56  fof(f3,axiom,(
% 1.40/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k2_relat_1(X0) = k2_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))))))),
% 1.40/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_relat_1)).
% 1.40/0.56  fof(f141,plain,(
% 1.40/0.56    spl1_12),
% 1.40/0.56    inference(avatar_contradiction_clause,[],[f140])).
% 1.40/0.56  fof(f140,plain,(
% 1.40/0.56    $false | spl1_12),
% 1.40/0.56    inference(resolution,[],[f135,f27])).
% 1.40/0.56  fof(f135,plain,(
% 1.40/0.56    ~v1_relat_1(k6_relat_1(k1_relat_1(sK0))) | spl1_12),
% 1.40/0.56    inference(avatar_component_clause,[],[f134])).
% 1.40/0.56  fof(f88,plain,(
% 1.40/0.56    spl1_6),
% 1.40/0.56    inference(avatar_contradiction_clause,[],[f87])).
% 1.40/0.56  fof(f87,plain,(
% 1.40/0.56    $false | spl1_6),
% 1.40/0.56    inference(resolution,[],[f77,f25])).
% 1.40/0.56  fof(f77,plain,(
% 1.40/0.56    ~v1_funct_1(sK0) | spl1_6),
% 1.40/0.56    inference(avatar_component_clause,[],[f76])).
% 1.40/0.56  fof(f76,plain,(
% 1.40/0.56    spl1_6 <=> v1_funct_1(sK0)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 1.40/0.56  fof(f86,plain,(
% 1.40/0.56    spl1_5),
% 1.40/0.56    inference(avatar_contradiction_clause,[],[f85])).
% 1.40/0.56  fof(f85,plain,(
% 1.40/0.56    $false | spl1_5),
% 1.40/0.56    inference(resolution,[],[f74,f24])).
% 1.40/0.56  fof(f74,plain,(
% 1.40/0.56    ~v1_relat_1(sK0) | spl1_5),
% 1.40/0.56    inference(avatar_component_clause,[],[f73])).
% 1.40/0.56  fof(f73,plain,(
% 1.40/0.56    spl1_5 <=> v1_relat_1(sK0)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 1.40/0.56  fof(f78,plain,(
% 1.40/0.56    ~spl1_5 | ~spl1_6 | spl1_3),
% 1.40/0.56    inference(avatar_split_clause,[],[f71,f64,f76,f73])).
% 1.40/0.56  fof(f71,plain,(
% 1.40/0.56    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_3),
% 1.40/0.56    inference(resolution,[],[f65,f34])).
% 1.40/0.56  fof(f65,plain,(
% 1.40/0.56    ~v1_relat_1(k2_funct_1(sK0)) | spl1_3),
% 1.40/0.56    inference(avatar_component_clause,[],[f64])).
% 1.40/0.56  fof(f44,plain,(
% 1.40/0.56    ~spl1_1 | ~spl1_2),
% 1.40/0.56    inference(avatar_split_clause,[],[f23,f42,f39])).
% 1.40/0.56  fof(f23,plain,(
% 1.40/0.56    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 1.40/0.56    inference(cnf_transformation,[],[f12])).
% 1.40/0.56  % SZS output end Proof for theBenchmark
% 1.40/0.56  % (30438)------------------------------
% 1.40/0.56  % (30438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (30438)Termination reason: Refutation
% 1.40/0.56  
% 1.40/0.56  % (30438)Memory used [KB]: 11129
% 1.40/0.56  % (30438)Time elapsed: 0.128 s
% 1.40/0.56  % (30438)------------------------------
% 1.40/0.56  % (30438)------------------------------
% 1.40/0.56  % (30442)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.40/0.56  % (30425)Success in time 0.179 s
%------------------------------------------------------------------------------
