%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t63_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:26 EDT 2019

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 187 expanded)
%              Number of leaves         :    9 (  58 expanded)
%              Depth                    :   19
%              Number of atoms          :  272 (1381 expanded)
%              Number of equality atoms :   93 ( 525 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f108,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f107])).

fof(f107,plain,(
    ~ spl2_0 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | ~ spl2_0 ),
    inference(subsumption_resolution,[],[f105,f45])).

fof(f45,plain,(
    v1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f44,f26])).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k2_funct_1(sK0) != sK1
    & k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0))
    & k2_relat_1(sK0) = k1_relat_1(sK1)
    & v2_funct_1(sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_funct_1(X0) != X1
            & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & k2_relat_1(X0) = k1_relat_1(X1)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_funct_1(sK0) != X1
          & k5_relat_1(sK0,X1) = k6_relat_1(k1_relat_1(sK0))
          & k2_relat_1(sK0) = k1_relat_1(X1)
          & v2_funct_1(sK0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( k2_funct_1(X0) != sK1
        & k5_relat_1(X0,sK1) = k6_relat_1(k1_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(sK1)
        & v2_funct_1(X0)
        & v1_funct_1(sK1)
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
                & k2_relat_1(X0) = k1_relat_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t63_funct_1.p',t63_funct_1)).

fof(f44,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f27,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t63_funct_1.p',dt_k2_funct_1)).

fof(f27,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f105,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl2_0 ),
    inference(subsumption_resolution,[],[f104,f71])).

fof(f71,plain,
    ( v1_funct_1(k2_funct_1(sK0))
    | ~ spl2_0 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl2_0
  <=> v1_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_0])])).

fof(f104,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f103,f33])).

fof(f33,plain,(
    k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f103,plain,
    ( k2_funct_1(sK0) = sK1
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f102,f55])).

fof(f55,plain,(
    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f54,f26])).

fof(f54,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f49,f27])).

fof(f49,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f30,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t63_funct_1.p',t61_funct_1)).

fof(f30,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f102,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) != k6_relat_1(k2_relat_1(sK0))
    | k2_funct_1(sK0) = sK1
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0)) ),
    inference(trivial_inequality_removal,[],[f101])).

fof(f101,plain,
    ( k6_relat_1(k1_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK0))
    | k5_relat_1(k2_funct_1(sK0),sK0) != k6_relat_1(k2_relat_1(sK0))
    | k2_funct_1(sK0) = sK1
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0)) ),
    inference(superposition,[],[f66,f59])).

fof(f59,plain,(
    k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f58,f26])).

fof(f58,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f51,f27])).

fof(f51,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f30,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t63_funct_1.p',t55_funct_1)).

fof(f66,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(sK0)) != k6_relat_1(k2_relat_1(X0))
      | k5_relat_1(X0,sK0) != k6_relat_1(k2_relat_1(sK0))
      | sK1 = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f65,f31])).

fof(f31,plain,(
    k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(sK0)) != k6_relat_1(k2_relat_1(X0))
      | sK1 = X0
      | k5_relat_1(X0,sK0) != k6_relat_1(k1_relat_1(sK1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f64,f26])).

fof(f64,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(sK0)) != k6_relat_1(k2_relat_1(X0))
      | sK1 = X0
      | k5_relat_1(X0,sK0) != k6_relat_1(k1_relat_1(sK1))
      | ~ v1_relat_1(sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f63,f27])).

fof(f63,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(sK0)) != k6_relat_1(k2_relat_1(X0))
      | sK1 = X0
      | k5_relat_1(X0,sK0) != k6_relat_1(k1_relat_1(sK1))
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f62,f28])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f62,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(sK0)) != k6_relat_1(k2_relat_1(X0))
      | sK1 = X0
      | k5_relat_1(X0,sK0) != k6_relat_1(k1_relat_1(sK1))
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f61,f29])).

fof(f29,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f61,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(sK0)) != k6_relat_1(k2_relat_1(X0))
      | sK1 = X0
      | k5_relat_1(X0,sK0) != k6_relat_1(k1_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f43,f32])).

fof(f32,plain,(
    k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    ! [X2,X3,X1] :
      ( k5_relat_1(X2,X3) != k6_relat_1(k2_relat_1(X1))
      | X1 = X3
      | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | k5_relat_1(X2,X3) != k6_relat_1(X0)
      | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
      | k2_relat_1(X1) != X0
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/funct_1__t63_funct_1.p',l72_funct_1)).

fof(f82,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f81])).

fof(f81,plain,
    ( $false
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f80,f26])).

fof(f80,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f79,f27])).

fof(f79,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_1 ),
    inference(resolution,[],[f74,f36])).

fof(f36,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f74,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl2_1
  <=> ~ v1_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
%------------------------------------------------------------------------------
