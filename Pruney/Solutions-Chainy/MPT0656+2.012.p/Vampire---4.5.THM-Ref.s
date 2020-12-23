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
% DateTime   : Thu Dec  3 12:53:03 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 553 expanded)
%              Number of leaves         :   16 ( 177 expanded)
%              Depth                    :   20
%              Number of atoms          :  340 (3736 expanded)
%              Number of equality atoms :   98 (1382 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f645,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f100,f114,f118,f644])).

fof(f644,plain,
    ( ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f643])).

fof(f643,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f642,f103])).

fof(f103,plain,(
    sK1 != k4_relat_1(sK0) ),
    inference(superposition,[],[f37,f61])).

fof(f61,plain,(
    k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f60,f30])).

fof(f30,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( k2_funct_1(sK0) != sK1
    & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1)
    & k2_relat_1(sK0) = k1_relat_1(sK1)
    & v2_funct_1(sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f28,f27])).

fof(f27,plain,
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
          & k1_relat_1(X1) = k2_relat_1(sK0)
          & v2_funct_1(sK0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( k2_funct_1(sK0) != X1
        & k5_relat_1(sK0,X1) = k6_relat_1(k1_relat_1(sK0))
        & k1_relat_1(X1) = k2_relat_1(sK0)
        & v2_funct_1(sK0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_funct_1(sK0) != sK1
      & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1)
      & k2_relat_1(sK0) = k1_relat_1(sK1)
      & v2_funct_1(sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

fof(f60,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f55,f31])).

fof(f31,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f55,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f34,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f34,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f37,plain,(
    k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f29])).

fof(f642,plain,
    ( sK1 = k4_relat_1(sK0)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f641,f102])).

fof(f102,plain,(
    sK1 = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) ),
    inference(subsumption_resolution,[],[f101,f32])).

fof(f32,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f101,plain,
    ( sK1 = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f47,f35])).

fof(f35,plain,(
    k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f47,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f641,plain,
    ( k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f640,f497])).

fof(f497,plain,
    ( k4_relat_1(sK0) = k8_relat_1(k1_relat_1(sK0),k4_relat_1(sK0))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f495,f75])).

fof(f75,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl2_1
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f495,plain,
    ( k4_relat_1(sK0) = k8_relat_1(k1_relat_1(sK0),k4_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(superposition,[],[f355,f48])).

fof(f48,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).

fof(f355,plain,
    ( k8_relat_1(k2_relat_1(k4_relat_1(sK0)),k4_relat_1(sK0)) = k8_relat_1(k1_relat_1(sK0),k4_relat_1(sK0))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f349,f125])).

fof(f125,plain,
    ( ! [X0] : k8_relat_1(X0,k4_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(X0))
    | ~ spl2_1 ),
    inference(resolution,[],[f75,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f349,plain,
    ( k8_relat_1(k2_relat_1(k4_relat_1(sK0)),k4_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k1_relat_1(sK0)))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(superposition,[],[f125,f340])).

fof(f340,plain,
    ( k6_relat_1(k1_relat_1(sK0)) = k6_relat_1(k2_relat_1(k4_relat_1(sK0)))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f339,f50])).

fof(f50,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(f339,plain,
    ( k6_relat_1(k2_relat_1(k4_relat_1(sK0))) = k4_relat_1(k6_relat_1(k1_relat_1(sK0)))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f338,f65])).

fof(f65,plain,(
    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k4_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f64,f61])).

fof(f64,plain,(
    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f63,f30])).

fof(f63,plain,
    ( k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f56,f31])).

fof(f56,plain,
    ( k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f34,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f338,plain,
    ( k6_relat_1(k2_relat_1(k4_relat_1(sK0))) = k4_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f337,f30])).

fof(f337,plain,
    ( k6_relat_1(k2_relat_1(k4_relat_1(sK0))) = k4_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | ~ v1_relat_1(sK0)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f334,f75])).

fof(f334,plain,
    ( k6_relat_1(k2_relat_1(k4_relat_1(sK0))) = k4_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(superposition,[],[f120,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f120,plain,
    ( k6_relat_1(k2_relat_1(k4_relat_1(sK0))) = k5_relat_1(k4_relat_1(k4_relat_1(sK0)),k4_relat_1(sK0))
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(backward_demodulation,[],[f99,f89])).

fof(f89,plain,
    ( k2_funct_1(k4_relat_1(sK0)) = k4_relat_1(k4_relat_1(sK0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl2_4
  <=> k2_funct_1(k4_relat_1(sK0)) = k4_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f99,plain,
    ( k5_relat_1(k2_funct_1(k4_relat_1(sK0)),k4_relat_1(sK0)) = k6_relat_1(k2_relat_1(k4_relat_1(sK0)))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl2_6
  <=> k5_relat_1(k2_funct_1(k4_relat_1(sK0)),k4_relat_1(sK0)) = k6_relat_1(k2_relat_1(k4_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f640,plain,
    ( k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) = k8_relat_1(k1_relat_1(sK0),k4_relat_1(sK0))
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f639,f125])).

fof(f639,plain,
    ( k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k1_relat_1(sK0)))
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f634,f36])).

fof(f36,plain,(
    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f634,plain,
    ( k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1))
    | ~ spl2_1 ),
    inference(resolution,[],[f223,f32])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X0)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) )
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f222,f75])).

fof(f222,plain,(
    ! [X0] :
      ( k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X0)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k4_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f221,f30])).

fof(f221,plain,(
    ! [X0] :
      ( k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X0)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK0)
      | ~ v1_relat_1(k4_relat_1(sK0)) ) ),
    inference(superposition,[],[f46,f68])).

fof(f68,plain,(
    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),sK0) ),
    inference(forward_demodulation,[],[f67,f61])).

fof(f67,plain,(
    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f66,f30])).

fof(f66,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f57,f31])).

fof(f57,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f34,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f118,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f117,f74])).

fof(f117,plain,(
    v1_relat_1(k4_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f116,f30])).

fof(f116,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f115,f31])).

fof(f115,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f104,f34])).

fof(f104,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f41,f61])).

fof(f41,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f114,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f113,f78])).

fof(f78,plain,
    ( spl2_2
  <=> v1_funct_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f113,plain,(
    v1_funct_1(k4_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f112,f30])).

fof(f112,plain,
    ( v1_funct_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f111,f31])).

% (4407)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f111,plain,
    ( v1_funct_1(k4_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f105,f34])).

fof(f105,plain,
    ( v1_funct_1(k4_relat_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f42,f61])).

fof(f42,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f100,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | spl2_6 ),
    inference(avatar_split_clause,[],[f72,f97,f78,f74])).

fof(f72,plain,
    ( k5_relat_1(k2_funct_1(k4_relat_1(sK0)),k4_relat_1(sK0)) = k6_relat_1(k2_relat_1(k4_relat_1(sK0)))
    | ~ v1_funct_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f62,f39])).

fof(f62,plain,(
    v2_funct_1(k4_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f59,f61])).

fof(f59,plain,(
    v2_funct_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f58,f30])).

fof(f58,plain,
    ( v2_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f54,f31])).

fof(f54,plain,
    ( v2_funct_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f34,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | v2_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f90,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | spl2_4 ),
    inference(avatar_split_clause,[],[f70,f87,f78,f74])).

fof(f70,plain,
    ( k2_funct_1(k4_relat_1(sK0)) = k4_relat_1(k4_relat_1(sK0))
    | ~ v1_funct_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f62,f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n008.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 12:51:15 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.56  % (4411)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.23/0.57  % (4412)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.23/0.58  % (4413)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.23/0.58  % (4414)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.23/0.58  % (4426)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.23/0.58  % (4409)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.23/0.58  % (4410)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.23/0.58  % (4427)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.23/0.59  % (4429)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.23/0.59  % (4419)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.23/0.59  % (4430)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.23/0.59  % (4417)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.23/0.59  % (4420)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.23/0.59  % (4418)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.23/0.59  % (4428)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.23/0.59  % (4421)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.59  % (4425)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.23/0.61  % (4422)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.23/0.62  % (4413)Refutation found. Thanks to Tanya!
% 0.23/0.62  % SZS status Theorem for theBenchmark
% 0.23/0.62  % SZS output start Proof for theBenchmark
% 0.23/0.62  fof(f645,plain,(
% 0.23/0.62    $false),
% 0.23/0.62    inference(avatar_sat_refutation,[],[f90,f100,f114,f118,f644])).
% 0.23/0.62  fof(f644,plain,(
% 0.23/0.62    ~spl2_1 | ~spl2_4 | ~spl2_6),
% 0.23/0.62    inference(avatar_contradiction_clause,[],[f643])).
% 0.23/0.62  fof(f643,plain,(
% 0.23/0.62    $false | (~spl2_1 | ~spl2_4 | ~spl2_6)),
% 0.23/0.62    inference(subsumption_resolution,[],[f642,f103])).
% 0.23/0.62  fof(f103,plain,(
% 0.23/0.62    sK1 != k4_relat_1(sK0)),
% 0.23/0.62    inference(superposition,[],[f37,f61])).
% 0.23/0.62  fof(f61,plain,(
% 0.23/0.62    k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.23/0.62    inference(subsumption_resolution,[],[f60,f30])).
% 0.23/0.62  fof(f30,plain,(
% 0.23/0.62    v1_relat_1(sK0)),
% 0.23/0.62    inference(cnf_transformation,[],[f29])).
% 0.23/0.62  fof(f29,plain,(
% 0.23/0.62    (k2_funct_1(sK0) != sK1 & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) & k2_relat_1(sK0) = k1_relat_1(sK1) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.23/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f28,f27])).
% 0.23/0.62  fof(f27,plain,(
% 0.23/0.62    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k2_funct_1(sK0) != X1 & k5_relat_1(sK0,X1) = k6_relat_1(k1_relat_1(sK0)) & k1_relat_1(X1) = k2_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.23/0.62    introduced(choice_axiom,[])).
% 0.23/0.62  fof(f28,plain,(
% 0.23/0.62    ? [X1] : (k2_funct_1(sK0) != X1 & k5_relat_1(sK0,X1) = k6_relat_1(k1_relat_1(sK0)) & k1_relat_1(X1) = k2_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(sK0) != sK1 & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) & k2_relat_1(sK0) = k1_relat_1(sK1) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.23/0.62    introduced(choice_axiom,[])).
% 0.23/0.62  fof(f15,plain,(
% 0.23/0.62    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.23/0.62    inference(flattening,[],[f14])).
% 0.23/0.62  fof(f14,plain,(
% 0.23/0.62    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.23/0.62    inference(ennf_transformation,[],[f13])).
% 0.23/0.62  fof(f13,negated_conjecture,(
% 0.23/0.62    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.23/0.62    inference(negated_conjecture,[],[f12])).
% 0.23/0.62  fof(f12,conjecture,(
% 0.23/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.23/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).
% 0.23/0.62  fof(f60,plain,(
% 0.23/0.62    k2_funct_1(sK0) = k4_relat_1(sK0) | ~v1_relat_1(sK0)),
% 0.23/0.62    inference(subsumption_resolution,[],[f55,f31])).
% 0.23/0.62  fof(f31,plain,(
% 0.23/0.62    v1_funct_1(sK0)),
% 0.23/0.62    inference(cnf_transformation,[],[f29])).
% 0.23/0.62  fof(f55,plain,(
% 0.23/0.62    k2_funct_1(sK0) = k4_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.23/0.62    inference(resolution,[],[f34,f40])).
% 0.23/0.62  fof(f40,plain,(
% 0.23/0.62    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.23/0.62    inference(cnf_transformation,[],[f19])).
% 0.23/0.62  fof(f19,plain,(
% 0.23/0.62    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.23/0.62    inference(flattening,[],[f18])).
% 0.23/0.62  fof(f18,plain,(
% 0.23/0.62    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.23/0.62    inference(ennf_transformation,[],[f8])).
% 0.23/0.62  fof(f8,axiom,(
% 0.23/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.23/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.23/0.62  fof(f34,plain,(
% 0.23/0.62    v2_funct_1(sK0)),
% 0.23/0.62    inference(cnf_transformation,[],[f29])).
% 0.23/0.62  fof(f37,plain,(
% 0.23/0.62    k2_funct_1(sK0) != sK1),
% 0.23/0.62    inference(cnf_transformation,[],[f29])).
% 0.23/0.62  fof(f642,plain,(
% 0.23/0.62    sK1 = k4_relat_1(sK0) | (~spl2_1 | ~spl2_4 | ~spl2_6)),
% 0.23/0.62    inference(forward_demodulation,[],[f641,f102])).
% 0.23/0.62  fof(f102,plain,(
% 0.23/0.62    sK1 = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1)),
% 0.23/0.62    inference(subsumption_resolution,[],[f101,f32])).
% 0.23/0.62  fof(f32,plain,(
% 0.23/0.62    v1_relat_1(sK1)),
% 0.23/0.62    inference(cnf_transformation,[],[f29])).
% 0.23/0.62  fof(f101,plain,(
% 0.23/0.62    sK1 = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) | ~v1_relat_1(sK1)),
% 0.23/0.62    inference(superposition,[],[f47,f35])).
% 0.23/0.62  fof(f35,plain,(
% 0.23/0.62    k2_relat_1(sK0) = k1_relat_1(sK1)),
% 0.23/0.62    inference(cnf_transformation,[],[f29])).
% 0.23/0.62  fof(f47,plain,(
% 0.23/0.62    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 0.23/0.62    inference(cnf_transformation,[],[f23])).
% 0.23/0.62  fof(f23,plain,(
% 0.23/0.62    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.23/0.62    inference(ennf_transformation,[],[f7])).
% 0.23/0.62  fof(f7,axiom,(
% 0.23/0.62    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.23/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 0.23/0.62  fof(f641,plain,(
% 0.23/0.62    k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) | (~spl2_1 | ~spl2_4 | ~spl2_6)),
% 0.23/0.62    inference(forward_demodulation,[],[f640,f497])).
% 0.23/0.62  fof(f497,plain,(
% 0.23/0.62    k4_relat_1(sK0) = k8_relat_1(k1_relat_1(sK0),k4_relat_1(sK0)) | (~spl2_1 | ~spl2_4 | ~spl2_6)),
% 0.23/0.62    inference(subsumption_resolution,[],[f495,f75])).
% 0.23/0.62  fof(f75,plain,(
% 0.23/0.62    v1_relat_1(k4_relat_1(sK0)) | ~spl2_1),
% 0.23/0.62    inference(avatar_component_clause,[],[f74])).
% 0.23/0.62  fof(f74,plain,(
% 0.23/0.62    spl2_1 <=> v1_relat_1(k4_relat_1(sK0))),
% 0.23/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.23/0.62  fof(f495,plain,(
% 0.23/0.62    k4_relat_1(sK0) = k8_relat_1(k1_relat_1(sK0),k4_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0)) | (~spl2_1 | ~spl2_4 | ~spl2_6)),
% 0.23/0.62    inference(superposition,[],[f355,f48])).
% 0.23/0.62  fof(f48,plain,(
% 0.23/0.62    ( ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0)) )),
% 0.23/0.62    inference(cnf_transformation,[],[f24])).
% 0.23/0.62  fof(f24,plain,(
% 0.23/0.62    ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0))),
% 0.23/0.62    inference(ennf_transformation,[],[f3])).
% 0.23/0.62  fof(f3,axiom,(
% 0.23/0.62    ! [X0] : (v1_relat_1(X0) => k8_relat_1(k2_relat_1(X0),X0) = X0)),
% 0.23/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).
% 0.23/0.62  fof(f355,plain,(
% 0.23/0.62    k8_relat_1(k2_relat_1(k4_relat_1(sK0)),k4_relat_1(sK0)) = k8_relat_1(k1_relat_1(sK0),k4_relat_1(sK0)) | (~spl2_1 | ~spl2_4 | ~spl2_6)),
% 0.23/0.62    inference(forward_demodulation,[],[f349,f125])).
% 0.23/0.62  fof(f125,plain,(
% 0.23/0.62    ( ! [X0] : (k8_relat_1(X0,k4_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(X0))) ) | ~spl2_1),
% 0.23/0.62    inference(resolution,[],[f75,f51])).
% 0.23/0.62  fof(f51,plain,(
% 0.23/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.23/0.62    inference(cnf_transformation,[],[f26])).
% 0.23/0.62  fof(f26,plain,(
% 0.23/0.62    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.23/0.62    inference(ennf_transformation,[],[f2])).
% 0.23/0.62  fof(f2,axiom,(
% 0.23/0.62    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.23/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.23/0.62  fof(f349,plain,(
% 0.23/0.62    k8_relat_1(k2_relat_1(k4_relat_1(sK0)),k4_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k1_relat_1(sK0))) | (~spl2_1 | ~spl2_4 | ~spl2_6)),
% 0.23/0.62    inference(superposition,[],[f125,f340])).
% 0.23/0.62  fof(f340,plain,(
% 0.23/0.62    k6_relat_1(k1_relat_1(sK0)) = k6_relat_1(k2_relat_1(k4_relat_1(sK0))) | (~spl2_1 | ~spl2_4 | ~spl2_6)),
% 0.23/0.62    inference(forward_demodulation,[],[f339,f50])).
% 0.23/0.62  fof(f50,plain,(
% 0.23/0.62    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 0.23/0.62    inference(cnf_transformation,[],[f6])).
% 0.23/0.62  fof(f6,axiom,(
% 0.23/0.62    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 0.23/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).
% 0.23/0.62  fof(f339,plain,(
% 0.23/0.62    k6_relat_1(k2_relat_1(k4_relat_1(sK0))) = k4_relat_1(k6_relat_1(k1_relat_1(sK0))) | (~spl2_1 | ~spl2_4 | ~spl2_6)),
% 0.23/0.62    inference(forward_demodulation,[],[f338,f65])).
% 0.23/0.62  fof(f65,plain,(
% 0.23/0.62    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k4_relat_1(sK0))),
% 0.23/0.62    inference(forward_demodulation,[],[f64,f61])).
% 0.23/0.62  fof(f64,plain,(
% 0.23/0.62    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0))),
% 0.23/0.62    inference(subsumption_resolution,[],[f63,f30])).
% 0.23/0.63  fof(f63,plain,(
% 0.23/0.63    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0)) | ~v1_relat_1(sK0)),
% 0.23/0.63    inference(subsumption_resolution,[],[f56,f31])).
% 0.23/0.63  fof(f56,plain,(
% 0.23/0.63    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.23/0.63    inference(resolution,[],[f34,f38])).
% 0.23/0.63  fof(f38,plain,(
% 0.23/0.63    ( ! [X0] : (~v2_funct_1(X0) | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.23/0.63    inference(cnf_transformation,[],[f17])).
% 0.23/0.63  fof(f17,plain,(
% 0.23/0.63    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.23/0.63    inference(flattening,[],[f16])).
% 0.23/0.63  fof(f16,plain,(
% 0.23/0.63    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.23/0.63    inference(ennf_transformation,[],[f11])).
% 0.23/0.63  fof(f11,axiom,(
% 0.23/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 0.23/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.23/0.63  fof(f338,plain,(
% 0.23/0.63    k6_relat_1(k2_relat_1(k4_relat_1(sK0))) = k4_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | (~spl2_1 | ~spl2_4 | ~spl2_6)),
% 0.23/0.63    inference(subsumption_resolution,[],[f337,f30])).
% 0.23/0.63  fof(f337,plain,(
% 0.23/0.63    k6_relat_1(k2_relat_1(k4_relat_1(sK0))) = k4_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | ~v1_relat_1(sK0) | (~spl2_1 | ~spl2_4 | ~spl2_6)),
% 0.23/0.63    inference(subsumption_resolution,[],[f334,f75])).
% 0.23/0.63  fof(f334,plain,(
% 0.23/0.63    k6_relat_1(k2_relat_1(k4_relat_1(sK0))) = k4_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | ~v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl2_4 | ~spl2_6)),
% 0.23/0.63    inference(superposition,[],[f120,f49])).
% 0.23/0.63  fof(f49,plain,(
% 0.23/0.63    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.23/0.63    inference(cnf_transformation,[],[f25])).
% 0.23/0.63  fof(f25,plain,(
% 0.23/0.63    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.23/0.63    inference(ennf_transformation,[],[f4])).
% 0.23/0.63  fof(f4,axiom,(
% 0.23/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.23/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 0.23/0.63  fof(f120,plain,(
% 0.23/0.63    k6_relat_1(k2_relat_1(k4_relat_1(sK0))) = k5_relat_1(k4_relat_1(k4_relat_1(sK0)),k4_relat_1(sK0)) | (~spl2_4 | ~spl2_6)),
% 0.23/0.63    inference(backward_demodulation,[],[f99,f89])).
% 0.23/0.63  fof(f89,plain,(
% 0.23/0.63    k2_funct_1(k4_relat_1(sK0)) = k4_relat_1(k4_relat_1(sK0)) | ~spl2_4),
% 0.23/0.63    inference(avatar_component_clause,[],[f87])).
% 0.23/0.63  fof(f87,plain,(
% 0.23/0.63    spl2_4 <=> k2_funct_1(k4_relat_1(sK0)) = k4_relat_1(k4_relat_1(sK0))),
% 0.23/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.23/0.63  fof(f99,plain,(
% 0.23/0.63    k5_relat_1(k2_funct_1(k4_relat_1(sK0)),k4_relat_1(sK0)) = k6_relat_1(k2_relat_1(k4_relat_1(sK0))) | ~spl2_6),
% 0.23/0.63    inference(avatar_component_clause,[],[f97])).
% 0.23/0.63  fof(f97,plain,(
% 0.23/0.63    spl2_6 <=> k5_relat_1(k2_funct_1(k4_relat_1(sK0)),k4_relat_1(sK0)) = k6_relat_1(k2_relat_1(k4_relat_1(sK0)))),
% 0.23/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.23/0.63  fof(f640,plain,(
% 0.23/0.63    k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) = k8_relat_1(k1_relat_1(sK0),k4_relat_1(sK0)) | ~spl2_1),
% 0.23/0.63    inference(forward_demodulation,[],[f639,f125])).
% 0.23/0.63  fof(f639,plain,(
% 0.23/0.63    k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k1_relat_1(sK0))) | ~spl2_1),
% 0.23/0.63    inference(forward_demodulation,[],[f634,f36])).
% 0.23/0.63  fof(f36,plain,(
% 0.23/0.63    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1)),
% 0.23/0.63    inference(cnf_transformation,[],[f29])).
% 0.23/0.63  fof(f634,plain,(
% 0.23/0.63    k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1)) | ~spl2_1),
% 0.23/0.63    inference(resolution,[],[f223,f32])).
% 0.23/0.63  fof(f223,plain,(
% 0.23/0.63    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X0)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)) ) | ~spl2_1),
% 0.23/0.63    inference(subsumption_resolution,[],[f222,f75])).
% 0.23/0.63  fof(f222,plain,(
% 0.23/0.63    ( ! [X0] : (k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X0)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) | ~v1_relat_1(X0) | ~v1_relat_1(k4_relat_1(sK0))) )),
% 0.23/0.63    inference(subsumption_resolution,[],[f221,f30])).
% 0.23/0.63  fof(f221,plain,(
% 0.23/0.63    ( ! [X0] : (k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X0)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK0) | ~v1_relat_1(k4_relat_1(sK0))) )),
% 0.23/0.63    inference(superposition,[],[f46,f68])).
% 0.23/0.63  fof(f68,plain,(
% 0.23/0.63    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),sK0)),
% 0.23/0.63    inference(forward_demodulation,[],[f67,f61])).
% 0.23/0.63  fof(f67,plain,(
% 0.23/0.63    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))),
% 0.23/0.63    inference(subsumption_resolution,[],[f66,f30])).
% 0.23/0.63  fof(f66,plain,(
% 0.23/0.63    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) | ~v1_relat_1(sK0)),
% 0.23/0.63    inference(subsumption_resolution,[],[f57,f31])).
% 0.23/0.63  fof(f57,plain,(
% 0.23/0.63    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.23/0.63    inference(resolution,[],[f34,f39])).
% 0.23/0.63  fof(f39,plain,(
% 0.23/0.63    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.23/0.63    inference(cnf_transformation,[],[f17])).
% 0.23/0.63  fof(f46,plain,(
% 0.23/0.63    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.23/0.63    inference(cnf_transformation,[],[f22])).
% 0.23/0.63  fof(f22,plain,(
% 0.23/0.63    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.23/0.63    inference(ennf_transformation,[],[f5])).
% 0.23/0.63  fof(f5,axiom,(
% 0.23/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.23/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 0.23/0.63  fof(f118,plain,(
% 0.23/0.63    spl2_1),
% 0.23/0.63    inference(avatar_split_clause,[],[f117,f74])).
% 0.23/0.63  fof(f117,plain,(
% 0.23/0.63    v1_relat_1(k4_relat_1(sK0))),
% 0.23/0.63    inference(subsumption_resolution,[],[f116,f30])).
% 0.23/0.63  fof(f116,plain,(
% 0.23/0.63    v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(sK0)),
% 0.23/0.63    inference(subsumption_resolution,[],[f115,f31])).
% 0.23/0.63  fof(f115,plain,(
% 0.23/0.63    v1_relat_1(k4_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.23/0.63    inference(subsumption_resolution,[],[f104,f34])).
% 0.23/0.63  fof(f104,plain,(
% 0.23/0.63    v1_relat_1(k4_relat_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.23/0.63    inference(superposition,[],[f41,f61])).
% 0.23/0.63  fof(f41,plain,(
% 0.23/0.63    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.23/0.63    inference(cnf_transformation,[],[f21])).
% 0.23/0.63  fof(f21,plain,(
% 0.23/0.63    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.23/0.63    inference(flattening,[],[f20])).
% 0.23/0.63  fof(f20,plain,(
% 0.23/0.63    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.23/0.63    inference(ennf_transformation,[],[f10])).
% 0.23/0.63  fof(f10,axiom,(
% 0.23/0.63    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.23/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.23/0.63  fof(f114,plain,(
% 0.23/0.63    spl2_2),
% 0.23/0.63    inference(avatar_split_clause,[],[f113,f78])).
% 0.23/0.63  fof(f78,plain,(
% 0.23/0.63    spl2_2 <=> v1_funct_1(k4_relat_1(sK0))),
% 0.23/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.23/0.63  fof(f113,plain,(
% 0.23/0.63    v1_funct_1(k4_relat_1(sK0))),
% 0.23/0.63    inference(subsumption_resolution,[],[f112,f30])).
% 0.23/0.63  fof(f112,plain,(
% 0.23/0.63    v1_funct_1(k4_relat_1(sK0)) | ~v1_relat_1(sK0)),
% 0.23/0.63    inference(subsumption_resolution,[],[f111,f31])).
% 0.23/0.64  % (4407)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.23/0.64  fof(f111,plain,(
% 0.23/0.64    v1_funct_1(k4_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.23/0.64    inference(subsumption_resolution,[],[f105,f34])).
% 0.23/0.64  fof(f105,plain,(
% 0.23/0.64    v1_funct_1(k4_relat_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.23/0.64    inference(superposition,[],[f42,f61])).
% 0.23/0.64  fof(f42,plain,(
% 0.23/0.64    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.23/0.64    inference(cnf_transformation,[],[f21])).
% 0.23/0.64  fof(f100,plain,(
% 0.23/0.64    ~spl2_1 | ~spl2_2 | spl2_6),
% 0.23/0.64    inference(avatar_split_clause,[],[f72,f97,f78,f74])).
% 0.23/0.64  fof(f72,plain,(
% 0.23/0.64    k5_relat_1(k2_funct_1(k4_relat_1(sK0)),k4_relat_1(sK0)) = k6_relat_1(k2_relat_1(k4_relat_1(sK0))) | ~v1_funct_1(k4_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0))),
% 0.23/0.64    inference(resolution,[],[f62,f39])).
% 0.23/0.64  fof(f62,plain,(
% 0.23/0.64    v2_funct_1(k4_relat_1(sK0))),
% 0.23/0.64    inference(backward_demodulation,[],[f59,f61])).
% 0.23/0.64  fof(f59,plain,(
% 0.23/0.64    v2_funct_1(k2_funct_1(sK0))),
% 0.23/0.64    inference(subsumption_resolution,[],[f58,f30])).
% 0.23/0.64  fof(f58,plain,(
% 0.23/0.64    v2_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0)),
% 0.23/0.64    inference(subsumption_resolution,[],[f54,f31])).
% 0.23/0.64  fof(f54,plain,(
% 0.23/0.64    v2_funct_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.23/0.64    inference(resolution,[],[f34,f43])).
% 0.23/0.64  fof(f43,plain,(
% 0.23/0.64    ( ! [X0] : (~v2_funct_1(X0) | v2_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.23/0.64    inference(cnf_transformation,[],[f21])).
% 0.23/0.64  fof(f90,plain,(
% 0.23/0.64    ~spl2_1 | ~spl2_2 | spl2_4),
% 0.23/0.64    inference(avatar_split_clause,[],[f70,f87,f78,f74])).
% 0.23/0.64  fof(f70,plain,(
% 0.23/0.64    k2_funct_1(k4_relat_1(sK0)) = k4_relat_1(k4_relat_1(sK0)) | ~v1_funct_1(k4_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0))),
% 0.23/0.64    inference(resolution,[],[f62,f40])).
% 0.23/0.64  % SZS output end Proof for theBenchmark
% 0.23/0.64  % (4413)------------------------------
% 0.23/0.64  % (4413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.64  % (4413)Termination reason: Refutation
% 0.23/0.64  
% 0.23/0.64  % (4413)Memory used [KB]: 11001
% 0.23/0.64  % (4413)Time elapsed: 0.178 s
% 0.23/0.64  % (4413)------------------------------
% 0.23/0.64  % (4413)------------------------------
% 0.23/0.64  % (4406)Success in time 0.258 s
%------------------------------------------------------------------------------
