%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t19_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:11 EDT 2019

% Result     : Theorem 1.09s
% Output     : Refutation 1.09s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 392 expanded)
%              Number of leaves         :   25 ( 100 expanded)
%              Depth                    :   20
%              Number of atoms          :  490 (1641 expanded)
%              Number of equality atoms :   38 ( 135 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10971,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f135,f905,f908,f9211,f10937,f10954,f10970])).

fof(f10970,plain,
    ( spl6_3
    | ~ spl6_18 ),
    inference(avatar_contradiction_clause,[],[f10969])).

fof(f10969,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f10968,f81])).

fof(f81,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,
    ( ( ~ r2_hidden(sK0,sK1)
      | ~ r2_hidden(sK0,k3_relat_1(sK2)) )
    & r2_hidden(sK0,k3_relat_1(k2_wellord1(sK2,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f45,f67])).

fof(f67,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X0,X1)
          | ~ r2_hidden(X0,k3_relat_1(X2)) )
        & r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(sK0,sK1)
        | ~ r2_hidden(sK0,k3_relat_1(sK2)) )
      & r2_hidden(sK0,k3_relat_1(k2_wellord1(sK2,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k3_relat_1(X2)) )
      & r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k3_relat_1(X2)) )
      & r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
         => ( r2_hidden(X0,X1)
            & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t19_wellord1.p',t19_wellord1)).

fof(f10968,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl6_3
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f10958,f134])).

fof(f134,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl6_3
  <=> ~ r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f10958,plain,
    ( r2_hidden(sK0,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl6_18 ),
    inference(resolution,[],[f901,f647])).

fof(f647,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_relat_1(k2_wellord1(X1,X0)))
      | r2_hidden(X2,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f642,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t19_wellord1.p',dt_k7_relat_1)).

fof(f642,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_relat_1(k2_wellord1(X1,X0)))
      | r2_hidden(X2,X0)
      | ~ v1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f242,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t19_wellord1.p',t18_wellord1)).

fof(f242,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_hidden(X9,k2_relat_1(k8_relat_1(X8,X7)))
      | r2_hidden(X9,X8)
      | ~ v1_relat_1(X7) ) ),
    inference(superposition,[],[f124,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t19_wellord1.p',t119_relat_1)).

fof(f124,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f73,f74])).

fof(f74,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t19_wellord1.p',d4_xboole_0)).

fof(f901,plain,
    ( r2_hidden(sK0,k2_relat_1(k2_wellord1(sK2,sK1)))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f900])).

fof(f900,plain,
    ( spl6_18
  <=> r2_hidden(sK0,k2_relat_1(k2_wellord1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f10954,plain,
    ( spl6_3
    | ~ spl6_20 ),
    inference(avatar_contradiction_clause,[],[f10953])).

fof(f10953,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f10952,f81])).

fof(f10952,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl6_3
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f10941,f134])).

fof(f10941,plain,
    ( r2_hidden(sK0,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl6_20 ),
    inference(resolution,[],[f904,f604])).

fof(f604,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(k2_wellord1(X1,X0)))
      | r2_hidden(X2,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f594,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t19_wellord1.p',dt_k8_relat_1)).

fof(f594,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(k2_wellord1(X1,X0)))
      | r2_hidden(X2,X0)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f230,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t19_wellord1.p',t17_wellord1)).

fof(f230,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_hidden(X9,k1_relat_1(k7_relat_1(X7,X8)))
      | r2_hidden(X9,X8)
      | ~ v1_relat_1(X7) ) ),
    inference(superposition,[],[f124,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t19_wellord1.p',t90_relat_1)).

fof(f904,plain,
    ( r2_hidden(sK0,k1_relat_1(k2_wellord1(sK2,sK1)))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f903])).

fof(f903,plain,
    ( spl6_20
  <=> r2_hidden(sK0,k1_relat_1(k2_wellord1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f10937,plain,
    ( spl6_1
    | ~ spl6_18 ),
    inference(avatar_contradiction_clause,[],[f10936])).

fof(f10936,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f10935,f81])).

fof(f10935,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl6_1
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f10930,f131])).

fof(f131,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(sK2))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl6_1
  <=> ~ r2_hidden(sK0,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f10930,plain,
    ( r2_hidden(sK0,k3_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_18 ),
    inference(resolution,[],[f10915,f207])).

fof(f207,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k2_relat_1(X2))
      | r2_hidden(X3,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f126,f88])).

fof(f88,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t19_wellord1.p',d6_relat_1)).

fof(f126,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f118])).

fof(f118,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & ~ r2_hidden(sK5(X0,X1,X2),X0) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( r2_hidden(sK5(X0,X1,X2),X1)
            | r2_hidden(sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f78,f79])).

fof(f79,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & ~ r2_hidden(sK5(X0,X1,X2),X0) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( r2_hidden(sK5(X0,X1,X2),X1)
          | r2_hidden(sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t19_wellord1.p',d3_xboole_0)).

fof(f10915,plain,
    ( r2_hidden(sK0,k2_relat_1(sK2))
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f10914,f10601])).

fof(f10601,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f10593,f81])).

fof(f10593,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_18 ),
    inference(resolution,[],[f9222,f417])).

fof(f417,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k2_relat_1(k7_relat_1(X4,X5)))
      | ~ v1_xboole_0(k2_relat_1(X4))
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f205,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t19_wellord1.p',t99_relat_1)).

fof(f205,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,X2)
      | ~ r2_hidden(X3,X4)
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f122,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t19_wellord1.p',t3_subset)).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t19_wellord1.p',t5_subset)).

fof(f9222,plain,
    ( r2_hidden(sK0,k2_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f9212,f81])).

fof(f9212,plain,
    ( r2_hidden(sK0,k2_relat_1(k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(sK2)
    | ~ spl6_18 ),
    inference(resolution,[],[f901,f807])).

fof(f807,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_relat_1(k2_wellord1(X1,X0)))
      | r2_hidden(X2,k2_relat_1(k7_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f802,f95])).

fof(f802,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_relat_1(k2_wellord1(X1,X0)))
      | r2_hidden(X2,k2_relat_1(k7_relat_1(X1,X0)))
      | ~ v1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f241,f99])).

fof(f241,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X6,k2_relat_1(k8_relat_1(X5,X4)))
      | r2_hidden(X6,k2_relat_1(X4))
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f125,f101])).

fof(f125,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f110])).

fof(f110,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f75])).

fof(f10914,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | r2_hidden(sK0,k2_relat_1(sK2))
    | ~ spl6_18 ),
    inference(resolution,[],[f10600,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t19_wellord1.p',t2_subset)).

fof(f10600,plain,
    ( m1_subset_1(sK0,k2_relat_1(sK2))
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f10592,f81])).

fof(f10592,plain,
    ( m1_subset_1(sK0,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_18 ),
    inference(resolution,[],[f9222,f460])).

fof(f460,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k2_relat_1(k7_relat_1(X4,X5)))
      | m1_subset_1(X3,k2_relat_1(X4))
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f209,f98])).

fof(f209,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,X3)
      | ~ r2_hidden(X2,X4)
      | m1_subset_1(X2,X3) ) ),
    inference(resolution,[],[f109,f106])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t19_wellord1.p',t4_subset)).

fof(f9211,plain,
    ( spl6_1
    | ~ spl6_20 ),
    inference(avatar_contradiction_clause,[],[f9210])).

fof(f9210,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f9209,f81])).

fof(f9209,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl6_1
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f9202,f131])).

fof(f9202,plain,
    ( r2_hidden(sK0,k3_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_20 ),
    inference(resolution,[],[f9130,f206])).

fof(f206,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f127,f88])).

fof(f127,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f117])).

fof(f117,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f80])).

fof(f9130,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f9128,f8821])).

fof(f8821,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f8812,f81])).

fof(f8812,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_20 ),
    inference(resolution,[],[f7883,f416])).

fof(f416,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | ~ v1_xboole_0(k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f205,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t19_wellord1.p',l29_wellord1)).

fof(f7883,plain,
    ( r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f7872,f81])).

fof(f7872,plain,
    ( r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    | ~ v1_relat_1(sK2)
    | ~ spl6_20 ),
    inference(resolution,[],[f904,f786])).

fof(f786,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(k2_wellord1(X1,X0)))
      | r2_hidden(X2,k1_relat_1(k8_relat_1(X0,X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f781,f96])).

fof(f781,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(k2_wellord1(X1,X0)))
      | r2_hidden(X2,k1_relat_1(k8_relat_1(X0,X1)))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f229,f102])).

fof(f229,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X6,k1_relat_1(k7_relat_1(X4,X5)))
      | r2_hidden(X6,k1_relat_1(X4))
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f125,f100])).

fof(f9128,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl6_20 ),
    inference(resolution,[],[f8820,f105])).

fof(f8820,plain,
    ( m1_subset_1(sK0,k1_relat_1(sK2))
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f8811,f81])).

fof(f8811,plain,
    ( m1_subset_1(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_20 ),
    inference(resolution,[],[f7883,f459])).

fof(f459,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | m1_subset_1(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f209,f97])).

fof(f908,plain,(
    spl6_17 ),
    inference(avatar_contradiction_clause,[],[f907])).

fof(f907,plain,
    ( $false
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f906,f81])).

fof(f906,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl6_17 ),
    inference(resolution,[],[f898,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t19_wellord1.p',dt_k2_wellord1)).

fof(f898,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,sK1))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f897])).

fof(f897,plain,
    ( spl6_17
  <=> ~ v1_relat_1(k2_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f905,plain,
    ( ~ spl6_17
    | spl6_18
    | spl6_20 ),
    inference(avatar_split_clause,[],[f885,f903,f900,f897])).

fof(f885,plain,
    ( r2_hidden(sK0,k1_relat_1(k2_wellord1(sK2,sK1)))
    | r2_hidden(sK0,k2_relat_1(k2_wellord1(sK2,sK1)))
    | ~ v1_relat_1(k2_wellord1(sK2,sK1)) ),
    inference(resolution,[],[f299,f82])).

fof(f82,plain,(
    r2_hidden(sK0,k3_relat_1(k2_wellord1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f68])).

fof(f299,plain,(
    ! [X15,X16] :
      ( ~ r2_hidden(X16,k3_relat_1(X15))
      | r2_hidden(X16,k1_relat_1(X15))
      | r2_hidden(X16,k2_relat_1(X15))
      | ~ v1_relat_1(X15) ) ),
    inference(superposition,[],[f128,f88])).

fof(f128,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f80])).

fof(f135,plain,
    ( ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f83,f133,f130])).

fof(f83,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f68])).
%------------------------------------------------------------------------------
