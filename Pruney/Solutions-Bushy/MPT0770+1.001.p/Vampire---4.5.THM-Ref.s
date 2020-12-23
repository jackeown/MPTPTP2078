%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0770+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:37 EST 2020

% Result     : Theorem 2.71s
% Output     : Refutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 392 expanded)
%              Number of leaves         :   25 ( 100 expanded)
%              Depth                    :   20
%              Number of atoms          :  489 (1640 expanded)
%              Number of equality atoms :   38 ( 135 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2295,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f289,f292,f1889,f2280,f2283,f2294])).

fof(f2294,plain,
    ( spl5_2
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f2293])).

fof(f2293,plain,
    ( $false
    | spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f2292,f50])).

fof(f50,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ r2_hidden(sK0,sK1)
      | ~ r2_hidden(sK0,k3_relat_1(sK2)) )
    & r2_hidden(sK0,k3_relat_1(k2_wellord1(sK2,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f38])).

fof(f38,plain,
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

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k3_relat_1(X2)) )
      & r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k3_relat_1(X2)) )
      & r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
         => ( r2_hidden(X0,X1)
            & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_wellord1)).

fof(f2292,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f2287,f90])).

fof(f90,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl5_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f2287,plain,
    ( r2_hidden(sK0,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl5_4 ),
    inference(resolution,[],[f285,f180])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_relat_1(k2_wellord1(X1,X0)))
      | r2_hidden(X2,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f179,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_relat_1(k2_wellord1(X1,X0)))
      | r2_hidden(X2,X0)
      | ~ v1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f114,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_wellord1)).

fof(f114,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k2_relat_1(k8_relat_1(X4,X3)))
      | r2_hidden(X5,X4)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f83,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

fof(f83,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f47,f48])).

fof(f48,plain,(
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

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f285,plain,
    ( r2_hidden(sK0,k2_relat_1(k2_wellord1(sK2,sK1)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl5_4
  <=> r2_hidden(sK0,k2_relat_1(k2_wellord1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f2283,plain,
    ( spl5_2
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f2282])).

fof(f2282,plain,
    ( $false
    | spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f90,f1898])).

fof(f1898,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f1893,f50])).

fof(f1893,plain,
    ( r2_hidden(sK0,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl5_5 ),
    inference(resolution,[],[f288,f175])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(k2_wellord1(X1,X0)))
      | r2_hidden(X2,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f174,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f174,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(k2_wellord1(X1,X0)))
      | r2_hidden(X2,X0)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f112,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_wellord1)).

fof(f112,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k1_relat_1(k7_relat_1(X3,X4)))
      | r2_hidden(X5,X4)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f83,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f288,plain,
    ( r2_hidden(sK0,k1_relat_1(k2_wellord1(sK2,sK1)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f287])).

fof(f287,plain,
    ( spl5_5
  <=> r2_hidden(sK0,k1_relat_1(k2_wellord1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f2280,plain,
    ( spl5_1
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f2279])).

fof(f2279,plain,
    ( $false
    | spl5_1
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f2278,f50])).

fof(f2278,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_1
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f2277,f87])).

fof(f87,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl5_1
  <=> r2_hidden(sK0,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f2277,plain,
    ( r2_hidden(sK0,k3_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl5_5 ),
    inference(resolution,[],[f2170,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f80,f53])).

fof(f53,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & ~ r2_hidden(sK3(X0,X1,X2),X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( r2_hidden(sK3(X0,X1,X2),X1)
            | r2_hidden(sK3(X0,X1,X2),X0)
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & ~ r2_hidden(sK3(X0,X1,X2),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( r2_hidden(sK3(X0,X1,X2),X1)
          | r2_hidden(sK3(X0,X1,X2),X0)
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f2170,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f2169,f1986])).

fof(f1986,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f1983,f50])).

fof(f1983,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl5_5 ),
    inference(resolution,[],[f1895,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | ~ v1_xboole_0(k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f93,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_wellord1)).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f78,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f1895,plain,
    ( r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f1890,f50])).

fof(f1890,plain,
    ( r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    | ~ v1_relat_1(sK2)
    | ~ spl5_5 ),
    inference(resolution,[],[f288,f232])).

fof(f232,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(k2_wellord1(X1,X0)))
      | r2_hidden(X2,k1_relat_1(k8_relat_1(X0,X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f231,f56])).

fof(f231,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(k2_wellord1(X1,X0)))
      | r2_hidden(X2,k1_relat_1(k8_relat_1(X0,X1)))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f111,f60])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(k7_relat_1(X0,X1)))
      | r2_hidden(X2,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f84,f61])).

fof(f84,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f2169,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl5_5 ),
    inference(resolution,[],[f1985,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f1985,plain,
    ( m1_subset_1(sK0,k1_relat_1(sK2))
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f1982,f50])).

fof(f1982,plain,
    ( m1_subset_1(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl5_5 ),
    inference(resolution,[],[f1895,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | m1_subset_1(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f98,f57])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | ~ r2_hidden(X0,X2)
      | m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f65,f64])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f1889,plain,
    ( spl5_1
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f1888])).

fof(f1888,plain,
    ( $false
    | spl5_1
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f1887,f50])).

fof(f1887,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_1
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f1886,f87])).

fof(f1886,plain,
    ( r2_hidden(sK0,k3_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl5_4 ),
    inference(resolution,[],[f1876,f95])).

fof(f95,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k2_relat_1(X2))
      | r2_hidden(X3,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f79,f53])).

fof(f79,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1876,plain,
    ( r2_hidden(sK0,k2_relat_1(sK2))
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f1875,f1751])).

fof(f1751,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f1748,f50])).

fof(f1748,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl5_4 ),
    inference(resolution,[],[f1616,f97])).

fof(f97,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k2_relat_1(k7_relat_1(X4,X5)))
      | ~ v1_xboole_0(k2_relat_1(X4))
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f93,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

fof(f1616,plain,
    ( r2_hidden(sK0,k2_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f1611,f50])).

fof(f1611,plain,
    ( r2_hidden(sK0,k2_relat_1(k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(sK2)
    | ~ spl5_4 ),
    inference(resolution,[],[f285,f245])).

fof(f245,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_relat_1(k2_wellord1(X1,X0)))
      | r2_hidden(X2,k2_relat_1(k7_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f244,f55])).

fof(f244,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_relat_1(k2_wellord1(X1,X0)))
      | r2_hidden(X2,k2_relat_1(k7_relat_1(X1,X0)))
      | ~ v1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f113,f59])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_relat_1(k8_relat_1(X1,X0)))
      | r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f84,f62])).

fof(f1875,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | r2_hidden(sK0,k2_relat_1(sK2))
    | ~ spl5_4 ),
    inference(resolution,[],[f1750,f63])).

fof(f1750,plain,
    ( m1_subset_1(sK0,k2_relat_1(sK2))
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f1747,f50])).

fof(f1747,plain,
    ( m1_subset_1(sK0,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl5_4 ),
    inference(resolution,[],[f1616,f103])).

fof(f103,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k2_relat_1(k7_relat_1(X4,X5)))
      | m1_subset_1(X3,k2_relat_1(X4))
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f98,f58])).

fof(f292,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f291])).

fof(f291,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f290,f50])).

fof(f290,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_3 ),
    inference(resolution,[],[f282,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f282,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,sK1))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl5_3
  <=> v1_relat_1(k2_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f289,plain,
    ( ~ spl5_3
    | spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f272,f287,f284,f281])).

fof(f272,plain,
    ( r2_hidden(sK0,k1_relat_1(k2_wellord1(sK2,sK1)))
    | r2_hidden(sK0,k2_relat_1(k2_wellord1(sK2,sK1)))
    | ~ v1_relat_1(k2_wellord1(sK2,sK1)) ),
    inference(resolution,[],[f117,f51])).

fof(f51,plain,(
    r2_hidden(sK0,k3_relat_1(k2_wellord1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k3_relat_1(X0))
      | r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f81,f53])).

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f91,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f52,f89,f86])).

fof(f52,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f39])).

%------------------------------------------------------------------------------
