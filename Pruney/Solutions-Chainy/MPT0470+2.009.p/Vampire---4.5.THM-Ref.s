%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:45 EST 2020

% Result     : Theorem 1.76s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 198 expanded)
%              Number of leaves         :   30 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          :  360 ( 574 expanded)
%              Number of equality atoms :   73 ( 168 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1066,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f102,f105,f205,f212,f290,f488,f1035,f1038,f1061])).

fof(f1061,plain,
    ( spl7_1
    | ~ spl7_24
    | ~ spl7_56 ),
    inference(avatar_contradiction_clause,[],[f1060])).

fof(f1060,plain,
    ( $false
    | spl7_1
    | ~ spl7_24
    | ~ spl7_56 ),
    inference(subsumption_resolution,[],[f1053,f82])).

fof(f82,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl7_1
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f1053,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ spl7_24
    | ~ spl7_56 ),
    inference(resolution,[],[f1052,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f1052,plain,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl7_24
    | ~ spl7_56 ),
    inference(subsumption_resolution,[],[f1051,f475])).

fof(f475,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f474])).

fof(f474,plain,
    ( spl7_24
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f1051,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl7_56 ),
    inference(subsumption_resolution,[],[f1044,f49])).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1044,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl7_56 ),
    inference(superposition,[],[f57,f1034])).

fof(f1034,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl7_56 ),
    inference(avatar_component_clause,[],[f1032])).

fof(f1032,plain,
    ( spl7_56
  <=> k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f1038,plain,(
    spl7_25 ),
    inference(avatar_contradiction_clause,[],[f1037])).

fof(f1037,plain,
    ( $false
    | spl7_25 ),
    inference(subsumption_resolution,[],[f1036,f89])).

fof(f89,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f58,f77])).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f58,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f1036,plain,
    ( r2_hidden(sK3(k1_xboole_0,k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),k1_xboole_0)
    | spl7_25 ),
    inference(resolution,[],[f479,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f479,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | spl7_25 ),
    inference(avatar_component_clause,[],[f478])).

fof(f478,plain,
    ( spl7_25
  <=> r1_tarski(k1_xboole_0,k1_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f1035,plain,
    ( spl7_56
    | ~ spl7_25
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f1030,f96,f478,f1032])).

fof(f96,plain,
    ( spl7_3
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f1030,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f986,f97])).

fof(f97,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f986,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f764,f50])).

fof(f50,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f764,plain,(
    ! [X8] :
      ( ~ r1_tarski(k1_relat_1(X8),k1_relat_1(k5_relat_1(X8,sK0)))
      | k1_relat_1(X8) = k1_relat_1(k5_relat_1(X8,sK0))
      | ~ v1_relat_1(X8) ) ),
    inference(resolution,[],[f107,f47])).

fof(f47,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(k5_relat_1(X1,X0))) ) ),
    inference(resolution,[],[f56,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(f488,plain,
    ( ~ spl7_3
    | spl7_24 ),
    inference(avatar_contradiction_clause,[],[f487])).

fof(f487,plain,
    ( $false
    | ~ spl7_3
    | spl7_24 ),
    inference(subsumption_resolution,[],[f486,f97])).

fof(f486,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl7_24 ),
    inference(subsumption_resolution,[],[f484,f47])).

fof(f484,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl7_24 ),
    inference(resolution,[],[f476,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f476,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | spl7_24 ),
    inference(avatar_component_clause,[],[f474])).

fof(f290,plain,
    ( ~ spl7_4
    | ~ spl7_13 ),
    inference(avatar_contradiction_clause,[],[f289])).

fof(f289,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f288,f89])).

fof(f288,plain,
    ( r2_hidden(sK2(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl7_4
    | ~ spl7_13 ),
    inference(forward_demodulation,[],[f286,f183])).

fof(f183,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl7_4 ),
    inference(resolution,[],[f47,f134])).

fof(f134,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k1_xboole_0 = k2_relat_1(k5_relat_1(X1,k1_xboole_0)) )
    | ~ spl7_4 ),
    inference(resolution,[],[f131,f101])).

fof(f101,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl7_4
  <=> ! [X0] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f131,plain,(
    ! [X4] :
      ( ~ r1_tarski(X4,k1_xboole_0)
      | k1_xboole_0 = X4 ) ),
    inference(resolution,[],[f92,f89])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X1,X0),X1)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(resolution,[],[f62,f64])).

fof(f286,plain,
    ( r2_hidden(sK2(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl7_13 ),
    inference(resolution,[],[f211,f75])).

fof(f75,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f40,f43,f42,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f211,plain,
    ( r2_hidden(k4_tarski(sK1(k5_relat_1(sK0,k1_xboole_0)),sK2(k5_relat_1(sK0,k1_xboole_0))),k5_relat_1(sK0,k1_xboole_0))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl7_13
  <=> r2_hidden(k4_tarski(sK1(k5_relat_1(sK0,k1_xboole_0)),sK2(k5_relat_1(sK0,k1_xboole_0))),k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f212,plain,
    ( spl7_2
    | spl7_13
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f207,f194,f209,f84])).

fof(f84,plain,
    ( spl7_2
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f194,plain,
    ( spl7_11
  <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f207,plain,
    ( r2_hidden(k4_tarski(sK1(k5_relat_1(sK0,k1_xboole_0)),sK2(k5_relat_1(sK0,k1_xboole_0))),k5_relat_1(sK0,k1_xboole_0))
    | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl7_11 ),
    inference(resolution,[],[f195,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
     => r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

fof(f195,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f194])).

fof(f205,plain,
    ( ~ spl7_3
    | spl7_11 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | ~ spl7_3
    | spl7_11 ),
    inference(subsumption_resolution,[],[f203,f47])).

fof(f203,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl7_3
    | spl7_11 ),
    inference(subsumption_resolution,[],[f201,f97])).

fof(f201,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | spl7_11 ),
    inference(resolution,[],[f196,f59])).

fof(f196,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | spl7_11 ),
    inference(avatar_component_clause,[],[f194])).

fof(f105,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | spl7_3 ),
    inference(subsumption_resolution,[],[f103,f49])).

fof(f103,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl7_3 ),
    inference(resolution,[],[f98,f52])).

fof(f52,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f98,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f102,plain,
    ( ~ spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f94,f100,f96])).

fof(f94,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f55,f51])).

fof(f51,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f87,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f48,f84,f80])).

fof(f48,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:39:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (29530)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (29537)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (29540)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (29538)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (29528)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (29523)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (29533)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (29545)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (29526)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (29525)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (29525)Refutation not found, incomplete strategy% (29525)------------------------------
% 0.22/0.54  % (29525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (29525)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (29525)Memory used [KB]: 10618
% 0.22/0.54  % (29525)Time elapsed: 0.122 s
% 0.22/0.54  % (29525)------------------------------
% 0.22/0.54  % (29525)------------------------------
% 0.22/0.54  % (29524)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (29545)Refutation not found, incomplete strategy% (29545)------------------------------
% 0.22/0.55  % (29545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (29545)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (29545)Memory used [KB]: 10746
% 0.22/0.55  % (29545)Time elapsed: 0.083 s
% 0.22/0.55  % (29545)------------------------------
% 0.22/0.55  % (29545)------------------------------
% 0.22/0.55  % (29547)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (29529)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (29531)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (29551)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (29527)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.55  % (29550)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (29544)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (29543)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (29532)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (29546)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (29544)Refutation not found, incomplete strategy% (29544)------------------------------
% 0.22/0.55  % (29544)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (29544)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  % (29543)Refutation not found, incomplete strategy% (29543)------------------------------
% 0.22/0.56  % (29543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (29543)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (29543)Memory used [KB]: 10746
% 0.22/0.56  % (29543)Time elapsed: 0.137 s
% 0.22/0.56  % (29543)------------------------------
% 0.22/0.56  % (29543)------------------------------
% 0.22/0.56  
% 0.22/0.56  % (29544)Memory used [KB]: 1663
% 0.22/0.56  % (29544)Time elapsed: 0.139 s
% 0.22/0.56  % (29544)------------------------------
% 0.22/0.56  % (29544)------------------------------
% 0.22/0.56  % (29536)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (29549)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.56  % (29539)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.56  % (29540)Refutation not found, incomplete strategy% (29540)------------------------------
% 0.22/0.56  % (29540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (29540)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (29540)Memory used [KB]: 10618
% 0.22/0.56  % (29540)Time elapsed: 0.145 s
% 0.22/0.56  % (29540)------------------------------
% 0.22/0.56  % (29540)------------------------------
% 0.22/0.56  % (29535)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.53/0.56  % (29548)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.53/0.56  % (29552)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.53/0.56  % (29542)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.53/0.56  % (29541)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.53/0.56  % (29534)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.76/0.60  % (29526)Refutation found. Thanks to Tanya!
% 1.76/0.60  % SZS status Theorem for theBenchmark
% 1.76/0.62  % SZS output start Proof for theBenchmark
% 1.76/0.62  fof(f1066,plain,(
% 1.76/0.62    $false),
% 1.76/0.62    inference(avatar_sat_refutation,[],[f87,f102,f105,f205,f212,f290,f488,f1035,f1038,f1061])).
% 1.76/0.62  fof(f1061,plain,(
% 1.76/0.62    spl7_1 | ~spl7_24 | ~spl7_56),
% 1.76/0.62    inference(avatar_contradiction_clause,[],[f1060])).
% 1.76/0.62  fof(f1060,plain,(
% 1.76/0.62    $false | (spl7_1 | ~spl7_24 | ~spl7_56)),
% 1.76/0.62    inference(subsumption_resolution,[],[f1053,f82])).
% 1.76/0.62  fof(f82,plain,(
% 1.76/0.62    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl7_1),
% 1.76/0.62    inference(avatar_component_clause,[],[f80])).
% 1.76/0.62  fof(f80,plain,(
% 1.76/0.62    spl7_1 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.76/0.62  fof(f1053,plain,(
% 1.76/0.62    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | (~spl7_24 | ~spl7_56)),
% 1.76/0.62    inference(resolution,[],[f1052,f53])).
% 1.76/0.62  fof(f53,plain,(
% 1.76/0.62    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.76/0.62    inference(cnf_transformation,[],[f19])).
% 1.76/0.62  fof(f19,plain,(
% 1.76/0.62    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.76/0.62    inference(ennf_transformation,[],[f3])).
% 1.76/0.62  fof(f3,axiom,(
% 1.76/0.62    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.76/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.76/0.62  fof(f1052,plain,(
% 1.76/0.62    v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) | (~spl7_24 | ~spl7_56)),
% 1.76/0.62    inference(subsumption_resolution,[],[f1051,f475])).
% 1.76/0.62  fof(f475,plain,(
% 1.76/0.62    v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl7_24),
% 1.76/0.62    inference(avatar_component_clause,[],[f474])).
% 1.76/0.62  fof(f474,plain,(
% 1.76/0.62    spl7_24 <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 1.76/0.62  fof(f1051,plain,(
% 1.76/0.62    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) | ~spl7_56),
% 1.76/0.62    inference(subsumption_resolution,[],[f1044,f49])).
% 1.76/0.62  fof(f49,plain,(
% 1.76/0.62    v1_xboole_0(k1_xboole_0)),
% 1.76/0.62    inference(cnf_transformation,[],[f2])).
% 1.76/0.62  fof(f2,axiom,(
% 1.76/0.62    v1_xboole_0(k1_xboole_0)),
% 1.76/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.76/0.62  fof(f1044,plain,(
% 1.76/0.62    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) | ~spl7_56),
% 1.76/0.62    inference(superposition,[],[f57,f1034])).
% 1.76/0.62  fof(f1034,plain,(
% 1.76/0.62    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl7_56),
% 1.76/0.62    inference(avatar_component_clause,[],[f1032])).
% 1.76/0.62  fof(f1032,plain,(
% 1.76/0.62    spl7_56 <=> k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).
% 1.76/0.62  fof(f57,plain,(
% 1.76/0.62    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f25])).
% 1.76/0.62  fof(f25,plain,(
% 1.76/0.62    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 1.76/0.62    inference(flattening,[],[f24])).
% 1.76/0.62  fof(f24,plain,(
% 1.76/0.62    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 1.76/0.62    inference(ennf_transformation,[],[f10])).
% 1.76/0.62  fof(f10,axiom,(
% 1.76/0.62    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 1.76/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).
% 1.76/0.62  fof(f1038,plain,(
% 1.76/0.62    spl7_25),
% 1.76/0.62    inference(avatar_contradiction_clause,[],[f1037])).
% 1.76/0.62  fof(f1037,plain,(
% 1.76/0.62    $false | spl7_25),
% 1.76/0.62    inference(subsumption_resolution,[],[f1036,f89])).
% 1.76/0.62  fof(f89,plain,(
% 1.76/0.62    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.76/0.62    inference(superposition,[],[f58,f77])).
% 1.76/0.62  fof(f77,plain,(
% 1.76/0.62    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.76/0.62    inference(equality_resolution,[],[f72])).
% 1.76/0.62  fof(f72,plain,(
% 1.76/0.62    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.76/0.62    inference(cnf_transformation,[],[f46])).
% 1.76/0.62  fof(f46,plain,(
% 1.76/0.62    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.76/0.62    inference(flattening,[],[f45])).
% 1.76/0.62  fof(f45,plain,(
% 1.76/0.62    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.76/0.62    inference(nnf_transformation,[],[f5])).
% 1.76/0.62  fof(f5,axiom,(
% 1.76/0.62    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.76/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.76/0.62  fof(f58,plain,(
% 1.76/0.62    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.76/0.62    inference(cnf_transformation,[],[f6])).
% 1.76/0.62  fof(f6,axiom,(
% 1.76/0.62    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.76/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 1.76/0.62  fof(f1036,plain,(
% 1.76/0.62    r2_hidden(sK3(k1_xboole_0,k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),k1_xboole_0) | spl7_25),
% 1.76/0.62    inference(resolution,[],[f479,f64])).
% 1.76/0.62  fof(f64,plain,(
% 1.76/0.62    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f38])).
% 1.76/0.62  fof(f38,plain,(
% 1.76/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.76/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 1.76/0.62  fof(f37,plain,(
% 1.76/0.62    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.76/0.62    introduced(choice_axiom,[])).
% 1.76/0.62  fof(f36,plain,(
% 1.76/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.76/0.62    inference(rectify,[],[f35])).
% 1.76/0.62  fof(f35,plain,(
% 1.76/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.76/0.62    inference(nnf_transformation,[],[f28])).
% 1.76/0.62  fof(f28,plain,(
% 1.76/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.76/0.62    inference(ennf_transformation,[],[f1])).
% 1.76/0.62  fof(f1,axiom,(
% 1.76/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.76/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.76/0.62  fof(f479,plain,(
% 1.76/0.62    ~r1_tarski(k1_xboole_0,k1_relat_1(k5_relat_1(k1_xboole_0,sK0))) | spl7_25),
% 1.76/0.62    inference(avatar_component_clause,[],[f478])).
% 1.76/0.62  fof(f478,plain,(
% 1.76/0.62    spl7_25 <=> r1_tarski(k1_xboole_0,k1_relat_1(k5_relat_1(k1_xboole_0,sK0)))),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 1.76/0.62  fof(f1035,plain,(
% 1.76/0.62    spl7_56 | ~spl7_25 | ~spl7_3),
% 1.76/0.62    inference(avatar_split_clause,[],[f1030,f96,f478,f1032])).
% 1.76/0.62  fof(f96,plain,(
% 1.76/0.62    spl7_3 <=> v1_relat_1(k1_xboole_0)),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.76/0.62  fof(f1030,plain,(
% 1.76/0.62    ~r1_tarski(k1_xboole_0,k1_relat_1(k5_relat_1(k1_xboole_0,sK0))) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl7_3),
% 1.76/0.62    inference(subsumption_resolution,[],[f986,f97])).
% 1.76/0.62  fof(f97,plain,(
% 1.76/0.62    v1_relat_1(k1_xboole_0) | ~spl7_3),
% 1.76/0.62    inference(avatar_component_clause,[],[f96])).
% 1.76/0.62  fof(f986,plain,(
% 1.76/0.62    ~r1_tarski(k1_xboole_0,k1_relat_1(k5_relat_1(k1_xboole_0,sK0))) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~v1_relat_1(k1_xboole_0)),
% 1.76/0.62    inference(superposition,[],[f764,f50])).
% 1.76/0.62  fof(f50,plain,(
% 1.76/0.62    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.76/0.62    inference(cnf_transformation,[],[f14])).
% 1.76/0.62  fof(f14,axiom,(
% 1.76/0.62    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.76/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.76/0.62  fof(f764,plain,(
% 1.76/0.62    ( ! [X8] : (~r1_tarski(k1_relat_1(X8),k1_relat_1(k5_relat_1(X8,sK0))) | k1_relat_1(X8) = k1_relat_1(k5_relat_1(X8,sK0)) | ~v1_relat_1(X8)) )),
% 1.76/0.62    inference(resolution,[],[f107,f47])).
% 1.76/0.62  fof(f47,plain,(
% 1.76/0.62    v1_relat_1(sK0)),
% 1.76/0.62    inference(cnf_transformation,[],[f30])).
% 1.76/0.62  fof(f30,plain,(
% 1.76/0.62    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 1.76/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f29])).
% 1.76/0.62  fof(f29,plain,(
% 1.76/0.62    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 1.76/0.62    introduced(choice_axiom,[])).
% 1.76/0.62  fof(f17,plain,(
% 1.76/0.62    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.76/0.62    inference(ennf_transformation,[],[f16])).
% 1.76/0.62  fof(f16,negated_conjecture,(
% 1.76/0.62    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.76/0.62    inference(negated_conjecture,[],[f15])).
% 1.76/0.62  fof(f15,conjecture,(
% 1.76/0.62    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.76/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 1.76/0.62  fof(f107,plain,(
% 1.76/0.62    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X1),k1_relat_1(k5_relat_1(X1,X0)))) )),
% 1.76/0.62    inference(resolution,[],[f56,f62])).
% 1.76/0.62  fof(f62,plain,(
% 1.76/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f34])).
% 1.76/0.62  fof(f34,plain,(
% 1.76/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.76/0.62    inference(flattening,[],[f33])).
% 1.76/0.62  fof(f33,plain,(
% 1.76/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.76/0.62    inference(nnf_transformation,[],[f4])).
% 1.76/0.62  fof(f4,axiom,(
% 1.76/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.76/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.76/0.62  fof(f56,plain,(
% 1.76/0.62    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f23])).
% 1.76/0.62  fof(f23,plain,(
% 1.76/0.62    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.76/0.62    inference(ennf_transformation,[],[f11])).
% 1.76/0.62  fof(f11,axiom,(
% 1.76/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 1.76/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).
% 1.76/0.62  fof(f488,plain,(
% 1.76/0.62    ~spl7_3 | spl7_24),
% 1.76/0.62    inference(avatar_contradiction_clause,[],[f487])).
% 1.76/0.62  fof(f487,plain,(
% 1.76/0.62    $false | (~spl7_3 | spl7_24)),
% 1.76/0.62    inference(subsumption_resolution,[],[f486,f97])).
% 1.76/0.62  fof(f486,plain,(
% 1.76/0.62    ~v1_relat_1(k1_xboole_0) | spl7_24),
% 1.76/0.62    inference(subsumption_resolution,[],[f484,f47])).
% 1.76/0.62  fof(f484,plain,(
% 1.76/0.62    ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | spl7_24),
% 1.76/0.62    inference(resolution,[],[f476,f59])).
% 1.76/0.62  fof(f59,plain,(
% 1.76/0.62    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f27])).
% 1.76/0.62  fof(f27,plain,(
% 1.76/0.62    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.76/0.62    inference(flattening,[],[f26])).
% 1.76/0.62  fof(f26,plain,(
% 1.76/0.62    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.76/0.62    inference(ennf_transformation,[],[f9])).
% 1.76/0.62  fof(f9,axiom,(
% 1.76/0.62    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.76/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.76/0.62  fof(f476,plain,(
% 1.76/0.62    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | spl7_24),
% 1.76/0.62    inference(avatar_component_clause,[],[f474])).
% 1.76/0.62  fof(f290,plain,(
% 1.76/0.62    ~spl7_4 | ~spl7_13),
% 1.76/0.62    inference(avatar_contradiction_clause,[],[f289])).
% 1.76/0.62  fof(f289,plain,(
% 1.76/0.62    $false | (~spl7_4 | ~spl7_13)),
% 1.76/0.62    inference(subsumption_resolution,[],[f288,f89])).
% 1.76/0.62  fof(f288,plain,(
% 1.76/0.62    r2_hidden(sK2(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0) | (~spl7_4 | ~spl7_13)),
% 1.76/0.62    inference(forward_demodulation,[],[f286,f183])).
% 1.76/0.62  fof(f183,plain,(
% 1.76/0.62    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl7_4),
% 1.76/0.62    inference(resolution,[],[f47,f134])).
% 1.76/0.62  fof(f134,plain,(
% 1.76/0.62    ( ! [X1] : (~v1_relat_1(X1) | k1_xboole_0 = k2_relat_1(k5_relat_1(X1,k1_xboole_0))) ) | ~spl7_4),
% 1.76/0.62    inference(resolution,[],[f131,f101])).
% 1.76/0.62  fof(f101,plain,(
% 1.76/0.62    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl7_4),
% 1.76/0.62    inference(avatar_component_clause,[],[f100])).
% 1.76/0.62  fof(f100,plain,(
% 1.76/0.62    spl7_4 <=> ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0))),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.76/0.62  fof(f131,plain,(
% 1.76/0.62    ( ! [X4] : (~r1_tarski(X4,k1_xboole_0) | k1_xboole_0 = X4) )),
% 1.76/0.62    inference(resolution,[],[f92,f89])).
% 1.76/0.62  fof(f92,plain,(
% 1.76/0.62    ( ! [X0,X1] : (r2_hidden(sK3(X1,X0),X1) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.76/0.62    inference(resolution,[],[f62,f64])).
% 1.76/0.62  fof(f286,plain,(
% 1.76/0.62    r2_hidden(sK2(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) | ~spl7_13),
% 1.76/0.62    inference(resolution,[],[f211,f75])).
% 1.76/0.62  fof(f75,plain,(
% 1.76/0.62    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X6,X5),X0) | r2_hidden(X5,k2_relat_1(X0))) )),
% 1.76/0.62    inference(equality_resolution,[],[f67])).
% 1.76/0.62  fof(f67,plain,(
% 1.76/0.62    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 1.76/0.62    inference(cnf_transformation,[],[f44])).
% 1.76/0.62  fof(f44,plain,(
% 1.76/0.62    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.76/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f40,f43,f42,f41])).
% 1.76/0.62  fof(f41,plain,(
% 1.76/0.62    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 1.76/0.62    introduced(choice_axiom,[])).
% 1.76/0.62  fof(f42,plain,(
% 1.76/0.62    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0) => r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0))),
% 1.76/0.62    introduced(choice_axiom,[])).
% 1.76/0.62  fof(f43,plain,(
% 1.76/0.62    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0))),
% 1.76/0.62    introduced(choice_axiom,[])).
% 1.76/0.62  fof(f40,plain,(
% 1.76/0.62    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.76/0.62    inference(rectify,[],[f39])).
% 1.76/0.62  fof(f39,plain,(
% 1.76/0.62    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 1.76/0.62    inference(nnf_transformation,[],[f8])).
% 1.76/0.62  fof(f8,axiom,(
% 1.76/0.62    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.76/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 1.76/0.62  fof(f211,plain,(
% 1.76/0.62    r2_hidden(k4_tarski(sK1(k5_relat_1(sK0,k1_xboole_0)),sK2(k5_relat_1(sK0,k1_xboole_0))),k5_relat_1(sK0,k1_xboole_0)) | ~spl7_13),
% 1.76/0.62    inference(avatar_component_clause,[],[f209])).
% 1.76/0.62  fof(f209,plain,(
% 1.76/0.62    spl7_13 <=> r2_hidden(k4_tarski(sK1(k5_relat_1(sK0,k1_xboole_0)),sK2(k5_relat_1(sK0,k1_xboole_0))),k5_relat_1(sK0,k1_xboole_0))),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 1.76/0.62  fof(f212,plain,(
% 1.76/0.62    spl7_2 | spl7_13 | ~spl7_11),
% 1.76/0.62    inference(avatar_split_clause,[],[f207,f194,f209,f84])).
% 1.76/0.62  fof(f84,plain,(
% 1.76/0.62    spl7_2 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.76/0.62  fof(f194,plain,(
% 1.76/0.62    spl7_11 <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.76/0.62  fof(f207,plain,(
% 1.76/0.62    r2_hidden(k4_tarski(sK1(k5_relat_1(sK0,k1_xboole_0)),sK2(k5_relat_1(sK0,k1_xboole_0))),k5_relat_1(sK0,k1_xboole_0)) | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | ~spl7_11),
% 1.76/0.62    inference(resolution,[],[f195,f54])).
% 1.76/0.62  fof(f54,plain,(
% 1.76/0.62    ( ! [X0] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) | k1_xboole_0 = X0) )),
% 1.76/0.62    inference(cnf_transformation,[],[f32])).
% 1.76/0.62  fof(f32,plain,(
% 1.76/0.62    ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) | ~v1_relat_1(X0))),
% 1.76/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f31])).
% 1.76/0.62  fof(f31,plain,(
% 1.76/0.62    ! [X0] : (? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) => r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0))),
% 1.76/0.62    introduced(choice_axiom,[])).
% 1.76/0.62  fof(f21,plain,(
% 1.76/0.62    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 1.76/0.62    inference(flattening,[],[f20])).
% 1.76/0.62  fof(f20,plain,(
% 1.76/0.62    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 1.76/0.62    inference(ennf_transformation,[],[f13])).
% 1.76/0.62  fof(f13,axiom,(
% 1.76/0.62    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 1.76/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).
% 1.76/0.62  fof(f195,plain,(
% 1.76/0.62    v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl7_11),
% 1.76/0.62    inference(avatar_component_clause,[],[f194])).
% 1.76/0.62  fof(f205,plain,(
% 1.76/0.62    ~spl7_3 | spl7_11),
% 1.76/0.62    inference(avatar_contradiction_clause,[],[f204])).
% 1.76/0.62  fof(f204,plain,(
% 1.76/0.62    $false | (~spl7_3 | spl7_11)),
% 1.76/0.62    inference(subsumption_resolution,[],[f203,f47])).
% 1.76/0.62  fof(f203,plain,(
% 1.76/0.62    ~v1_relat_1(sK0) | (~spl7_3 | spl7_11)),
% 1.76/0.62    inference(subsumption_resolution,[],[f201,f97])).
% 1.76/0.62  fof(f201,plain,(
% 1.76/0.62    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0) | spl7_11),
% 1.76/0.62    inference(resolution,[],[f196,f59])).
% 1.76/0.62  fof(f196,plain,(
% 1.76/0.62    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | spl7_11),
% 1.76/0.62    inference(avatar_component_clause,[],[f194])).
% 1.76/0.62  fof(f105,plain,(
% 1.76/0.62    spl7_3),
% 1.76/0.62    inference(avatar_contradiction_clause,[],[f104])).
% 1.76/0.62  fof(f104,plain,(
% 1.76/0.62    $false | spl7_3),
% 1.76/0.62    inference(subsumption_resolution,[],[f103,f49])).
% 1.76/0.62  fof(f103,plain,(
% 1.76/0.62    ~v1_xboole_0(k1_xboole_0) | spl7_3),
% 1.76/0.62    inference(resolution,[],[f98,f52])).
% 1.76/0.62  fof(f52,plain,(
% 1.76/0.62    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f18])).
% 1.76/0.62  fof(f18,plain,(
% 1.76/0.62    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.76/0.62    inference(ennf_transformation,[],[f7])).
% 1.76/0.62  fof(f7,axiom,(
% 1.76/0.62    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.76/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.76/0.62  fof(f98,plain,(
% 1.76/0.62    ~v1_relat_1(k1_xboole_0) | spl7_3),
% 1.76/0.62    inference(avatar_component_clause,[],[f96])).
% 1.76/0.62  fof(f102,plain,(
% 1.76/0.62    ~spl7_3 | spl7_4),
% 1.76/0.62    inference(avatar_split_clause,[],[f94,f100,f96])).
% 1.76/0.62  fof(f94,plain,(
% 1.76/0.62    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.76/0.62    inference(superposition,[],[f55,f51])).
% 1.76/0.62  fof(f51,plain,(
% 1.76/0.62    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.76/0.62    inference(cnf_transformation,[],[f14])).
% 1.76/0.62  fof(f55,plain,(
% 1.76/0.62    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f22])).
% 1.76/0.62  fof(f22,plain,(
% 1.76/0.62    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.76/0.62    inference(ennf_transformation,[],[f12])).
% 1.76/0.62  fof(f12,axiom,(
% 1.76/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.76/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 1.76/0.62  fof(f87,plain,(
% 1.76/0.62    ~spl7_1 | ~spl7_2),
% 1.76/0.62    inference(avatar_split_clause,[],[f48,f84,f80])).
% 1.76/0.62  fof(f48,plain,(
% 1.76/0.62    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.76/0.62    inference(cnf_transformation,[],[f30])).
% 1.76/0.62  % SZS output end Proof for theBenchmark
% 1.76/0.62  % (29526)------------------------------
% 1.76/0.62  % (29526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.62  % (29526)Termination reason: Refutation
% 1.76/0.62  
% 1.76/0.62  % (29526)Memory used [KB]: 11129
% 1.76/0.62  % (29526)Time elapsed: 0.167 s
% 1.76/0.62  % (29526)------------------------------
% 1.76/0.62  % (29526)------------------------------
% 1.76/0.62  % (29522)Success in time 0.251 s
%------------------------------------------------------------------------------
