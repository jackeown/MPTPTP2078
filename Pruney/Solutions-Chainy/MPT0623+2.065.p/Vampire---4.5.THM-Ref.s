%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:12 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 129 expanded)
%              Number of leaves         :   18 (  40 expanded)
%              Depth                    :   17
%              Number of atoms          :  273 ( 542 expanded)
%              Number of equality atoms :  117 ( 245 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f187,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f175,f186])).

fof(f186,plain,(
    ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f184,f37])).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f184,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f181,f117])).

fof(f117,plain,(
    k1_xboole_0 = k2_relat_1(sK3(k1_xboole_0)) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_relat_1(sK3(X0)) ) ),
    inference(subsumption_resolution,[],[f93,f44])).

fof(f44,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X2] :
          ( np__1 = k1_funct_1(sK3(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK3(X0)) = X0
      & v1_funct_1(sK3(X0))
      & v1_relat_1(sK3(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_funct_1(X1,X2) = np__1
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( np__1 = k1_funct_1(sK3(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK3(X0)) = X0
        & v1_funct_1(sK3(X0))
        & v1_relat_1(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = np__1 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

fof(f93,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_relat_1(sK3(X0))
      | ~ v1_relat_1(sK3(X0)) ) ),
    inference(superposition,[],[f38,f46])).

fof(f46,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f181,plain,
    ( ~ r1_tarski(k2_relat_1(sK3(k1_xboole_0)),sK0)
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f83,f67])).

fof(f67,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f83,plain,(
    ~ r1_tarski(k2_relat_1(sK3(sK1)),sK0) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ r1_tarski(k2_relat_1(sK3(X0)),sK0) ) ),
    inference(subsumption_resolution,[],[f81,f44])).

fof(f81,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ r1_tarski(k2_relat_1(sK3(X0)),sK0)
      | ~ v1_relat_1(sK3(X0)) ) ),
    inference(subsumption_resolution,[],[f80,f45])).

fof(f45,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f80,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ r1_tarski(k2_relat_1(sK3(X0)),sK0)
      | ~ v1_funct_1(sK3(X0))
      | ~ v1_relat_1(sK3(X0)) ) ),
    inference(superposition,[],[f34,f46])).

fof(f34,plain,(
    ! [X2] :
      ( k1_relat_1(X2) != sK1
      | ~ r1_tarski(k2_relat_1(X2),sK0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK0)
        | k1_relat_1(X2) != sK1
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r1_tarski(k2_relat_1(X2),X0)
            | k1_relat_1(X2) != X1
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X0 ) )
   => ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),sK0)
          | k1_relat_1(X2) != sK1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK0 ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(f175,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f144,f64])).

fof(f64,plain,
    ( k1_xboole_0 != sK0
    | spl7_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl7_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f144,plain,
    ( k1_xboole_0 = sK0
    | spl7_2 ),
    inference(resolution,[],[f116,f105])).

fof(f105,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | spl7_2 ),
    inference(resolution,[],[f101,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f101,plain,
    ( ! [X0] : ~ r1_tarski(k1_tarski(X0),sK0)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f99,f78])).

fof(f78,plain,
    ( k1_xboole_0 != sK1
    | spl7_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f99,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tarski(X0),sK0)
        | k1_xboole_0 = sK1 )
    | spl7_2 ),
    inference(superposition,[],[f91,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
          & k1_relat_1(sK2(X0,X1)) = X0
          & v1_funct_1(sK2(X0,X1))
          & v1_relat_1(sK2(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
        & k1_relat_1(sK2(X0,X1)) = X0
        & v1_funct_1(sK2(X0,X1))
        & v1_relat_1(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f91,plain,
    ( ! [X0] : ~ r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f90,f78])).

fof(f90,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0)
      | k1_xboole_0 = sK1 ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | ~ r1_tarski(k2_relat_1(sK2(X0,X1)),sK0)
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f88,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f88,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | ~ r1_tarski(k2_relat_1(sK2(X0,X1)),sK0)
      | ~ v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f87,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f87,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | ~ r1_tarski(k2_relat_1(sK2(X0,X1)),sK0)
      | ~ v1_funct_1(sK2(X0,X1))
      | ~ v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f34,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f116,plain,(
    ! [X4] :
      ( r2_hidden(sK4(k1_xboole_0,X4),X4)
      | k1_xboole_0 = X4 ) ),
    inference(forward_demodulation,[],[f113,f36])).

fof(f36,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f113,plain,(
    ! [X4] :
      ( k2_relat_1(k1_xboole_0) = X4
      | r2_hidden(sK4(k1_xboole_0,X4),X4) ) ),
    inference(resolution,[],[f51,f84])).

fof(f84,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f48,f60])).

fof(f60,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f48,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
      | k2_relat_1(X0) = X1
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f28,f27,f26])).

fof(f26,plain,(
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

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f68,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f33,f66,f63])).

fof(f33,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.11  % Command    : run_vampire %s %d
% 0.11/0.32  % Computer   : n013.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 09:46:39 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.18/0.38  % (3936)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.18/0.38  % (3940)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.18/0.40  % (3936)Refutation found. Thanks to Tanya!
% 0.18/0.40  % SZS status Theorem for theBenchmark
% 0.18/0.40  % SZS output start Proof for theBenchmark
% 0.18/0.40  fof(f187,plain,(
% 0.18/0.40    $false),
% 0.18/0.40    inference(avatar_sat_refutation,[],[f68,f175,f186])).
% 0.18/0.40  fof(f186,plain,(
% 0.18/0.40    ~spl7_2),
% 0.18/0.40    inference(avatar_contradiction_clause,[],[f185])).
% 0.18/0.40  fof(f185,plain,(
% 0.18/0.40    $false | ~spl7_2),
% 0.18/0.40    inference(subsumption_resolution,[],[f184,f37])).
% 0.18/0.40  fof(f37,plain,(
% 0.18/0.40    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.18/0.40    inference(cnf_transformation,[],[f1])).
% 0.18/0.40  fof(f1,axiom,(
% 0.18/0.40    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.18/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.18/0.40  fof(f184,plain,(
% 0.18/0.40    ~r1_tarski(k1_xboole_0,sK0) | ~spl7_2),
% 0.18/0.40    inference(forward_demodulation,[],[f181,f117])).
% 0.18/0.40  fof(f117,plain,(
% 0.18/0.40    k1_xboole_0 = k2_relat_1(sK3(k1_xboole_0))),
% 0.18/0.40    inference(equality_resolution,[],[f96])).
% 0.18/0.40  fof(f96,plain,(
% 0.18/0.40    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_relat_1(sK3(X0))) )),
% 0.18/0.40    inference(subsumption_resolution,[],[f93,f44])).
% 0.18/0.40  fof(f44,plain,(
% 0.18/0.40    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 0.18/0.40    inference(cnf_transformation,[],[f23])).
% 0.18/0.40  fof(f23,plain,(
% 0.18/0.40    ! [X0] : (! [X2] : (np__1 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0)))),
% 0.18/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f22])).
% 0.18/0.40  fof(f22,plain,(
% 0.18/0.40    ! [X0] : (? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (np__1 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0))))),
% 0.18/0.40    introduced(choice_axiom,[])).
% 0.18/0.40  fof(f16,plain,(
% 0.18/0.40    ! [X0] : ? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.18/0.40    inference(ennf_transformation,[],[f8])).
% 0.18/0.40  fof(f8,axiom,(
% 0.18/0.40    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = np__1) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.18/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).
% 0.18/0.40  fof(f93,plain,(
% 0.18/0.40    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_relat_1(sK3(X0)) | ~v1_relat_1(sK3(X0))) )),
% 0.18/0.40    inference(superposition,[],[f38,f46])).
% 0.18/0.40  fof(f46,plain,(
% 0.18/0.40    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) )),
% 0.18/0.40    inference(cnf_transformation,[],[f23])).
% 0.18/0.40  fof(f38,plain,(
% 0.18/0.40    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.18/0.40    inference(cnf_transformation,[],[f19])).
% 0.18/0.40  fof(f19,plain,(
% 0.18/0.40    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.18/0.40    inference(nnf_transformation,[],[f14])).
% 0.18/0.40  fof(f14,plain,(
% 0.18/0.40    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.18/0.40    inference(ennf_transformation,[],[f7])).
% 0.18/0.40  fof(f7,axiom,(
% 0.18/0.40    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.18/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.18/0.40  fof(f181,plain,(
% 0.18/0.40    ~r1_tarski(k2_relat_1(sK3(k1_xboole_0)),sK0) | ~spl7_2),
% 0.18/0.40    inference(backward_demodulation,[],[f83,f67])).
% 0.18/0.40  fof(f67,plain,(
% 0.18/0.40    k1_xboole_0 = sK1 | ~spl7_2),
% 0.18/0.40    inference(avatar_component_clause,[],[f66])).
% 0.18/0.40  fof(f66,plain,(
% 0.18/0.40    spl7_2 <=> k1_xboole_0 = sK1),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.18/0.40  fof(f83,plain,(
% 0.18/0.40    ~r1_tarski(k2_relat_1(sK3(sK1)),sK0)),
% 0.18/0.40    inference(equality_resolution,[],[f82])).
% 0.18/0.40  fof(f82,plain,(
% 0.18/0.40    ( ! [X0] : (sK1 != X0 | ~r1_tarski(k2_relat_1(sK3(X0)),sK0)) )),
% 0.18/0.40    inference(subsumption_resolution,[],[f81,f44])).
% 0.18/0.40  fof(f81,plain,(
% 0.18/0.40    ( ! [X0] : (sK1 != X0 | ~r1_tarski(k2_relat_1(sK3(X0)),sK0) | ~v1_relat_1(sK3(X0))) )),
% 0.18/0.40    inference(subsumption_resolution,[],[f80,f45])).
% 0.18/0.40  fof(f45,plain,(
% 0.18/0.40    ( ! [X0] : (v1_funct_1(sK3(X0))) )),
% 0.18/0.40    inference(cnf_transformation,[],[f23])).
% 0.18/0.40  fof(f80,plain,(
% 0.18/0.40    ( ! [X0] : (sK1 != X0 | ~r1_tarski(k2_relat_1(sK3(X0)),sK0) | ~v1_funct_1(sK3(X0)) | ~v1_relat_1(sK3(X0))) )),
% 0.18/0.40    inference(superposition,[],[f34,f46])).
% 0.18/0.40  fof(f34,plain,(
% 0.18/0.40    ( ! [X2] : (k1_relat_1(X2) != sK1 | ~r1_tarski(k2_relat_1(X2),sK0) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.18/0.40    inference(cnf_transformation,[],[f18])).
% 0.18/0.40  fof(f18,plain,(
% 0.18/0.40    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0)),
% 0.18/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f17])).
% 0.18/0.40  fof(f17,plain,(
% 0.18/0.40    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0))),
% 0.18/0.40    introduced(choice_axiom,[])).
% 0.18/0.40  fof(f13,plain,(
% 0.18/0.40    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.18/0.40    inference(flattening,[],[f12])).
% 0.18/0.40  fof(f12,plain,(
% 0.18/0.40    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.18/0.40    inference(ennf_transformation,[],[f11])).
% 0.18/0.40  fof(f11,negated_conjecture,(
% 0.18/0.40    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.18/0.40    inference(negated_conjecture,[],[f10])).
% 0.18/0.40  fof(f10,conjecture,(
% 0.18/0.40    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.18/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 0.18/0.40  fof(f175,plain,(
% 0.18/0.40    spl7_1 | spl7_2),
% 0.18/0.40    inference(avatar_contradiction_clause,[],[f174])).
% 0.18/0.40  fof(f174,plain,(
% 0.18/0.40    $false | (spl7_1 | spl7_2)),
% 0.18/0.40    inference(subsumption_resolution,[],[f144,f64])).
% 0.18/0.40  fof(f64,plain,(
% 0.18/0.40    k1_xboole_0 != sK0 | spl7_1),
% 0.18/0.40    inference(avatar_component_clause,[],[f63])).
% 0.18/0.40  fof(f63,plain,(
% 0.18/0.40    spl7_1 <=> k1_xboole_0 = sK0),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.18/0.40  fof(f144,plain,(
% 0.18/0.40    k1_xboole_0 = sK0 | spl7_2),
% 0.18/0.40    inference(resolution,[],[f116,f105])).
% 0.18/0.40  fof(f105,plain,(
% 0.18/0.40    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | spl7_2),
% 0.18/0.40    inference(resolution,[],[f101,f54])).
% 0.18/0.40  fof(f54,plain,(
% 0.18/0.40    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.18/0.40    inference(cnf_transformation,[],[f30])).
% 0.18/0.40  fof(f30,plain,(
% 0.18/0.40    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.18/0.40    inference(nnf_transformation,[],[f2])).
% 0.18/0.40  fof(f2,axiom,(
% 0.18/0.40    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.18/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.18/0.40  fof(f101,plain,(
% 0.18/0.40    ( ! [X0] : (~r1_tarski(k1_tarski(X0),sK0)) ) | spl7_2),
% 0.18/0.40    inference(subsumption_resolution,[],[f99,f78])).
% 0.18/0.40  fof(f78,plain,(
% 0.18/0.40    k1_xboole_0 != sK1 | spl7_2),
% 0.18/0.40    inference(avatar_component_clause,[],[f66])).
% 0.18/0.40  fof(f99,plain,(
% 0.18/0.40    ( ! [X0] : (~r1_tarski(k1_tarski(X0),sK0) | k1_xboole_0 = sK1) ) | spl7_2),
% 0.18/0.40    inference(superposition,[],[f91,f43])).
% 0.18/0.40  fof(f43,plain,(
% 0.18/0.40    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.18/0.40    inference(cnf_transformation,[],[f21])).
% 0.18/0.40  fof(f21,plain,(
% 0.18/0.40    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))) | k1_xboole_0 = X0)),
% 0.18/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f20])).
% 0.18/0.40  fof(f20,plain,(
% 0.18/0.40    ! [X1,X0] : (? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))))),
% 0.18/0.40    introduced(choice_axiom,[])).
% 0.18/0.40  fof(f15,plain,(
% 0.18/0.40    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 0.18/0.40    inference(ennf_transformation,[],[f9])).
% 0.18/0.40  fof(f9,axiom,(
% 0.18/0.40    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.18/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 0.18/0.40  fof(f91,plain,(
% 0.18/0.40    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0)) ) | spl7_2),
% 0.18/0.40    inference(subsumption_resolution,[],[f90,f78])).
% 0.18/0.40  fof(f90,plain,(
% 0.18/0.40    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0) | k1_xboole_0 = sK1) )),
% 0.18/0.40    inference(equality_resolution,[],[f89])).
% 0.18/0.40  fof(f89,plain,(
% 0.18/0.40    ( ! [X0,X1] : (sK1 != X0 | ~r1_tarski(k2_relat_1(sK2(X0,X1)),sK0) | k1_xboole_0 = X0) )),
% 0.18/0.40    inference(subsumption_resolution,[],[f88,f40])).
% 0.18/0.40  fof(f40,plain,(
% 0.18/0.40    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.18/0.40    inference(cnf_transformation,[],[f21])).
% 0.18/0.40  fof(f88,plain,(
% 0.18/0.40    ( ! [X0,X1] : (sK1 != X0 | ~r1_tarski(k2_relat_1(sK2(X0,X1)),sK0) | ~v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.18/0.40    inference(subsumption_resolution,[],[f87,f41])).
% 0.18/0.40  fof(f41,plain,(
% 0.18/0.40    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.18/0.40    inference(cnf_transformation,[],[f21])).
% 0.18/0.40  fof(f87,plain,(
% 0.18/0.40    ( ! [X0,X1] : (sK1 != X0 | ~r1_tarski(k2_relat_1(sK2(X0,X1)),sK0) | ~v1_funct_1(sK2(X0,X1)) | ~v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.18/0.40    inference(superposition,[],[f34,f42])).
% 0.18/0.40  fof(f42,plain,(
% 0.18/0.40    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 0.18/0.40    inference(cnf_transformation,[],[f21])).
% 0.18/0.40  fof(f116,plain,(
% 0.18/0.40    ( ! [X4] : (r2_hidden(sK4(k1_xboole_0,X4),X4) | k1_xboole_0 = X4) )),
% 0.18/0.40    inference(forward_demodulation,[],[f113,f36])).
% 0.18/0.40  fof(f36,plain,(
% 0.18/0.40    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.18/0.40    inference(cnf_transformation,[],[f6])).
% 0.18/0.40  fof(f6,axiom,(
% 0.18/0.40    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.18/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.18/0.40  fof(f113,plain,(
% 0.18/0.40    ( ! [X4] : (k2_relat_1(k1_xboole_0) = X4 | r2_hidden(sK4(k1_xboole_0,X4),X4)) )),
% 0.18/0.40    inference(resolution,[],[f51,f84])).
% 0.18/0.40  fof(f84,plain,(
% 0.18/0.40    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.18/0.40    inference(superposition,[],[f48,f60])).
% 0.18/0.40  fof(f60,plain,(
% 0.18/0.40    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.18/0.40    inference(equality_resolution,[],[f57])).
% 0.18/0.40  fof(f57,plain,(
% 0.18/0.40    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.18/0.40    inference(cnf_transformation,[],[f32])).
% 0.18/0.40  fof(f32,plain,(
% 0.18/0.40    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.18/0.40    inference(flattening,[],[f31])).
% 0.18/0.40  fof(f31,plain,(
% 0.18/0.40    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.18/0.40    inference(nnf_transformation,[],[f3])).
% 0.18/0.40  fof(f3,axiom,(
% 0.18/0.40    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.18/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.18/0.40  fof(f48,plain,(
% 0.18/0.40    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.18/0.40    inference(cnf_transformation,[],[f4])).
% 0.18/0.40  fof(f4,axiom,(
% 0.18/0.40    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.18/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.18/0.40  fof(f51,plain,(
% 0.18/0.40    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | k2_relat_1(X0) = X1 | r2_hidden(sK4(X0,X1),X1)) )),
% 0.18/0.40    inference(cnf_transformation,[],[f29])).
% 0.18/0.40  fof(f29,plain,(
% 0.18/0.40    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.18/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f28,f27,f26])).
% 0.18/0.40  fof(f26,plain,(
% 0.18/0.40    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 0.18/0.40    introduced(choice_axiom,[])).
% 0.18/0.40  fof(f27,plain,(
% 0.18/0.40    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0) => r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0))),
% 0.18/0.40    introduced(choice_axiom,[])).
% 0.18/0.40  fof(f28,plain,(
% 0.18/0.40    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0))),
% 0.18/0.40    introduced(choice_axiom,[])).
% 0.18/0.40  fof(f25,plain,(
% 0.18/0.40    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.18/0.40    inference(rectify,[],[f24])).
% 0.18/0.40  fof(f24,plain,(
% 0.18/0.40    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.18/0.40    inference(nnf_transformation,[],[f5])).
% 0.18/0.40  fof(f5,axiom,(
% 0.18/0.40    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.18/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.18/0.40  fof(f68,plain,(
% 0.18/0.40    ~spl7_1 | spl7_2),
% 0.18/0.40    inference(avatar_split_clause,[],[f33,f66,f63])).
% 0.18/0.40  fof(f33,plain,(
% 0.18/0.40    k1_xboole_0 = sK1 | k1_xboole_0 != sK0),
% 0.18/0.40    inference(cnf_transformation,[],[f18])).
% 0.18/0.40  % SZS output end Proof for theBenchmark
% 0.18/0.40  % (3936)------------------------------
% 0.18/0.40  % (3936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.40  % (3936)Termination reason: Refutation
% 0.18/0.40  
% 0.18/0.40  % (3936)Memory used [KB]: 10618
% 0.18/0.40  % (3936)Time elapsed: 0.042 s
% 0.18/0.40  % (3936)------------------------------
% 0.18/0.40  % (3936)------------------------------
% 0.18/0.40  % (3933)Success in time 0.072 s
%------------------------------------------------------------------------------
