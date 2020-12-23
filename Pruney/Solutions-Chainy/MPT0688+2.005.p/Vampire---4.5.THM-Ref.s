%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 143 expanded)
%              Number of leaves         :   12 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  248 ( 802 expanded)
%              Number of equality atoms :   50 ( 136 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f218,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f84,f187,f213,f217])).

fof(f217,plain,(
    ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f45,f80])).

fof(f80,plain,
    ( ! [X0,X1] : ~ r1_tarski(X0,X1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_3
  <=> ! [X1,X0] : ~ r1_tarski(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f213,plain,
    ( spl3_1
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | spl3_1
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f209,f53])).

fof(f53,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_1
  <=> r1_tarski(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f209,plain,
    ( r1_tarski(sK0,k2_relat_1(sK1))
    | ~ spl3_7 ),
    inference(trivial_inequality_removal,[],[f201])).

fof(f201,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k2_relat_1(sK1))
    | ~ spl3_7 ),
    inference(superposition,[],[f28,f186])).

fof(f186,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_relat_1(sK1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl3_7
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f187,plain,
    ( spl3_7
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f182,f82,f56,f184])).

fof(f56,plain,
    ( spl3_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f82,plain,
    ( spl3_4
  <=> ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f182,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_relat_1(sK1))
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f172,f98])).

fof(f98,plain,
    ( ! [X9] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X9)
    | ~ spl3_4 ),
    inference(resolution,[],[f76,f83])).

fof(f83,plain,
    ( ! [X2] : ~ r2_hidden(X2,k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f172,plain,
    ( ! [X13] : k4_xboole_0(sK0,k2_relat_1(sK1)) = k4_xboole_0(k1_xboole_0,X13)
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(resolution,[],[f154,f83])).

fof(f154,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(X0,X1,k4_xboole_0(sK0,k2_relat_1(sK1))),X0)
        | k4_xboole_0(X0,X1) = k4_xboole_0(sK0,k2_relat_1(sK1)) )
    | ~ spl3_2 ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(X0,X1,k4_xboole_0(sK0,k2_relat_1(sK1))),X0)
        | k4_xboole_0(X0,X1) = k4_xboole_0(sK0,k2_relat_1(sK1))
        | k4_xboole_0(X0,X1) = k4_xboole_0(sK0,k2_relat_1(sK1))
        | r2_hidden(sK2(X0,X1,k4_xboole_0(sK0,k2_relat_1(sK1))),X0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f129,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK2(X0,X1,k4_xboole_0(X2,X3)),X2)
      | k4_xboole_0(X0,X1) = k4_xboole_0(X2,X3)
      | r2_hidden(sK2(X0,X1,k4_xboole_0(X2,X3)),X0) ) ),
    inference(resolution,[],[f38,f49])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f129,plain,
    ( ! [X10,X8,X9] :
        ( ~ r2_hidden(sK2(X9,X10,k4_xboole_0(X8,k2_relat_1(sK1))),sK0)
        | r2_hidden(sK2(X9,X10,k4_xboole_0(X8,k2_relat_1(sK1))),X9)
        | k4_xboole_0(X8,k2_relat_1(sK1)) = k4_xboole_0(X9,X10) )
    | ~ spl3_2 ),
    inference(resolution,[],[f74,f72])).

fof(f72,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_relat_1(sK1))
        | ~ r2_hidden(X0,sK0) )
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f71,f58])).

fof(f58,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f71,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(X0,k2_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(trivial_inequality_removal,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(X0,sK0)
      | r2_hidden(X0,k2_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f26,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
      | r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k2_relat_1(X1))
          | k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) )
        & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
          | ~ r2_hidden(X0,k2_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

fof(f26,plain,(
    ! [X2] :
      ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(X2))
      | ~ r2_hidden(X2,sK0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK1))
    & ! [X2] :
        ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(X2))
        | ~ r2_hidden(X2,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k2_relat_1(X1))
        & ! [X2] :
            ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2))
            | ~ r2_hidden(X2,X0) )
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k2_relat_1(sK1))
      & ! [X2] :
          ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(X2))
          | ~ r2_hidden(X2,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      & ! [X2] :
          ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2))
          | ~ r2_hidden(X2,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      & ! [X2] :
          ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2))
          | ~ r2_hidden(X2,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( ! [X2] :
              ~ ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
                & r2_hidden(X2,X0) )
         => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ~ ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
              & r2_hidden(X2,X0) )
       => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_1)).

fof(f74,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(sK2(X4,X5,k4_xboole_0(X6,X7)),X7)
      | k4_xboole_0(X6,X7) = k4_xboole_0(X4,X5)
      | r2_hidden(sK2(X4,X5,k4_xboole_0(X6,X7)),X4) ) ),
    inference(resolution,[],[f38,f48])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f84,plain,
    ( spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f77,f82,f79])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f62,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f61,f45])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(superposition,[],[f48,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f49,f29])).

fof(f59,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f25,f56])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f54,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f27,f51])).

fof(f27,plain,(
    ~ r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:27:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (8001)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (8006)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (8006)Refutation not found, incomplete strategy% (8006)------------------------------
% 0.21/0.52  % (8006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (8017)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (8018)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (8011)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (7998)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (8006)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (8006)Memory used [KB]: 10618
% 0.21/0.52  % (8006)Time elapsed: 0.104 s
% 0.21/0.52  % (8006)------------------------------
% 0.21/0.52  % (8006)------------------------------
% 0.21/0.53  % (8004)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (8010)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (8015)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (8019)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (7996)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (8022)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (8023)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (7997)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (8023)Refutation not found, incomplete strategy% (8023)------------------------------
% 0.21/0.53  % (8023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (8023)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (8023)Memory used [KB]: 6140
% 0.21/0.53  % (8023)Time elapsed: 0.126 s
% 0.21/0.53  % (8023)------------------------------
% 0.21/0.53  % (8023)------------------------------
% 0.21/0.53  % (7997)Refutation not found, incomplete strategy% (7997)------------------------------
% 0.21/0.53  % (7997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (7997)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (7997)Memory used [KB]: 1663
% 0.21/0.53  % (7997)Time elapsed: 0.122 s
% 0.21/0.53  % (7997)------------------------------
% 0.21/0.53  % (7997)------------------------------
% 0.21/0.53  % (8024)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (8002)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (8012)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (8012)Refutation not found, incomplete strategy% (8012)------------------------------
% 0.21/0.54  % (8012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8012)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (8012)Memory used [KB]: 10618
% 0.21/0.54  % (8012)Time elapsed: 0.120 s
% 0.21/0.54  % (8012)------------------------------
% 0.21/0.54  % (8012)------------------------------
% 0.21/0.54  % (8016)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (8009)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (8007)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (8003)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (8000)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (8021)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (8024)Refutation not found, incomplete strategy% (8024)------------------------------
% 0.21/0.54  % (8024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8024)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (8024)Memory used [KB]: 10618
% 0.21/0.54  % (8024)Time elapsed: 0.127 s
% 0.21/0.54  % (8024)------------------------------
% 0.21/0.54  % (8024)------------------------------
% 0.21/0.54  % (8005)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (8013)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (8017)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % (8025)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (8020)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (7999)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.55  % (8008)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f218,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f54,f59,f84,f187,f213,f217])).
% 0.21/0.55  fof(f217,plain,(
% 0.21/0.55    ~spl3_3),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f214])).
% 0.21/0.55  fof(f214,plain,(
% 0.21/0.55    $false | ~spl3_3),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f45,f80])).
% 0.21/0.55  fof(f80,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1)) ) | ~spl3_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f79])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    spl3_3 <=> ! [X1,X0] : ~r1_tarski(X0,X1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.55    inference(equality_resolution,[],[f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.55    inference(flattening,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.55  fof(f213,plain,(
% 0.21/0.55    spl3_1 | ~spl3_7),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f212])).
% 0.21/0.55  fof(f212,plain,(
% 0.21/0.55    $false | (spl3_1 | ~spl3_7)),
% 0.21/0.55    inference(subsumption_resolution,[],[f209,f53])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ~r1_tarski(sK0,k2_relat_1(sK1)) | spl3_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f51])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    spl3_1 <=> r1_tarski(sK0,k2_relat_1(sK1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.55  fof(f209,plain,(
% 0.21/0.55    r1_tarski(sK0,k2_relat_1(sK1)) | ~spl3_7),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f201])).
% 0.21/0.55  fof(f201,plain,(
% 0.21/0.55    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,k2_relat_1(sK1)) | ~spl3_7),
% 0.21/0.55    inference(superposition,[],[f28,f186])).
% 0.21/0.55  fof(f186,plain,(
% 0.21/0.55    k1_xboole_0 = k4_xboole_0(sK0,k2_relat_1(sK1)) | ~spl3_7),
% 0.21/0.55    inference(avatar_component_clause,[],[f184])).
% 0.21/0.55  fof(f184,plain,(
% 0.21/0.55    spl3_7 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_relat_1(sK1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.55    inference(nnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.55  fof(f187,plain,(
% 0.21/0.55    spl3_7 | ~spl3_2 | ~spl3_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f182,f82,f56,f184])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    spl3_2 <=> v1_relat_1(sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.55  fof(f82,plain,(
% 0.21/0.55    spl3_4 <=> ! [X2] : ~r2_hidden(X2,k1_xboole_0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.55  fof(f182,plain,(
% 0.21/0.55    k1_xboole_0 = k4_xboole_0(sK0,k2_relat_1(sK1)) | (~spl3_2 | ~spl3_4)),
% 0.21/0.55    inference(forward_demodulation,[],[f172,f98])).
% 0.21/0.55  fof(f98,plain,(
% 0.21/0.55    ( ! [X9] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X9)) ) | ~spl3_4),
% 0.21/0.55    inference(resolution,[],[f76,f83])).
% 0.21/0.55  fof(f83,plain,(
% 0.21/0.55    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) ) | ~spl3_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f82])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) )),
% 0.21/0.55    inference(factoring,[],[f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(rectify,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(flattening,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(nnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.55  fof(f172,plain,(
% 0.21/0.55    ( ! [X13] : (k4_xboole_0(sK0,k2_relat_1(sK1)) = k4_xboole_0(k1_xboole_0,X13)) ) | (~spl3_2 | ~spl3_4)),
% 0.21/0.55    inference(resolution,[],[f154,f83])).
% 0.21/0.55  fof(f154,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,k4_xboole_0(sK0,k2_relat_1(sK1))),X0) | k4_xboole_0(X0,X1) = k4_xboole_0(sK0,k2_relat_1(sK1))) ) | ~spl3_2),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f151])).
% 0.21/0.55  fof(f151,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,k4_xboole_0(sK0,k2_relat_1(sK1))),X0) | k4_xboole_0(X0,X1) = k4_xboole_0(sK0,k2_relat_1(sK1)) | k4_xboole_0(X0,X1) = k4_xboole_0(sK0,k2_relat_1(sK1)) | r2_hidden(sK2(X0,X1,k4_xboole_0(sK0,k2_relat_1(sK1))),X0)) ) | ~spl3_2),
% 0.21/0.55    inference(resolution,[],[f129,f73])).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(sK2(X0,X1,k4_xboole_0(X2,X3)),X2) | k4_xboole_0(X0,X1) = k4_xboole_0(X2,X3) | r2_hidden(sK2(X0,X1,k4_xboole_0(X2,X3)),X0)) )),
% 0.21/0.55    inference(resolution,[],[f38,f49])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 0.21/0.55    inference(equality_resolution,[],[f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f129,plain,(
% 0.21/0.55    ( ! [X10,X8,X9] : (~r2_hidden(sK2(X9,X10,k4_xboole_0(X8,k2_relat_1(sK1))),sK0) | r2_hidden(sK2(X9,X10,k4_xboole_0(X8,k2_relat_1(sK1))),X9) | k4_xboole_0(X8,k2_relat_1(sK1)) = k4_xboole_0(X9,X10)) ) | ~spl3_2),
% 0.21/0.55    inference(resolution,[],[f74,f72])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK1)) | ~r2_hidden(X0,sK0)) ) | ~spl3_2),
% 0.21/0.55    inference(subsumption_resolution,[],[f71,f58])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    v1_relat_1(sK1) | ~spl3_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f56])).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(X0,k2_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f68])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(X0,sK0) | r2_hidden(X0,k2_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 0.21/0.55    inference(superposition,[],[f26,f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0,X1] : (((r2_hidden(X0,k2_relat_1(X1)) | k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1)))) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ! [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ( ! [X2] : (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(X2)) | ~r2_hidden(X2,sK0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ~r1_tarski(sK0,k2_relat_1(sK1)) & ! [X2] : (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(X2)) | ~r2_hidden(X2,sK0)) & v1_relat_1(sK1)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ? [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) & ! [X2] : (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2)) | ~r2_hidden(X2,X0)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k2_relat_1(sK1)) & ! [X2] : (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(X2)) | ~r2_hidden(X2,sK0)) & v1_relat_1(sK1))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f12,plain,(
% 0.21/0.55    ? [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) & ! [X2] : (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2)) | ~r2_hidden(X2,X0)) & v1_relat_1(X1))),
% 0.21/0.55    inference(flattening,[],[f11])).
% 0.21/0.55  fof(f11,plain,(
% 0.21/0.55    ? [X0,X1] : ((~r1_tarski(X0,k2_relat_1(X1)) & ! [X2] : (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2)) | ~r2_hidden(X2,X0))) & v1_relat_1(X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1] : (v1_relat_1(X1) => (! [X2] : ~(k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2)) & r2_hidden(X2,X0)) => r1_tarski(X0,k2_relat_1(X1))))),
% 0.21/0.55    inference(negated_conjecture,[],[f9])).
% 0.21/0.55  fof(f9,conjecture,(
% 0.21/0.55    ! [X0,X1] : (v1_relat_1(X1) => (! [X2] : ~(k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2)) & r2_hidden(X2,X0)) => r1_tarski(X0,k2_relat_1(X1))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_1)).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    ( ! [X6,X4,X7,X5] : (~r2_hidden(sK2(X4,X5,k4_xboole_0(X6,X7)),X7) | k4_xboole_0(X6,X7) = k4_xboole_0(X4,X5) | r2_hidden(sK2(X4,X5,k4_xboole_0(X6,X7)),X4)) )),
% 0.21/0.55    inference(resolution,[],[f38,f48])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.21/0.55    inference(equality_resolution,[],[f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f84,plain,(
% 0.21/0.55    spl3_3 | spl3_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f77,f82,f79])).
% 0.21/0.55  fof(f77,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_xboole_0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f62,f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(resolution,[],[f61,f45])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,k1_xboole_0)) )),
% 0.21/0.55    inference(superposition,[],[f48,f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_xboole_0) | r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(superposition,[],[f49,f29])).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    spl3_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f25,f56])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    v1_relat_1(sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ~spl3_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f27,f51])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ~r1_tarski(sK0,k2_relat_1(sK1))),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (8017)------------------------------
% 0.21/0.55  % (8017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (8017)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (8017)Memory used [KB]: 6396
% 0.21/0.55  % (8017)Time elapsed: 0.142 s
% 0.21/0.55  % (8017)------------------------------
% 0.21/0.55  % (8017)------------------------------
% 0.21/0.55  % (7994)Success in time 0.191 s
%------------------------------------------------------------------------------
