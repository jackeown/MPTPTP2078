%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0570+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 254 expanded)
%              Number of leaves         :   25 (  81 expanded)
%              Depth                    :   15
%              Number of atoms          :  329 ( 781 expanded)
%              Number of equality atoms :   34 ( 123 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f581,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f173,f176,f323,f487,f533,f541,f563,f565,f576])).

fof(f576,plain,
    ( spl8_23
    | spl8_11
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f569,f526,f276,f485])).

fof(f485,plain,
    ( spl8_23
  <=> ! [X2] : ~ m1_subset_1(X2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f276,plain,
    ( spl8_11
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f526,plain,
    ( spl8_24
  <=> r1_tarski(sK0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f569,plain,
    ( ! [X2] :
        ( v1_xboole_0(sK0)
        | ~ m1_subset_1(X2,sK0) )
    | ~ spl8_24 ),
    inference(resolution,[],[f566,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f566,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl8_24 ),
    inference(resolution,[],[f528,f74])).

fof(f74,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,o_0_0_xboole_0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f72,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f63,f45])).

fof(f45,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f528,plain,
    ( r1_tarski(sK0,o_0_0_xboole_0)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f526])).

fof(f565,plain,(
    ~ spl8_23 ),
    inference(avatar_contradiction_clause,[],[f564])).

fof(f564,plain,
    ( $false
    | ~ spl8_23 ),
    inference(resolution,[],[f486,f47])).

fof(f47,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f4,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f486,plain,
    ( ! [X2] : ~ m1_subset_1(X2,sK0)
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f485])).

fof(f563,plain,
    ( spl8_19
    | ~ spl8_20
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f519,f170,f379,f376])).

fof(f376,plain,
    ( spl8_19
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f379,plain,
    ( spl8_20
  <=> r2_hidden(sK3(sK0,o_0_0_xboole_0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f170,plain,
    ( spl8_10
  <=> v1_xboole_0(k10_relat_1(sK1,sK2(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f519,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK0,o_0_0_xboole_0),k2_relat_1(sK1))
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_10 ),
    inference(resolution,[],[f272,f74])).

fof(f272,plain,
    ( ! [X4] :
        ( r1_tarski(sK0,X4)
        | ~ r2_hidden(sK3(sK0,X4),k2_relat_1(sK1)) )
    | ~ spl8_10 ),
    inference(resolution,[],[f267,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f267,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK0)
        | ~ r2_hidden(X2,k2_relat_1(sK1)) )
    | ~ spl8_10 ),
    inference(duplicate_literal_removal,[],[f263])).

fof(f263,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_relat_1(sK1))
        | ~ r2_hidden(X2,sK0)
        | ~ r2_hidden(X2,k2_relat_1(sK1)) )
    | ~ spl8_10 ),
    inference(resolution,[],[f258,f65])).

fof(f65,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f31,f34,f33,f32])).

fof(f32,plain,(
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

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f258,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ r2_hidden(X1,k2_relat_1(sK1))
        | ~ r2_hidden(X1,sK0) )
    | ~ spl8_10 ),
    inference(resolution,[],[f256,f180])).

fof(f180,plain,
    ( ! [X5] : ~ r2_hidden(X5,o_0_0_xboole_0)
    | ~ spl8_10 ),
    inference(backward_demodulation,[],[f151,f179])).

fof(f179,plain,
    ( o_0_0_xboole_0 = k10_relat_1(sK1,sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl8_10 ),
    inference(resolution,[],[f172,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(backward_demodulation,[],[f46,f66])).

fof(f66,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[],[f46,f45])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f172,plain,
    ( v1_xboole_0(k10_relat_1(sK1,sK2(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f170])).

fof(f151,plain,(
    ! [X5] : ~ r2_hidden(X5,k10_relat_1(sK1,sK2(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    inference(resolution,[],[f73,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1,sK1),X1)
      | ~ r2_hidden(X0,k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f61,f41])).

fof(f41,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    & r1_tarski(sK0,k2_relat_1(sK1))
    & k1_xboole_0 != sK0
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k10_relat_1(X1,X0)
        & r1_tarski(X0,k2_relat_1(X1))
        & k1_xboole_0 != X0
        & v1_relat_1(X1) )
   => ( k1_xboole_0 = k10_relat_1(sK1,sK0)
      & r1_tarski(sK0,k2_relat_1(sK1))
      & k1_xboole_0 != sK0
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      & r1_tarski(X0,k2_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      & r1_tarski(X0,k2_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
            & r1_tarski(X0,k2_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(sK7(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK7(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK7(X0,X1,X2)),X2)
            & r2_hidden(sK7(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK7(X0,X1,X2)),X2)
        & r2_hidden(sK7(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

% (5361)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f73,plain,(
    ! [X0] : ~ r2_hidden(X0,sK2(k1_zfmisc_1(o_0_0_xboole_0))) ),
    inference(resolution,[],[f72,f47])).

fof(f256,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,o_0_0_xboole_0)
      | ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | ~ r2_hidden(X1,k2_relat_1(sK1))
      | ~ r2_hidden(X1,sK0) ) ),
    inference(superposition,[],[f254,f69])).

fof(f69,plain,(
    o_0_0_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f44,f66])).

fof(f44,plain,(
    k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f254,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_relat_1(sK1,X1))
      | ~ r2_hidden(k4_tarski(X2,X0),sK1)
      | ~ r2_hidden(X0,k2_relat_1(sK1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f62,f41])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f541,plain,(
    spl8_25 ),
    inference(avatar_contradiction_clause,[],[f537])).

fof(f537,plain,
    ( $false
    | spl8_25 ),
    inference(resolution,[],[f532,f43])).

fof(f43,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f532,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK1))
    | spl8_25 ),
    inference(avatar_component_clause,[],[f530])).

fof(f530,plain,
    ( spl8_25
  <=> r1_tarski(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f533,plain,
    ( spl8_24
    | ~ spl8_25
    | spl8_20 ),
    inference(avatar_split_clause,[],[f521,f379,f530,f526])).

fof(f521,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK1))
    | r1_tarski(sK0,o_0_0_xboole_0)
    | spl8_20 ),
    inference(resolution,[],[f498,f50])).

fof(f498,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3(sK0,o_0_0_xboole_0),X1)
        | ~ r1_tarski(X1,k2_relat_1(sK1)) )
    | spl8_20 ),
    inference(resolution,[],[f381,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f381,plain,
    ( ~ r2_hidden(sK3(sK0,o_0_0_xboole_0),k2_relat_1(sK1))
    | spl8_20 ),
    inference(avatar_component_clause,[],[f379])).

fof(f487,plain,
    ( spl8_23
    | spl8_11
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f478,f376,f276,f485])).

fof(f478,plain,
    ( ! [X2] :
        ( v1_xboole_0(sK0)
        | ~ m1_subset_1(X2,sK0) )
    | ~ spl8_19 ),
    inference(resolution,[],[f377,f48])).

fof(f377,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f376])).

fof(f323,plain,(
    ~ spl8_11 ),
    inference(avatar_contradiction_clause,[],[f322])).

fof(f322,plain,
    ( $false
    | ~ spl8_11 ),
    inference(trivial_inequality_removal,[],[f321])).

fof(f321,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0
    | ~ spl8_11 ),
    inference(superposition,[],[f68,f299])).

fof(f299,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl8_11 ),
    inference(resolution,[],[f278,f67])).

fof(f278,plain,
    ( v1_xboole_0(sK0)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f276])).

fof(f68,plain,(
    o_0_0_xboole_0 != sK0 ),
    inference(backward_demodulation,[],[f42,f66])).

fof(f42,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f23])).

fof(f176,plain,(
    ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | ~ spl8_9 ),
    inference(resolution,[],[f168,f47])).

fof(f168,plain,
    ( ! [X2] : ~ m1_subset_1(X2,k10_relat_1(sK1,sK2(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl8_9
  <=> ! [X2] : ~ m1_subset_1(X2,k10_relat_1(sK1,sK2(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f173,plain,
    ( spl8_9
    | spl8_10 ),
    inference(avatar_split_clause,[],[f162,f170,f167])).

fof(f162,plain,(
    ! [X2] :
      ( v1_xboole_0(k10_relat_1(sK1,sK2(k1_zfmisc_1(o_0_0_xboole_0))))
      | ~ m1_subset_1(X2,k10_relat_1(sK1,sK2(k1_zfmisc_1(o_0_0_xboole_0)))) ) ),
    inference(resolution,[],[f151,f48])).

%------------------------------------------------------------------------------
