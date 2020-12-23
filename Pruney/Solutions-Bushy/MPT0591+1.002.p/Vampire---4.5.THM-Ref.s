%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0591+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 191 expanded)
%              Number of leaves         :   24 (  69 expanded)
%              Depth                    :   12
%              Number of atoms          :  295 ( 692 expanded)
%              Number of equality atoms :   59 ( 154 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f437,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f130,f139,f286,f400,f411,f414,f427,f430,f436])).

fof(f436,plain,(
    ~ spl9_16 ),
    inference(avatar_contradiction_clause,[],[f435])).

fof(f435,plain,
    ( $false
    | ~ spl9_16 ),
    inference(resolution,[],[f426,f47])).

fof(f47,plain,(
    ! [X0] : m1_subset_1(sK8(X0),X0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] : m1_subset_1(sK8(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f3,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK8(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f426,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK1)
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f425])).

fof(f425,plain,
    ( spl9_16
  <=> ! [X0] : ~ m1_subset_1(X0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f430,plain,(
    ~ spl9_15 ),
    inference(avatar_contradiction_clause,[],[f429])).

fof(f429,plain,
    ( $false
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f428,f32])).

fof(f32,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1))
      | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) )
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) != X1
          | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ( sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1))
        | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) )
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) != X1
        | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
              & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

fof(f428,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_15 ),
    inference(resolution,[],[f397,f45])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f397,plain,
    ( v1_xboole_0(sK1)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f395])).

fof(f395,plain,
    ( spl9_15
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f427,plain,
    ( spl9_16
    | spl9_15
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f415,f76,f395,f425])).

fof(f76,plain,
    ( spl9_4
  <=> ! [X0] : ~ r2_hidden(X0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f415,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1) )
    | ~ spl9_4 ),
    inference(resolution,[],[f77,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f77,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f414,plain,
    ( ~ spl9_3
    | spl9_4
    | spl9_1 ),
    inference(avatar_split_clause,[],[f65,f53,f76,f72])).

fof(f72,plain,
    ( spl9_3
  <=> r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f53,plain,
    ( spl9_1
  <=> sK0 = k1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f65,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),sK0),sK0) )
    | spl9_1 ),
    inference(resolution,[],[f64,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f64,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK5(k2_zfmisc_1(sK0,sK1),sK0),X0),k2_zfmisc_1(sK0,sK1))
    | spl9_1 ),
    inference(subsumption_resolution,[],[f63,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK5(k2_zfmisc_1(sK0,sK1),sK0),X0),k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),sK0),sK0) )
    | spl9_1 ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,
    ( ! [X2,X1] :
        ( sK0 != X1
        | ~ r2_hidden(k4_tarski(sK5(k2_zfmisc_1(sK0,sK1),X1),X2),k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),X1),X1) )
    | spl9_1 ),
    inference(superposition,[],[f55,f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( k1_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f22,f25,f24,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f55,plain,
    ( sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f411,plain,
    ( spl9_7
    | ~ spl9_11 ),
    inference(avatar_contradiction_clause,[],[f410])).

fof(f410,plain,
    ( $false
    | spl9_7
    | ~ spl9_11 ),
    inference(resolution,[],[f281,f147])).

fof(f147,plain,
    ( r2_hidden(sK8(sK0),sK0)
    | spl9_7 ),
    inference(resolution,[],[f146,f47])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | r2_hidden(X0,sK0) )
    | spl9_7 ),
    inference(resolution,[],[f107,f46])).

fof(f107,plain,
    ( ~ v1_xboole_0(sK0)
    | spl9_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl9_7
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f281,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl9_11
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f400,plain,
    ( spl9_2
    | spl9_12 ),
    inference(avatar_contradiction_clause,[],[f399])).

fof(f399,plain,
    ( $false
    | spl9_2
    | spl9_12 ),
    inference(subsumption_resolution,[],[f287,f285])).

fof(f285,plain,
    ( ~ r2_hidden(sK2(k2_zfmisc_1(sK0,sK1),sK1),sK1)
    | spl9_12 ),
    inference(avatar_component_clause,[],[f283])).

fof(f283,plain,
    ( spl9_12
  <=> r2_hidden(sK2(k2_zfmisc_1(sK0,sK1),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f287,plain,
    ( r2_hidden(sK2(k2_zfmisc_1(sK0,sK1),sK1),sK1)
    | spl9_2 ),
    inference(subsumption_resolution,[],[f274,f59])).

fof(f59,plain,
    ( sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl9_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl9_2
  <=> sK1 = k2_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f274,plain,
    ( sK1 = k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | r2_hidden(sK2(k2_zfmisc_1(sK0,sK1),sK1),sK1)
    | spl9_2 ),
    inference(resolution,[],[f254,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f19,f18,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f15,plain,(
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

fof(f254,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK2(k2_zfmisc_1(sK0,sK1),sK1)),k2_zfmisc_1(sK0,sK1))
    | spl9_2 ),
    inference(subsumption_resolution,[],[f253,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f253,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK2(k2_zfmisc_1(sK0,sK1),sK1)),k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(sK2(k2_zfmisc_1(sK0,sK1),sK1),sK1) )
    | spl9_2 ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,
    ( ! [X2,X1] :
        ( sK1 != X1
        | ~ r2_hidden(k4_tarski(X2,sK2(k2_zfmisc_1(sK0,sK1),X1)),k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(sK2(k2_zfmisc_1(sK0,sK1),X1),X1) )
    | spl9_2 ),
    inference(superposition,[],[f59,f37])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f286,plain,
    ( spl9_11
    | ~ spl9_12
    | spl9_2 ),
    inference(avatar_split_clause,[],[f273,f57,f283,f280])).

fof(f273,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(k2_zfmisc_1(sK0,sK1),sK1),sK1)
        | ~ r2_hidden(X0,sK0) )
    | spl9_2 ),
    inference(resolution,[],[f254,f44])).

fof(f139,plain,(
    ~ spl9_7 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f137,f31])).

fof(f31,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).

fof(f137,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_7 ),
    inference(resolution,[],[f108,f45])).

fof(f108,plain,
    ( v1_xboole_0(sK0)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f130,plain,
    ( spl9_1
    | spl9_3 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl9_1
    | spl9_3 ),
    inference(subsumption_resolution,[],[f79,f74])).

fof(f74,plain,
    ( ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),sK0),sK0)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f79,plain,
    ( r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),sK0),sK0)
    | spl9_1 ),
    inference(subsumption_resolution,[],[f66,f55])).

fof(f66,plain,
    ( sK0 = k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),sK0),sK0)
    | spl9_1 ),
    inference(resolution,[],[f64,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f60,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f33,f57,f53])).

fof(f33,plain,
    ( sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

%------------------------------------------------------------------------------
