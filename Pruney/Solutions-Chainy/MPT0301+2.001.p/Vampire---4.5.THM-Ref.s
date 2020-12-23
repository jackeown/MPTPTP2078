%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:52 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 197 expanded)
%              Number of leaves         :   23 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :  360 ( 799 expanded)
%              Number of equality atoms :  113 ( 277 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f648,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f177,f182,f183,f355,f391,f611,f633,f647])).

fof(f647,plain,
    ( spl12_3
    | ~ spl12_10 ),
    inference(avatar_contradiction_clause,[],[f646])).

fof(f646,plain,
    ( $false
    | spl12_3
    | ~ spl12_10 ),
    inference(subsumption_resolution,[],[f639,f181])).

fof(f181,plain,
    ( k1_xboole_0 != sK0
    | spl12_3 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl12_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f639,plain,
    ( k1_xboole_0 = sK0
    | ~ spl12_10 ),
    inference(resolution,[],[f607,f443])).

fof(f443,plain,(
    ! [X4] :
      ( r2_hidden(sK5(X4,k1_xboole_0),X4)
      | k1_xboole_0 = X4 ) ),
    inference(resolution,[],[f439,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f62,f63])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f439,plain,(
    ! [X12] :
      ( ~ r1_tarski(X12,k1_xboole_0)
      | k1_xboole_0 = X12 ) ),
    inference(condensation,[],[f435])).

fof(f435,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,X13)
      | ~ r1_tarski(X12,k1_xboole_0)
      | k1_xboole_0 = X12 ) ),
    inference(resolution,[],[f420,f198])).

fof(f198,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f194,f88])).

fof(f88,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f194,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f97,f87])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f97,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).

fof(f420,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | k1_xboole_0 = X2 ) ),
    inference(resolution,[],[f132,f91])).

fof(f91,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f132,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

fof(f607,plain,
    ( ! [X6] : ~ r2_hidden(X6,sK0)
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f606])).

fof(f606,plain,
    ( spl12_10
  <=> ! [X6] : ~ r2_hidden(X6,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f633,plain,
    ( spl12_2
    | ~ spl12_11 ),
    inference(avatar_contradiction_clause,[],[f632])).

fof(f632,plain,
    ( $false
    | spl12_2
    | ~ spl12_11 ),
    inference(subsumption_resolution,[],[f625,f176])).

fof(f176,plain,
    ( k1_xboole_0 != sK1
    | spl12_2 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl12_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f625,plain,
    ( k1_xboole_0 = sK1
    | ~ spl12_11 ),
    inference(resolution,[],[f610,f443])).

fof(f610,plain,
    ( ! [X7] : ~ r2_hidden(X7,sK1)
    | ~ spl12_11 ),
    inference(avatar_component_clause,[],[f609])).

fof(f609,plain,
    ( spl12_11
  <=> ! [X7] : ~ r2_hidden(X7,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).

fof(f611,plain,
    ( spl12_10
    | spl12_11
    | ~ spl12_1 ),
    inference(avatar_split_clause,[],[f604,f170,f609,f606])).

fof(f170,plain,
    ( spl12_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f604,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(X7,sK1)
        | ~ r2_hidden(X6,sK0) )
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f603,f267])).

fof(f267,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f263])).

fof(f263,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f103,f85])).

fof(f85,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f59])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f603,plain,
    ( ! [X6,X7] :
        ( r2_hidden(k4_tarski(X6,X7),k1_xboole_0)
        | ~ r2_hidden(X7,sK1)
        | ~ r2_hidden(X6,sK0) )
    | ~ spl12_1 ),
    inference(superposition,[],[f161,f171])).

fof(f171,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f170])).

fof(f161,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f160])).

fof(f160,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK7(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( sK7(X0,X1,X2) = k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2))
              & r2_hidden(sK9(X0,X1,X2),X1)
              & r2_hidden(sK8(X0,X1,X2),X0) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8
                & r2_hidden(sK11(X0,X1,X8),X1)
                & r2_hidden(sK10(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10,sK11])],[f72,f75,f74,f73])).

fof(f73,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK7(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK7(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK7(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK7(X0,X1,X2) = k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2))
        & r2_hidden(sK9(X0,X1,X2),X1)
        & r2_hidden(sK8(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8
        & r2_hidden(sK11(X0,X1,X8),X1)
        & r2_hidden(sK10(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f391,plain,
    ( spl12_1
    | ~ spl12_3 ),
    inference(avatar_contradiction_clause,[],[f390])).

fof(f390,plain,
    ( $false
    | spl12_1
    | ~ spl12_3 ),
    inference(trivial_inequality_removal,[],[f389])).

fof(f389,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl12_1
    | ~ spl12_3 ),
    inference(superposition,[],[f356,f374])).

fof(f374,plain,(
    ! [X4] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X4) ),
    inference(resolution,[],[f368,f95])).

fof(f95,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f368,plain,(
    ! [X4,X3] : ~ r2_hidden(X3,k2_zfmisc_1(k1_xboole_0,X4)) ),
    inference(resolution,[],[f164,f267])).

fof(f164,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK10(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f119])).

fof(f119,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK10(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f76])).

fof(f356,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl12_1
    | ~ spl12_3 ),
    inference(forward_demodulation,[],[f172,f180])).

fof(f180,plain,
    ( k1_xboole_0 = sK0
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f179])).

fof(f172,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f170])).

fof(f355,plain,
    ( spl12_1
    | ~ spl12_2 ),
    inference(avatar_contradiction_clause,[],[f354])).

fof(f354,plain,
    ( $false
    | spl12_1
    | ~ spl12_2 ),
    inference(trivial_inequality_removal,[],[f353])).

fof(f353,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl12_1
    | ~ spl12_2 ),
    inference(superposition,[],[f184,f342])).

fof(f342,plain,(
    ! [X4] : k1_xboole_0 = k2_zfmisc_1(X4,k1_xboole_0) ),
    inference(resolution,[],[f336,f95])).

fof(f336,plain,(
    ! [X4,X3] : ~ r2_hidden(X3,k2_zfmisc_1(X4,k1_xboole_0)) ),
    inference(resolution,[],[f163,f267])).

fof(f163,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK11(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK11(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f76])).

fof(f184,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl12_1
    | ~ spl12_2 ),
    inference(forward_demodulation,[],[f172,f175])).

fof(f175,plain,
    ( k1_xboole_0 = sK1
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f174])).

fof(f183,plain,
    ( spl12_1
    | spl12_3
    | spl12_2 ),
    inference(avatar_split_clause,[],[f79,f174,f179,f170])).

fof(f79,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ( ( k1_xboole_0 != sK1
        & k1_xboole_0 != sK0 )
      | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f50,f51])).

fof(f51,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 != X1
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) )
   => ( ( ( k1_xboole_0 != sK1
          & k1_xboole_0 != sK0 )
        | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f31])).

fof(f31,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f182,plain,
    ( ~ spl12_1
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f80,f179,f170])).

fof(f80,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f177,plain,
    ( ~ spl12_1
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f81,f174,f170])).

fof(f81,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:47:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (18253)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.47  % (18237)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.47  % (18237)Refutation not found, incomplete strategy% (18237)------------------------------
% 0.22/0.47  % (18237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (18237)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (18237)Memory used [KB]: 10618
% 0.22/0.47  % (18237)Time elapsed: 0.052 s
% 0.22/0.47  % (18237)------------------------------
% 0.22/0.47  % (18237)------------------------------
% 0.22/0.52  % (18232)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (18233)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (18238)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (18231)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (18238)Refutation not found, incomplete strategy% (18238)------------------------------
% 0.22/0.52  % (18238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (18238)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (18238)Memory used [KB]: 10618
% 0.22/0.52  % (18238)Time elapsed: 0.116 s
% 0.22/0.52  % (18238)------------------------------
% 0.22/0.52  % (18238)------------------------------
% 0.22/0.53  % (18242)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (18240)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (18251)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (18228)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (18228)Refutation not found, incomplete strategy% (18228)------------------------------
% 0.22/0.54  % (18228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18228)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (18228)Memory used [KB]: 1663
% 0.22/0.54  % (18228)Time elapsed: 0.123 s
% 0.22/0.54  % (18228)------------------------------
% 0.22/0.54  % (18228)------------------------------
% 0.22/0.54  % (18239)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (18230)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (18257)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (18243)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (18230)Refutation not found, incomplete strategy% (18230)------------------------------
% 0.22/0.54  % (18230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18230)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (18230)Memory used [KB]: 10746
% 0.22/0.54  % (18230)Time elapsed: 0.125 s
% 0.22/0.54  % (18230)------------------------------
% 0.22/0.54  % (18230)------------------------------
% 0.22/0.54  % (18234)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (18248)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (18255)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (18254)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (18248)Refutation not found, incomplete strategy% (18248)------------------------------
% 0.22/0.55  % (18248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (18248)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (18248)Memory used [KB]: 10746
% 0.22/0.55  % (18248)Time elapsed: 0.140 s
% 0.22/0.55  % (18248)------------------------------
% 0.22/0.55  % (18248)------------------------------
% 0.22/0.55  % (18235)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (18250)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.45/0.55  % (18256)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.45/0.55  % (18250)Refutation not found, incomplete strategy% (18250)------------------------------
% 1.45/0.55  % (18250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (18250)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (18250)Memory used [KB]: 10746
% 1.45/0.55  % (18250)Time elapsed: 0.117 s
% 1.45/0.55  % (18250)------------------------------
% 1.45/0.55  % (18250)------------------------------
% 1.45/0.55  % (18236)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.45/0.55  % (18247)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.45/0.55  % (18236)Refutation not found, incomplete strategy% (18236)------------------------------
% 1.45/0.55  % (18236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (18236)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (18236)Memory used [KB]: 10746
% 1.45/0.55  % (18236)Time elapsed: 0.133 s
% 1.45/0.55  % (18236)------------------------------
% 1.45/0.55  % (18236)------------------------------
% 1.45/0.55  % (18246)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.45/0.55  % (18252)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.45/0.56  % (18249)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.45/0.56  % (18229)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.45/0.56  % (18249)Refutation not found, incomplete strategy% (18249)------------------------------
% 1.45/0.56  % (18249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (18249)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (18249)Memory used [KB]: 1791
% 1.45/0.56  % (18249)Time elapsed: 0.150 s
% 1.45/0.56  % (18249)------------------------------
% 1.45/0.56  % (18249)------------------------------
% 1.45/0.56  % (18241)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.45/0.56  % (18245)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.45/0.56  % (18245)Refutation not found, incomplete strategy% (18245)------------------------------
% 1.45/0.56  % (18245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (18245)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (18245)Memory used [KB]: 10618
% 1.45/0.56  % (18245)Time elapsed: 0.144 s
% 1.45/0.56  % (18245)------------------------------
% 1.45/0.56  % (18245)------------------------------
% 1.45/0.56  % (18239)Refutation not found, incomplete strategy% (18239)------------------------------
% 1.45/0.56  % (18239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (18239)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (18239)Memory used [KB]: 10618
% 1.45/0.56  % (18239)Time elapsed: 0.150 s
% 1.45/0.56  % (18239)------------------------------
% 1.45/0.56  % (18239)------------------------------
% 1.63/0.57  % (18231)Refutation found. Thanks to Tanya!
% 1.63/0.57  % SZS status Theorem for theBenchmark
% 1.63/0.57  % SZS output start Proof for theBenchmark
% 1.63/0.57  fof(f648,plain,(
% 1.63/0.57    $false),
% 1.63/0.57    inference(avatar_sat_refutation,[],[f177,f182,f183,f355,f391,f611,f633,f647])).
% 1.63/0.57  fof(f647,plain,(
% 1.63/0.57    spl12_3 | ~spl12_10),
% 1.63/0.57    inference(avatar_contradiction_clause,[],[f646])).
% 1.63/0.57  fof(f646,plain,(
% 1.63/0.57    $false | (spl12_3 | ~spl12_10)),
% 1.63/0.57    inference(subsumption_resolution,[],[f639,f181])).
% 1.63/0.57  fof(f181,plain,(
% 1.63/0.57    k1_xboole_0 != sK0 | spl12_3),
% 1.63/0.57    inference(avatar_component_clause,[],[f179])).
% 1.63/0.57  fof(f179,plain,(
% 1.63/0.57    spl12_3 <=> k1_xboole_0 = sK0),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 1.63/0.57  fof(f639,plain,(
% 1.63/0.57    k1_xboole_0 = sK0 | ~spl12_10),
% 1.63/0.57    inference(resolution,[],[f607,f443])).
% 1.63/0.57  fof(f443,plain,(
% 1.63/0.57    ( ! [X4] : (r2_hidden(sK5(X4,k1_xboole_0),X4) | k1_xboole_0 = X4) )),
% 1.63/0.57    inference(resolution,[],[f439,f105])).
% 1.63/0.57  fof(f105,plain,(
% 1.63/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f64])).
% 1.63/0.57  fof(f64,plain,(
% 1.63/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.63/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f62,f63])).
% 1.63/0.57  fof(f63,plain,(
% 1.63/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.63/0.57    introduced(choice_axiom,[])).
% 1.63/0.57  fof(f62,plain,(
% 1.63/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.63/0.57    inference(rectify,[],[f61])).
% 1.63/0.57  fof(f61,plain,(
% 1.63/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.63/0.57    inference(nnf_transformation,[],[f39])).
% 1.63/0.57  fof(f39,plain,(
% 1.63/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.63/0.57    inference(ennf_transformation,[],[f3])).
% 1.63/0.57  fof(f3,axiom,(
% 1.63/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.63/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.63/0.57  fof(f439,plain,(
% 1.63/0.57    ( ! [X12] : (~r1_tarski(X12,k1_xboole_0) | k1_xboole_0 = X12) )),
% 1.63/0.57    inference(condensation,[],[f435])).
% 1.63/0.57  fof(f435,plain,(
% 1.63/0.57    ( ! [X12,X13] : (~r1_tarski(X12,X13) | ~r1_tarski(X12,k1_xboole_0) | k1_xboole_0 = X12) )),
% 1.63/0.57    inference(resolution,[],[f420,f198])).
% 1.63/0.57  fof(f198,plain,(
% 1.63/0.57    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.63/0.57    inference(forward_demodulation,[],[f194,f88])).
% 1.63/0.57  fof(f88,plain,(
% 1.63/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.63/0.57    inference(cnf_transformation,[],[f13])).
% 1.63/0.57  fof(f13,axiom,(
% 1.63/0.57    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.63/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.63/0.57  fof(f194,plain,(
% 1.63/0.57    ( ! [X0] : (r1_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.63/0.57    inference(superposition,[],[f97,f87])).
% 1.63/0.57  fof(f87,plain,(
% 1.63/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f15])).
% 1.63/0.57  fof(f15,axiom,(
% 1.63/0.57    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.63/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.63/0.57  fof(f97,plain,(
% 1.63/0.57    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 1.63/0.57    inference(cnf_transformation,[],[f21])).
% 1.63/0.57  fof(f21,axiom,(
% 1.63/0.57    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 1.63/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).
% 1.63/0.57  fof(f420,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0) | k1_xboole_0 = X2) )),
% 1.63/0.57    inference(resolution,[],[f132,f91])).
% 1.63/0.57  fof(f91,plain,(
% 1.63/0.57    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.63/0.57    inference(cnf_transformation,[],[f35])).
% 1.63/0.57  fof(f35,plain,(
% 1.63/0.57    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.63/0.57    inference(ennf_transformation,[],[f18])).
% 1.63/0.57  fof(f18,axiom,(
% 1.63/0.57    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.63/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.63/0.57  fof(f132,plain,(
% 1.63/0.57    ( ! [X2,X0,X3,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f46])).
% 1.63/0.57  fof(f46,plain,(
% 1.63/0.57    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 1.63/0.57    inference(flattening,[],[f45])).
% 1.63/0.57  fof(f45,plain,(
% 1.63/0.57    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 1.63/0.57    inference(ennf_transformation,[],[f16])).
% 1.63/0.57  fof(f16,axiom,(
% 1.63/0.57    ! [X0,X1,X2,X3] : ((r1_xboole_0(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.63/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).
% 1.63/0.57  fof(f607,plain,(
% 1.63/0.57    ( ! [X6] : (~r2_hidden(X6,sK0)) ) | ~spl12_10),
% 1.63/0.57    inference(avatar_component_clause,[],[f606])).
% 1.63/0.57  fof(f606,plain,(
% 1.63/0.57    spl12_10 <=> ! [X6] : ~r2_hidden(X6,sK0)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).
% 1.63/0.57  fof(f633,plain,(
% 1.63/0.57    spl12_2 | ~spl12_11),
% 1.63/0.57    inference(avatar_contradiction_clause,[],[f632])).
% 1.63/0.57  fof(f632,plain,(
% 1.63/0.57    $false | (spl12_2 | ~spl12_11)),
% 1.63/0.57    inference(subsumption_resolution,[],[f625,f176])).
% 1.63/0.57  fof(f176,plain,(
% 1.63/0.57    k1_xboole_0 != sK1 | spl12_2),
% 1.63/0.57    inference(avatar_component_clause,[],[f174])).
% 1.63/0.57  fof(f174,plain,(
% 1.63/0.57    spl12_2 <=> k1_xboole_0 = sK1),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 1.63/0.57  fof(f625,plain,(
% 1.63/0.57    k1_xboole_0 = sK1 | ~spl12_11),
% 1.63/0.57    inference(resolution,[],[f610,f443])).
% 1.63/0.57  fof(f610,plain,(
% 1.63/0.57    ( ! [X7] : (~r2_hidden(X7,sK1)) ) | ~spl12_11),
% 1.63/0.57    inference(avatar_component_clause,[],[f609])).
% 1.63/0.57  fof(f609,plain,(
% 1.63/0.57    spl12_11 <=> ! [X7] : ~r2_hidden(X7,sK1)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).
% 1.63/0.57  fof(f611,plain,(
% 1.63/0.57    spl12_10 | spl12_11 | ~spl12_1),
% 1.63/0.57    inference(avatar_split_clause,[],[f604,f170,f609,f606])).
% 1.63/0.57  fof(f170,plain,(
% 1.63/0.57    spl12_1 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 1.63/0.57  fof(f604,plain,(
% 1.63/0.57    ( ! [X6,X7] : (~r2_hidden(X7,sK1) | ~r2_hidden(X6,sK0)) ) | ~spl12_1),
% 1.63/0.57    inference(subsumption_resolution,[],[f603,f267])).
% 1.63/0.57  fof(f267,plain,(
% 1.63/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.63/0.57    inference(condensation,[],[f263])).
% 1.63/0.57  fof(f263,plain,(
% 1.63/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 1.63/0.57    inference(resolution,[],[f103,f85])).
% 1.63/0.57  fof(f85,plain,(
% 1.63/0.57    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f17])).
% 1.63/0.57  fof(f17,axiom,(
% 1.63/0.57    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.63/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.63/0.57  fof(f103,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f60])).
% 1.63/0.57  fof(f60,plain,(
% 1.63/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.63/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f59])).
% 1.63/0.57  fof(f59,plain,(
% 1.63/0.57    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.63/0.57    introduced(choice_axiom,[])).
% 1.63/0.57  fof(f38,plain,(
% 1.63/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.63/0.57    inference(ennf_transformation,[],[f33])).
% 1.63/0.57  fof(f33,plain,(
% 1.63/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.63/0.57    inference(rectify,[],[f6])).
% 1.63/0.57  fof(f6,axiom,(
% 1.63/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.63/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.63/0.57  fof(f603,plain,(
% 1.63/0.57    ( ! [X6,X7] : (r2_hidden(k4_tarski(X6,X7),k1_xboole_0) | ~r2_hidden(X7,sK1) | ~r2_hidden(X6,sK0)) ) | ~spl12_1),
% 1.63/0.57    inference(superposition,[],[f161,f171])).
% 1.63/0.57  fof(f171,plain,(
% 1.63/0.57    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl12_1),
% 1.63/0.57    inference(avatar_component_clause,[],[f170])).
% 1.63/0.57  fof(f161,plain,(
% 1.63/0.57    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 1.63/0.57    inference(equality_resolution,[],[f160])).
% 1.63/0.57  fof(f160,plain,(
% 1.63/0.57    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.63/0.57    inference(equality_resolution,[],[f122])).
% 1.63/0.57  fof(f122,plain,(
% 1.63/0.57    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.63/0.57    inference(cnf_transformation,[],[f76])).
% 1.63/0.57  fof(f76,plain,(
% 1.63/0.57    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK7(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((sK7(X0,X1,X2) = k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)) & r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X0)) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8 & r2_hidden(sK11(X0,X1,X8),X1) & r2_hidden(sK10(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.63/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10,sK11])],[f72,f75,f74,f73])).
% 1.63/0.57  fof(f73,plain,(
% 1.63/0.57    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK7(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK7(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 1.63/0.57    introduced(choice_axiom,[])).
% 1.63/0.57  fof(f74,plain,(
% 1.63/0.57    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK7(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK7(X0,X1,X2) = k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)) & r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X0)))),
% 1.63/0.57    introduced(choice_axiom,[])).
% 1.63/0.57  fof(f75,plain,(
% 1.63/0.57    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8 & r2_hidden(sK11(X0,X1,X8),X1) & r2_hidden(sK10(X0,X1,X8),X0)))),
% 1.63/0.57    introduced(choice_axiom,[])).
% 1.63/0.57  fof(f72,plain,(
% 1.63/0.57    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.63/0.57    inference(rectify,[],[f71])).
% 1.63/0.57  fof(f71,plain,(
% 1.63/0.57    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.63/0.57    inference(nnf_transformation,[],[f24])).
% 1.63/0.57  fof(f24,axiom,(
% 1.63/0.57    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.63/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.63/0.57  fof(f391,plain,(
% 1.63/0.57    spl12_1 | ~spl12_3),
% 1.63/0.57    inference(avatar_contradiction_clause,[],[f390])).
% 1.63/0.57  fof(f390,plain,(
% 1.63/0.57    $false | (spl12_1 | ~spl12_3)),
% 1.63/0.57    inference(trivial_inequality_removal,[],[f389])).
% 1.63/0.57  fof(f389,plain,(
% 1.63/0.57    k1_xboole_0 != k1_xboole_0 | (spl12_1 | ~spl12_3)),
% 1.63/0.57    inference(superposition,[],[f356,f374])).
% 1.63/0.57  fof(f374,plain,(
% 1.63/0.57    ( ! [X4] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X4)) )),
% 1.63/0.57    inference(resolution,[],[f368,f95])).
% 1.63/0.57  fof(f95,plain,(
% 1.63/0.57    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.63/0.57    inference(cnf_transformation,[],[f58])).
% 1.63/0.57  fof(f58,plain,(
% 1.63/0.57    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.63/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f57])).
% 1.63/0.57  fof(f57,plain,(
% 1.63/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.63/0.57    introduced(choice_axiom,[])).
% 1.63/0.57  fof(f37,plain,(
% 1.63/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.63/0.57    inference(ennf_transformation,[],[f7])).
% 1.63/0.57  fof(f7,axiom,(
% 1.63/0.57    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.63/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.63/0.57  fof(f368,plain,(
% 1.63/0.57    ( ! [X4,X3] : (~r2_hidden(X3,k2_zfmisc_1(k1_xboole_0,X4))) )),
% 1.63/0.57    inference(resolution,[],[f164,f267])).
% 1.63/0.57  fof(f164,plain,(
% 1.63/0.57    ( ! [X0,X8,X1] : (r2_hidden(sK10(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 1.63/0.57    inference(equality_resolution,[],[f119])).
% 1.63/0.57  fof(f119,plain,(
% 1.63/0.57    ( ! [X2,X0,X8,X1] : (r2_hidden(sK10(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.63/0.57    inference(cnf_transformation,[],[f76])).
% 1.63/0.57  fof(f356,plain,(
% 1.63/0.57    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | (spl12_1 | ~spl12_3)),
% 1.63/0.57    inference(forward_demodulation,[],[f172,f180])).
% 1.63/0.57  fof(f180,plain,(
% 1.63/0.57    k1_xboole_0 = sK0 | ~spl12_3),
% 1.63/0.57    inference(avatar_component_clause,[],[f179])).
% 1.63/0.57  fof(f172,plain,(
% 1.63/0.57    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | spl12_1),
% 1.63/0.57    inference(avatar_component_clause,[],[f170])).
% 1.63/0.57  fof(f355,plain,(
% 1.63/0.57    spl12_1 | ~spl12_2),
% 1.63/0.57    inference(avatar_contradiction_clause,[],[f354])).
% 1.63/0.57  fof(f354,plain,(
% 1.63/0.57    $false | (spl12_1 | ~spl12_2)),
% 1.63/0.57    inference(trivial_inequality_removal,[],[f353])).
% 1.63/0.57  fof(f353,plain,(
% 1.63/0.57    k1_xboole_0 != k1_xboole_0 | (spl12_1 | ~spl12_2)),
% 1.63/0.57    inference(superposition,[],[f184,f342])).
% 1.63/0.57  fof(f342,plain,(
% 1.63/0.57    ( ! [X4] : (k1_xboole_0 = k2_zfmisc_1(X4,k1_xboole_0)) )),
% 1.63/0.57    inference(resolution,[],[f336,f95])).
% 1.63/0.57  fof(f336,plain,(
% 1.63/0.57    ( ! [X4,X3] : (~r2_hidden(X3,k2_zfmisc_1(X4,k1_xboole_0))) )),
% 1.63/0.57    inference(resolution,[],[f163,f267])).
% 1.63/0.57  fof(f163,plain,(
% 1.63/0.57    ( ! [X0,X8,X1] : (r2_hidden(sK11(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 1.63/0.57    inference(equality_resolution,[],[f120])).
% 1.63/0.57  fof(f120,plain,(
% 1.63/0.57    ( ! [X2,X0,X8,X1] : (r2_hidden(sK11(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.63/0.57    inference(cnf_transformation,[],[f76])).
% 1.63/0.57  fof(f184,plain,(
% 1.63/0.57    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | (spl12_1 | ~spl12_2)),
% 1.63/0.58    inference(forward_demodulation,[],[f172,f175])).
% 1.63/0.58  fof(f175,plain,(
% 1.63/0.58    k1_xboole_0 = sK1 | ~spl12_2),
% 1.63/0.58    inference(avatar_component_clause,[],[f174])).
% 1.63/0.58  fof(f183,plain,(
% 1.63/0.58    spl12_1 | spl12_3 | spl12_2),
% 1.63/0.58    inference(avatar_split_clause,[],[f79,f174,f179,f170])).
% 1.63/0.58  fof(f79,plain,(
% 1.63/0.58    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 1.63/0.58    inference(cnf_transformation,[],[f52])).
% 1.63/0.58  fof(f52,plain,(
% 1.63/0.58    ((k1_xboole_0 != sK1 & k1_xboole_0 != sK0) | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)) & (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1))),
% 1.63/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f50,f51])).
% 1.63/0.58  fof(f51,plain,(
% 1.63/0.58    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK1 & k1_xboole_0 != sK0) | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)) & (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)))),
% 1.63/0.58    introduced(choice_axiom,[])).
% 1.63/0.58  fof(f50,plain,(
% 1.63/0.58    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.63/0.58    inference(flattening,[],[f49])).
% 1.63/0.58  fof(f49,plain,(
% 1.63/0.58    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.63/0.58    inference(nnf_transformation,[],[f34])).
% 1.63/0.58  fof(f34,plain,(
% 1.63/0.58    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.63/0.58    inference(ennf_transformation,[],[f32])).
% 1.63/0.58  fof(f32,negated_conjecture,(
% 1.63/0.58    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.63/0.58    inference(negated_conjecture,[],[f31])).
% 1.63/0.58  fof(f31,conjecture,(
% 1.63/0.58    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.63/0.58  fof(f182,plain,(
% 1.63/0.58    ~spl12_1 | ~spl12_3),
% 1.63/0.58    inference(avatar_split_clause,[],[f80,f179,f170])).
% 1.63/0.58  fof(f80,plain,(
% 1.63/0.58    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 1.63/0.58    inference(cnf_transformation,[],[f52])).
% 1.63/0.58  fof(f177,plain,(
% 1.63/0.58    ~spl12_1 | ~spl12_2),
% 1.63/0.58    inference(avatar_split_clause,[],[f81,f174,f170])).
% 1.63/0.58  fof(f81,plain,(
% 1.63/0.58    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 1.63/0.58    inference(cnf_transformation,[],[f52])).
% 1.63/0.58  % SZS output end Proof for theBenchmark
% 1.63/0.58  % (18231)------------------------------
% 1.63/0.58  % (18231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.58  % (18231)Termination reason: Refutation
% 1.63/0.58  
% 1.63/0.58  % (18231)Memory used [KB]: 11001
% 1.63/0.58  % (18231)Time elapsed: 0.145 s
% 1.63/0.58  % (18231)------------------------------
% 1.63/0.58  % (18231)------------------------------
% 1.63/0.58  % (18227)Success in time 0.207 s
%------------------------------------------------------------------------------
