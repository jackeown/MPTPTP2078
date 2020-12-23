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
% DateTime   : Thu Dec  3 12:59:29 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 395 expanded)
%              Number of leaves         :   31 ( 118 expanded)
%              Depth                    :   18
%              Number of atoms          :  545 (1985 expanded)
%              Number of equality atoms :  160 ( 737 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f944,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f527,f694,f698,f718,f820,f870,f882,f899,f910,f929,f943])).

fof(f943,plain,(
    ~ spl13_34 ),
    inference(avatar_contradiction_clause,[],[f942])).

fof(f942,plain,
    ( $false
    | ~ spl13_34 ),
    inference(subsumption_resolution,[],[f936,f65])).

fof(f65,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( sK6 != k7_mcart_1(sK3,sK4,sK5,sK7)
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK6 = X7
                | k3_mcart_1(X5,X6,X7) != sK7
                | ~ m1_subset_1(X7,sK5) )
            | ~ m1_subset_1(X6,sK4) )
        | ~ m1_subset_1(X5,sK3) )
    & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f22,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k7_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X7
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( sK6 != k7_mcart_1(sK3,sK4,sK5,sK7)
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK6 = X7
                  | k3_mcart_1(X5,X6,X7) != sK7
                  | ~ m1_subset_1(X7,sK5) )
              | ~ m1_subset_1(X6,sK4) )
          | ~ m1_subset_1(X5,sK3) )
      & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X7 ) ) ) )
         => ( k7_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X7 ) ) ) )
       => ( k7_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).

fof(f936,plain,
    ( k1_xboole_0 = sK4
    | ~ spl13_34 ),
    inference(resolution,[],[f906,f372])).

fof(f372,plain,(
    ! [X4] :
      ( r2_hidden(sK9(X4,k1_xboole_0),X4)
      | k1_xboole_0 = X4 ) ),
    inference(resolution,[],[f80,f128])).

fof(f128,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f73,f120])).

fof(f120,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f73,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK9(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK9(X0,X1),X1)
          | ~ r2_hidden(sK9(X0,X1),X0) )
        & ( r2_hidden(sK9(X0,X1),X1)
          | r2_hidden(sK9(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK9(X0,X1),X1)
          | ~ r2_hidden(sK9(X0,X1),X0) )
        & ( r2_hidden(sK9(X0,X1),X1)
          | r2_hidden(sK9(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f906,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK4)
    | ~ spl13_34 ),
    inference(avatar_component_clause,[],[f905])).

fof(f905,plain,
    ( spl13_34
  <=> ! [X1] : ~ r2_hidden(X1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_34])])).

fof(f929,plain,(
    ~ spl13_35 ),
    inference(avatar_contradiction_clause,[],[f928])).

fof(f928,plain,
    ( $false
    | ~ spl13_35 ),
    inference(subsumption_resolution,[],[f922,f64])).

fof(f64,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f38])).

fof(f922,plain,
    ( k1_xboole_0 = sK3
    | ~ spl13_35 ),
    inference(resolution,[],[f909,f372])).

fof(f909,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl13_35 ),
    inference(avatar_component_clause,[],[f908])).

fof(f908,plain,
    ( spl13_35
  <=> ! [X0] : ~ r2_hidden(X0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_35])])).

fof(f910,plain,
    ( spl13_34
    | spl13_35
    | ~ spl13_26 ),
    inference(avatar_split_clause,[],[f900,f758,f908,f905])).

fof(f758,plain,
    ( spl13_26
  <=> v1_xboole_0(k2_zfmisc_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_26])])).

fof(f900,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK3)
        | ~ r2_hidden(X1,sK4) )
    | ~ spl13_26 ),
    inference(resolution,[],[f759,f350])).

fof(f350,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X6,X4))
      | ~ r2_hidden(X5,X6)
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f122,f276])).

fof(f276,plain,(
    ! [X12,X13,X11] :
      ( ~ sP0(X11,X12,X13)
      | ~ v1_xboole_0(k2_zfmisc_1(X13,X12)) ) ),
    inference(resolution,[],[f269,f69])).

fof(f69,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK8(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f40,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK8(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f269,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k2_zfmisc_1(X2,X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f90,f123])).

fof(f123,plain,(
    ! [X0,X1] : sP1(X0,X1,k2_zfmisc_1(X0,X1)) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f4,f33,f32])).

fof(f32,plain,(
    ! [X3,X1,X0] :
      ( sP0(X3,X1,X0)
    <=> ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X4,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X3,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f90,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X4,X1,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(sK10(X0,X1,X2),X1,X0)
            | ~ r2_hidden(sK10(X0,X1,X2),X2) )
          & ( sP0(sK10(X0,X1,X2),X1,X0)
            | r2_hidden(sK10(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X4,X1,X0) )
            & ( sP0(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f50,f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X3,X1,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X3,X1,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(sK10(X0,X1,X2),X1,X0)
          | ~ r2_hidden(sK10(X0,X1,X2),X2) )
        & ( sP0(sK10(X0,X1,X2),X1,X0)
          | r2_hidden(sK10(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X4,X1,X0) )
            & ( sP0(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X3,X1,X0) )
            & ( sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f122,plain,(
    ! [X4,X2,X3,X1] :
      ( sP0(k4_tarski(X3,X4),X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X3,X2) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | k4_tarski(X3,X4) != X0
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X3,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3,X4] :
            ( k4_tarski(X3,X4) != X0
            | ~ r2_hidden(X4,X1)
            | ~ r2_hidden(X3,X2) ) )
      & ( ( k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)) = X0
          & r2_hidden(sK12(X0,X1,X2),X1)
          & r2_hidden(sK11(X0,X1,X2),X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f54,f55])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X5,X6] :
          ( k4_tarski(X5,X6) = X0
          & r2_hidden(X6,X1)
          & r2_hidden(X5,X2) )
     => ( k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)) = X0
        & r2_hidden(sK12(X0,X1,X2),X1)
        & r2_hidden(sK11(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3,X4] :
            ( k4_tarski(X3,X4) != X0
            | ~ r2_hidden(X4,X1)
            | ~ r2_hidden(X3,X2) ) )
      & ( ? [X5,X6] :
            ( k4_tarski(X5,X6) = X0
            & r2_hidden(X6,X1)
            & r2_hidden(X5,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X3,X1,X0] :
      ( ( sP0(X3,X1,X0)
        | ! [X4,X5] :
            ( k4_tarski(X4,X5) != X3
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X0) ) )
      & ( ? [X4,X5] :
            ( k4_tarski(X4,X5) = X3
            & r2_hidden(X5,X1)
            & r2_hidden(X4,X0) )
        | ~ sP0(X3,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f759,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK3,sK4))
    | ~ spl13_26 ),
    inference(avatar_component_clause,[],[f758])).

fof(f899,plain,
    ( spl13_26
    | ~ spl13_33 ),
    inference(avatar_split_clause,[],[f888,f868,f758])).

fof(f868,plain,
    ( spl13_33
  <=> ! [X0] : ~ r2_hidden(X0,k2_zfmisc_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_33])])).

fof(f888,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK3,sK4))
    | ~ spl13_33 ),
    inference(resolution,[],[f869,f70])).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f869,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_zfmisc_1(sK3,sK4))
    | ~ spl13_33 ),
    inference(avatar_component_clause,[],[f868])).

fof(f882,plain,(
    ~ spl13_32 ),
    inference(avatar_contradiction_clause,[],[f881])).

fof(f881,plain,
    ( $false
    | ~ spl13_32 ),
    inference(subsumption_resolution,[],[f877,f66])).

fof(f66,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f38])).

fof(f877,plain,
    ( k1_xboole_0 = sK5
    | ~ spl13_32 ),
    inference(resolution,[],[f866,f372])).

fof(f866,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK5)
    | ~ spl13_32 ),
    inference(avatar_component_clause,[],[f865])).

fof(f865,plain,
    ( spl13_32
  <=> ! [X1] : ~ r2_hidden(X1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_32])])).

fof(f870,plain,
    ( spl13_32
    | spl13_33
    | ~ spl13_1 ),
    inference(avatar_split_clause,[],[f857,f138,f868,f865])).

fof(f138,plain,
    ( spl13_1
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f857,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(sK3,sK4))
        | ~ r2_hidden(X1,sK5) )
    | ~ spl13_1 ),
    inference(resolution,[],[f139,f350])).

fof(f139,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | ~ spl13_1 ),
    inference(avatar_component_clause,[],[f138])).

fof(f820,plain,(
    spl13_13 ),
    inference(avatar_split_clause,[],[f819,f520])).

fof(f520,plain,
    ( spl13_13
  <=> sP2(sK7,sK5,sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).

fof(f819,plain,(
    sP2(sK7,sK5,sK4,sK3) ),
    inference(subsumption_resolution,[],[f818,f64])).

fof(f818,plain,
    ( sP2(sK7,sK5,sK4,sK3)
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f817,f65])).

fof(f817,plain,
    ( sP2(sK7,sK5,sK4,sK3)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f800,f66])).

fof(f800,plain,
    ( sP2(sK7,sK5,sK4,sK3)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f113,f112])).

fof(f112,plain,(
    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f62,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f62,plain,(
    m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f38])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | sP2(X3,X2,X1,X0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f102,f86])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X3,X2,X1,X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( sP2(X3,X2,X1,X0)
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f30,f35])).

fof(f35,plain,(
    ! [X3,X2,X1,X0] :
      ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
        & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
        & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
      | ~ sP2(X3,X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f718,plain,
    ( spl13_1
    | ~ spl13_15 ),
    inference(avatar_contradiction_clause,[],[f717])).

fof(f717,plain,
    ( $false
    | spl13_1
    | ~ spl13_15 ),
    inference(subsumption_resolution,[],[f714,f72])).

fof(f72,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f714,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | spl13_1
    | ~ spl13_15 ),
    inference(resolution,[],[f689,f150])).

fof(f150,plain,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | spl13_1 ),
    inference(subsumption_resolution,[],[f148,f140])).

fof(f140,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | spl13_1 ),
    inference(avatar_component_clause,[],[f138])).

fof(f148,plain,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(resolution,[],[f74,f112])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f689,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK7,X0)
        | ~ v1_relat_1(X0) )
    | ~ spl13_15 ),
    inference(avatar_component_clause,[],[f688])).

fof(f688,plain,
    ( spl13_15
  <=> ! [X0] :
        ( ~ r2_hidden(sK7,X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_15])])).

fof(f698,plain,
    ( spl13_1
    | spl13_16 ),
    inference(avatar_contradiction_clause,[],[f697])).

fof(f697,plain,
    ( $false
    | spl13_1
    | spl13_16 ),
    inference(subsumption_resolution,[],[f695,f162])).

fof(f162,plain,
    ( r2_hidden(k2_mcart_1(sK7),sK5)
    | spl13_1 ),
    inference(resolution,[],[f88,f150])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f695,plain,
    ( ~ r2_hidden(k2_mcart_1(sK7),sK5)
    | spl13_16 ),
    inference(resolution,[],[f693,f152])).

fof(f152,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f75,f69])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f693,plain,
    ( ~ m1_subset_1(k2_mcart_1(sK7),sK5)
    | spl13_16 ),
    inference(avatar_component_clause,[],[f691])).

fof(f691,plain,
    ( spl13_16
  <=> m1_subset_1(k2_mcart_1(sK7),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).

fof(f694,plain,
    ( spl13_15
    | spl13_14
    | ~ spl13_16
    | spl13_1 ),
    inference(avatar_split_clause,[],[f686,f138,f691,f524,f688])).

fof(f524,plain,
    ( spl13_14
  <=> sK6 = k2_mcart_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).

fof(f686,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_mcart_1(sK7),sK5)
        | sK6 = k2_mcart_1(sK7)
        | ~ r2_hidden(sK7,X0)
        | ~ v1_relat_1(X0) )
    | spl13_1 ),
    inference(trivial_inequality_removal,[],[f685])).

fof(f685,plain,
    ( ! [X0] :
        ( sK7 != sK7
        | ~ m1_subset_1(k2_mcart_1(sK7),sK5)
        | sK6 = k2_mcart_1(sK7)
        | ~ r2_hidden(sK7,X0)
        | ~ v1_relat_1(X0) )
    | spl13_1 ),
    inference(resolution,[],[f675,f254])).

fof(f254,plain,
    ( sP0(k1_mcart_1(sK7),sK4,sK3)
    | spl13_1 ),
    inference(resolution,[],[f251,f156])).

fof(f156,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK3,sK4))
    | spl13_1 ),
    inference(resolution,[],[f87,f150])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f251,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | sP0(X0,X2,X1) ) ),
    inference(resolution,[],[f89,f123])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP0(X4,X1,X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f675,plain,(
    ! [X0,X1] :
      ( ~ sP0(k1_mcart_1(X0),sK4,sK3)
      | sK7 != X0
      | ~ m1_subset_1(k2_mcart_1(X0),sK5)
      | k2_mcart_1(X0) = sK6
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f674,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f674,plain,(
    ! [X0,X1] :
      ( sK7 != k4_tarski(X1,X0)
      | ~ sP0(X1,sK4,sK3)
      | ~ m1_subset_1(X0,sK5)
      | sK6 = X0 ) ),
    inference(duplicate_literal_removal,[],[f673])).

fof(f673,plain,(
    ! [X0,X1] :
      ( sK6 = X0
      | ~ sP0(X1,sK4,sK3)
      | ~ m1_subset_1(X0,sK5)
      | sK7 != k4_tarski(X1,X0)
      | ~ sP0(X1,sK4,sK3) ) ),
    inference(resolution,[],[f672,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK11(X0,X1,X2),X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f672,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK11(X0,sK4,X2),sK3)
      | sK6 = X1
      | ~ sP0(X0,sK4,X2)
      | ~ m1_subset_1(X1,sK5)
      | k4_tarski(X0,X1) != sK7 ) ),
    inference(duplicate_literal_removal,[],[f671])).

fof(f671,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X0,X1) != sK7
      | sK6 = X1
      | ~ sP0(X0,sK4,X2)
      | ~ m1_subset_1(X1,sK5)
      | ~ r2_hidden(sK11(X0,sK4,X2),sK3)
      | ~ sP0(X0,sK4,X2) ) ),
    inference(resolution,[],[f669,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK12(X0,X1,X2),X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f669,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK12(X1,X2,X3),sK4)
      | sK7 != k4_tarski(X1,X0)
      | sK6 = X0
      | ~ sP0(X1,X2,X3)
      | ~ m1_subset_1(X0,sK5)
      | ~ r2_hidden(sK11(X1,X2,X3),sK3) ) ),
    inference(resolution,[],[f667,f152])).

fof(f667,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK11(X1,X2,X3),sK3)
      | ~ m1_subset_1(X0,sK5)
      | sK7 != k4_tarski(X1,X0)
      | sK6 = X0
      | ~ sP0(X1,X2,X3)
      | ~ r2_hidden(sK12(X1,X2,X3),sK4) ) ),
    inference(resolution,[],[f659,f152])).

fof(f659,plain,(
    ! [X14,X15,X13,X16] :
      ( ~ m1_subset_1(sK12(X13,X14,X15),sK4)
      | sK6 = X16
      | ~ m1_subset_1(X16,sK5)
      | sK7 != k4_tarski(X13,X16)
      | ~ m1_subset_1(sK11(X13,X14,X15),sK3)
      | ~ sP0(X13,X14,X15) ) ),
    inference(superposition,[],[f111,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)) = X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f111,plain,(
    ! [X6,X7,X5] :
      ( sK7 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK6 = X7
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4)
      | ~ m1_subset_1(X5,sK3) ) ),
    inference(definition_unfolding,[],[f63,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f63,plain,(
    ! [X6,X7,X5] :
      ( sK6 = X7
      | k3_mcart_1(X5,X6,X7) != sK7
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4)
      | ~ m1_subset_1(X5,sK3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f527,plain,
    ( ~ spl13_13
    | ~ spl13_14 ),
    inference(avatar_split_clause,[],[f518,f524,f520])).

fof(f518,plain,
    ( sK6 != k2_mcart_1(sK7)
    | ~ sP2(sK7,sK5,sK4,sK3) ),
    inference(superposition,[],[f67,f101])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0)
        & k6_mcart_1(X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(X0))
        & k5_mcart_1(X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(X0)) )
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X3,X2,X1,X0] :
      ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
        & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
        & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
      | ~ sP2(X3,X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f67,plain,(
    sK6 != k7_mcart_1(sK3,sK4,sK5,sK7) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:27:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (4855)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (4846)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (4840)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.29/0.54  % (4865)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.29/0.54  % (4843)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.29/0.55  % (4841)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.55  % (4848)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.29/0.55  % (4842)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.29/0.55  % (4869)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.29/0.55  % (4850)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.29/0.55  % (4839)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.29/0.55  % (4864)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.29/0.55  % (4851)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.44/0.55  % (4868)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.44/0.56  % (4863)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.44/0.56  % (4857)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.44/0.56  % (4844)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.44/0.56  % (4867)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.44/0.56  % (4860)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.44/0.56  % (4854)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.44/0.56  % (4862)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.44/0.56  % (4849)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.44/0.57  % (4859)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.44/0.57  % (4852)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.44/0.57  % (4853)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.44/0.57  % (4858)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.44/0.57  % (4841)Refutation not found, incomplete strategy% (4841)------------------------------
% 1.44/0.57  % (4841)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.57  % (4841)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.57  
% 1.44/0.57  % (4841)Memory used [KB]: 10746
% 1.44/0.57  % (4841)Time elapsed: 0.153 s
% 1.44/0.57  % (4841)------------------------------
% 1.44/0.57  % (4841)------------------------------
% 1.44/0.57  % (4845)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.44/0.58  % (4856)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.44/0.58  % (4861)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.44/0.58  % (4866)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.44/0.59  % (4862)Refutation not found, incomplete strategy% (4862)------------------------------
% 1.44/0.59  % (4862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.59  % (4862)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.59  
% 1.44/0.59  % (4862)Memory used [KB]: 11129
% 1.44/0.59  % (4862)Time elapsed: 0.121 s
% 1.44/0.59  % (4862)------------------------------
% 1.44/0.59  % (4862)------------------------------
% 1.44/0.61  % (4861)Refutation not found, incomplete strategy% (4861)------------------------------
% 1.44/0.61  % (4861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.61  % (4861)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.61  
% 1.44/0.61  % (4861)Memory used [KB]: 1791
% 1.44/0.61  % (4861)Time elapsed: 0.193 s
% 1.44/0.61  % (4861)------------------------------
% 1.44/0.61  % (4861)------------------------------
% 1.44/0.62  % (4867)Refutation found. Thanks to Tanya!
% 1.44/0.62  % SZS status Theorem for theBenchmark
% 1.44/0.62  % SZS output start Proof for theBenchmark
% 1.44/0.62  fof(f944,plain,(
% 1.44/0.62    $false),
% 1.44/0.62    inference(avatar_sat_refutation,[],[f527,f694,f698,f718,f820,f870,f882,f899,f910,f929,f943])).
% 1.44/0.62  fof(f943,plain,(
% 1.44/0.62    ~spl13_34),
% 1.44/0.62    inference(avatar_contradiction_clause,[],[f942])).
% 1.44/0.62  fof(f942,plain,(
% 1.44/0.62    $false | ~spl13_34),
% 1.44/0.62    inference(subsumption_resolution,[],[f936,f65])).
% 1.44/0.62  fof(f65,plain,(
% 1.44/0.62    k1_xboole_0 != sK4),
% 1.44/0.62    inference(cnf_transformation,[],[f38])).
% 1.44/0.62  fof(f38,plain,(
% 1.44/0.62    sK6 != k7_mcart_1(sK3,sK4,sK5,sK7) & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & ! [X5] : (! [X6] : (! [X7] : (sK6 = X7 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) | ~m1_subset_1(X5,sK3)) & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))),
% 1.44/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f22,f37])).
% 1.44/0.62  fof(f37,plain,(
% 1.44/0.62    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK6 != k7_mcart_1(sK3,sK4,sK5,sK7) & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & ! [X5] : (! [X6] : (! [X7] : (sK6 = X7 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) | ~m1_subset_1(X5,sK3)) & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)))),
% 1.44/0.62    introduced(choice_axiom,[])).
% 1.44/0.62  fof(f22,plain,(
% 1.44/0.62    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.44/0.62    inference(flattening,[],[f21])).
% 1.44/0.62  fof(f21,plain,(
% 1.44/0.62    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.44/0.62    inference(ennf_transformation,[],[f20])).
% 1.44/0.62  fof(f20,negated_conjecture,(
% 1.44/0.62    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.44/0.62    inference(negated_conjecture,[],[f19])).
% 1.44/0.62  fof(f19,conjecture,(
% 1.44/0.62    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.44/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).
% 1.44/0.62  fof(f936,plain,(
% 1.44/0.62    k1_xboole_0 = sK4 | ~spl13_34),
% 1.44/0.62    inference(resolution,[],[f906,f372])).
% 1.44/0.62  fof(f372,plain,(
% 1.44/0.62    ( ! [X4] : (r2_hidden(sK9(X4,k1_xboole_0),X4) | k1_xboole_0 = X4) )),
% 1.44/0.62    inference(resolution,[],[f80,f128])).
% 1.44/0.62  fof(f128,plain,(
% 1.44/0.62    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.44/0.62    inference(superposition,[],[f73,f120])).
% 1.44/0.62  fof(f120,plain,(
% 1.44/0.62    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.44/0.62    inference(equality_resolution,[],[f84])).
% 1.44/0.62  fof(f84,plain,(
% 1.44/0.62    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.44/0.62    inference(cnf_transformation,[],[f48])).
% 1.44/0.62  fof(f48,plain,(
% 1.44/0.62    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.44/0.62    inference(flattening,[],[f47])).
% 1.44/0.62  fof(f47,plain,(
% 1.44/0.62    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.44/0.62    inference(nnf_transformation,[],[f6])).
% 1.44/0.62  fof(f6,axiom,(
% 1.44/0.62    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.44/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.44/0.62  fof(f73,plain,(
% 1.44/0.62    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.44/0.62    inference(cnf_transformation,[],[f7])).
% 1.44/0.62  fof(f7,axiom,(
% 1.44/0.62    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.44/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 1.44/0.62  fof(f80,plain,(
% 1.44/0.62    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X1) | X0 = X1 | r2_hidden(sK9(X0,X1),X0)) )),
% 1.44/0.62    inference(cnf_transformation,[],[f46])).
% 1.44/0.62  fof(f46,plain,(
% 1.44/0.62    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK9(X0,X1),X1) | ~r2_hidden(sK9(X0,X1),X0)) & (r2_hidden(sK9(X0,X1),X1) | r2_hidden(sK9(X0,X1),X0))))),
% 1.44/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f44,f45])).
% 1.44/0.62  fof(f45,plain,(
% 1.44/0.62    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK9(X0,X1),X1) | ~r2_hidden(sK9(X0,X1),X0)) & (r2_hidden(sK9(X0,X1),X1) | r2_hidden(sK9(X0,X1),X0))))),
% 1.44/0.62    introduced(choice_axiom,[])).
% 1.44/0.62  fof(f44,plain,(
% 1.44/0.62    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 1.44/0.62    inference(nnf_transformation,[],[f28])).
% 1.44/0.62  fof(f28,plain,(
% 1.44/0.62    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.44/0.62    inference(ennf_transformation,[],[f3])).
% 1.44/0.62  fof(f3,axiom,(
% 1.44/0.62    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.44/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 1.44/0.62  fof(f906,plain,(
% 1.44/0.62    ( ! [X1] : (~r2_hidden(X1,sK4)) ) | ~spl13_34),
% 1.44/0.62    inference(avatar_component_clause,[],[f905])).
% 1.44/0.62  fof(f905,plain,(
% 1.44/0.62    spl13_34 <=> ! [X1] : ~r2_hidden(X1,sK4)),
% 1.44/0.62    introduced(avatar_definition,[new_symbols(naming,[spl13_34])])).
% 1.44/0.62  fof(f929,plain,(
% 1.44/0.62    ~spl13_35),
% 1.44/0.62    inference(avatar_contradiction_clause,[],[f928])).
% 1.44/0.62  fof(f928,plain,(
% 1.44/0.62    $false | ~spl13_35),
% 1.44/0.62    inference(subsumption_resolution,[],[f922,f64])).
% 1.44/0.62  fof(f64,plain,(
% 1.44/0.62    k1_xboole_0 != sK3),
% 1.44/0.62    inference(cnf_transformation,[],[f38])).
% 1.44/0.62  fof(f922,plain,(
% 1.44/0.62    k1_xboole_0 = sK3 | ~spl13_35),
% 1.44/0.62    inference(resolution,[],[f909,f372])).
% 1.44/0.62  fof(f909,plain,(
% 1.44/0.62    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | ~spl13_35),
% 1.44/0.62    inference(avatar_component_clause,[],[f908])).
% 1.44/0.62  fof(f908,plain,(
% 1.44/0.62    spl13_35 <=> ! [X0] : ~r2_hidden(X0,sK3)),
% 1.44/0.62    introduced(avatar_definition,[new_symbols(naming,[spl13_35])])).
% 1.44/0.62  fof(f910,plain,(
% 1.44/0.62    spl13_34 | spl13_35 | ~spl13_26),
% 1.44/0.62    inference(avatar_split_clause,[],[f900,f758,f908,f905])).
% 1.44/0.62  fof(f758,plain,(
% 1.44/0.62    spl13_26 <=> v1_xboole_0(k2_zfmisc_1(sK3,sK4))),
% 1.44/0.62    introduced(avatar_definition,[new_symbols(naming,[spl13_26])])).
% 1.44/0.62  fof(f900,plain,(
% 1.44/0.62    ( ! [X0,X1] : (~r2_hidden(X0,sK3) | ~r2_hidden(X1,sK4)) ) | ~spl13_26),
% 1.44/0.62    inference(resolution,[],[f759,f350])).
% 1.44/0.62  fof(f350,plain,(
% 1.44/0.62    ( ! [X6,X4,X5,X3] : (~v1_xboole_0(k2_zfmisc_1(X6,X4)) | ~r2_hidden(X5,X6) | ~r2_hidden(X3,X4)) )),
% 1.44/0.62    inference(resolution,[],[f122,f276])).
% 1.44/0.62  fof(f276,plain,(
% 1.44/0.62    ( ! [X12,X13,X11] : (~sP0(X11,X12,X13) | ~v1_xboole_0(k2_zfmisc_1(X13,X12))) )),
% 1.44/0.62    inference(resolution,[],[f269,f69])).
% 1.44/0.62  fof(f69,plain,(
% 1.44/0.62    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.44/0.62    inference(cnf_transformation,[],[f42])).
% 1.44/0.62  fof(f42,plain,(
% 1.44/0.62    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK8(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.44/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f40,f41])).
% 1.44/0.62  fof(f41,plain,(
% 1.44/0.62    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK8(X0),X0))),
% 1.44/0.62    introduced(choice_axiom,[])).
% 1.44/0.62  fof(f40,plain,(
% 1.44/0.62    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.44/0.62    inference(rectify,[],[f39])).
% 1.44/0.62  fof(f39,plain,(
% 1.44/0.62    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.44/0.62    inference(nnf_transformation,[],[f1])).
% 1.44/0.62  fof(f1,axiom,(
% 1.44/0.62    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.44/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.44/0.62  fof(f269,plain,(
% 1.44/0.62    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_zfmisc_1(X2,X1)) | ~sP0(X0,X1,X2)) )),
% 1.44/0.62    inference(resolution,[],[f90,f123])).
% 1.44/0.62  fof(f123,plain,(
% 1.44/0.62    ( ! [X0,X1] : (sP1(X0,X1,k2_zfmisc_1(X0,X1))) )),
% 1.44/0.62    inference(equality_resolution,[],[f97])).
% 1.44/0.62  fof(f97,plain,(
% 1.44/0.62    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.44/0.62    inference(cnf_transformation,[],[f57])).
% 1.44/0.62  fof(f57,plain,(
% 1.44/0.62    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k2_zfmisc_1(X0,X1) != X2))),
% 1.44/0.62    inference(nnf_transformation,[],[f34])).
% 1.44/0.62  fof(f34,plain,(
% 1.44/0.62    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 1.44/0.62    inference(definition_folding,[],[f4,f33,f32])).
% 1.44/0.62  fof(f32,plain,(
% 1.44/0.62    ! [X3,X1,X0] : (sP0(X3,X1,X0) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)))),
% 1.44/0.62    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.44/0.62  fof(f33,plain,(
% 1.44/0.62    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X3,X1,X0)))),
% 1.44/0.62    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.44/0.62  fof(f4,axiom,(
% 1.44/0.62    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.44/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.44/0.62  fof(f90,plain,(
% 1.44/0.62    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X4,X1,X0) | r2_hidden(X4,X2)) )),
% 1.44/0.62    inference(cnf_transformation,[],[f52])).
% 1.44/0.62  fof(f52,plain,(
% 1.44/0.62    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(sK10(X0,X1,X2),X1,X0) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (sP0(sK10(X0,X1,X2),X1,X0) | r2_hidden(sK10(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X4,X1,X0)) & (sP0(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.44/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f50,f51])).
% 1.44/0.62  fof(f51,plain,(
% 1.44/0.62    ! [X2,X1,X0] : (? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2))) => ((~sP0(sK10(X0,X1,X2),X1,X0) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (sP0(sK10(X0,X1,X2),X1,X0) | r2_hidden(sK10(X0,X1,X2),X2))))),
% 1.44/0.62    introduced(choice_axiom,[])).
% 1.44/0.63  fof(f50,plain,(
% 1.44/0.63    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X4,X1,X0)) & (sP0(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.44/0.63    inference(rectify,[],[f49])).
% 1.44/0.63  fof(f49,plain,(
% 1.44/0.63    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X3,X1,X0)) & (sP0(X3,X1,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 1.44/0.63    inference(nnf_transformation,[],[f33])).
% 1.44/0.63  fof(f122,plain,(
% 1.44/0.63    ( ! [X4,X2,X3,X1] : (sP0(k4_tarski(X3,X4),X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2)) )),
% 1.44/0.63    inference(equality_resolution,[],[f96])).
% 1.44/0.63  fof(f96,plain,(
% 1.44/0.63    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2) | k4_tarski(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f56])).
% 1.44/0.63  fof(f56,plain,(
% 1.44/0.63    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3,X4] : (k4_tarski(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2))) & ((k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)) = X0 & r2_hidden(sK12(X0,X1,X2),X1) & r2_hidden(sK11(X0,X1,X2),X2)) | ~sP0(X0,X1,X2)))),
% 1.44/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f54,f55])).
% 1.44/0.63  fof(f55,plain,(
% 1.44/0.63    ! [X2,X1,X0] : (? [X5,X6] : (k4_tarski(X5,X6) = X0 & r2_hidden(X6,X1) & r2_hidden(X5,X2)) => (k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)) = X0 & r2_hidden(sK12(X0,X1,X2),X1) & r2_hidden(sK11(X0,X1,X2),X2)))),
% 1.44/0.63    introduced(choice_axiom,[])).
% 1.44/0.63  fof(f54,plain,(
% 1.44/0.63    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3,X4] : (k4_tarski(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2))) & (? [X5,X6] : (k4_tarski(X5,X6) = X0 & r2_hidden(X6,X1) & r2_hidden(X5,X2)) | ~sP0(X0,X1,X2)))),
% 1.44/0.63    inference(rectify,[],[f53])).
% 1.44/0.63  fof(f53,plain,(
% 1.44/0.63    ! [X3,X1,X0] : ((sP0(X3,X1,X0) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~sP0(X3,X1,X0)))),
% 1.44/0.63    inference(nnf_transformation,[],[f32])).
% 1.44/0.63  fof(f759,plain,(
% 1.44/0.63    v1_xboole_0(k2_zfmisc_1(sK3,sK4)) | ~spl13_26),
% 1.44/0.63    inference(avatar_component_clause,[],[f758])).
% 1.44/0.63  fof(f899,plain,(
% 1.44/0.63    spl13_26 | ~spl13_33),
% 1.44/0.63    inference(avatar_split_clause,[],[f888,f868,f758])).
% 1.44/0.63  fof(f868,plain,(
% 1.44/0.63    spl13_33 <=> ! [X0] : ~r2_hidden(X0,k2_zfmisc_1(sK3,sK4))),
% 1.44/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_33])])).
% 1.44/0.63  fof(f888,plain,(
% 1.44/0.63    v1_xboole_0(k2_zfmisc_1(sK3,sK4)) | ~spl13_33),
% 1.44/0.63    inference(resolution,[],[f869,f70])).
% 1.44/0.63  fof(f70,plain,(
% 1.44/0.63    ( ! [X0] : (r2_hidden(sK8(X0),X0) | v1_xboole_0(X0)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f42])).
% 1.44/0.63  fof(f869,plain,(
% 1.44/0.63    ( ! [X0] : (~r2_hidden(X0,k2_zfmisc_1(sK3,sK4))) ) | ~spl13_33),
% 1.44/0.63    inference(avatar_component_clause,[],[f868])).
% 1.44/0.63  fof(f882,plain,(
% 1.44/0.63    ~spl13_32),
% 1.44/0.63    inference(avatar_contradiction_clause,[],[f881])).
% 1.44/0.63  fof(f881,plain,(
% 1.44/0.63    $false | ~spl13_32),
% 1.44/0.63    inference(subsumption_resolution,[],[f877,f66])).
% 1.44/0.63  fof(f66,plain,(
% 1.44/0.63    k1_xboole_0 != sK5),
% 1.44/0.63    inference(cnf_transformation,[],[f38])).
% 1.44/0.63  fof(f877,plain,(
% 1.44/0.63    k1_xboole_0 = sK5 | ~spl13_32),
% 1.44/0.63    inference(resolution,[],[f866,f372])).
% 1.44/0.63  fof(f866,plain,(
% 1.44/0.63    ( ! [X1] : (~r2_hidden(X1,sK5)) ) | ~spl13_32),
% 1.44/0.63    inference(avatar_component_clause,[],[f865])).
% 1.44/0.63  fof(f865,plain,(
% 1.44/0.63    spl13_32 <=> ! [X1] : ~r2_hidden(X1,sK5)),
% 1.44/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_32])])).
% 1.44/0.63  fof(f870,plain,(
% 1.44/0.63    spl13_32 | spl13_33 | ~spl13_1),
% 1.44/0.63    inference(avatar_split_clause,[],[f857,f138,f868,f865])).
% 1.44/0.63  fof(f138,plain,(
% 1.44/0.63    spl13_1 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 1.44/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 1.44/0.63  fof(f857,plain,(
% 1.44/0.63    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(sK3,sK4)) | ~r2_hidden(X1,sK5)) ) | ~spl13_1),
% 1.44/0.63    inference(resolution,[],[f139,f350])).
% 1.44/0.63  fof(f139,plain,(
% 1.44/0.63    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | ~spl13_1),
% 1.44/0.63    inference(avatar_component_clause,[],[f138])).
% 1.44/0.63  fof(f820,plain,(
% 1.44/0.63    spl13_13),
% 1.44/0.63    inference(avatar_split_clause,[],[f819,f520])).
% 1.44/0.63  fof(f520,plain,(
% 1.44/0.63    spl13_13 <=> sP2(sK7,sK5,sK4,sK3)),
% 1.44/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).
% 1.44/0.63  fof(f819,plain,(
% 1.44/0.63    sP2(sK7,sK5,sK4,sK3)),
% 1.44/0.63    inference(subsumption_resolution,[],[f818,f64])).
% 1.44/0.63  fof(f818,plain,(
% 1.44/0.63    sP2(sK7,sK5,sK4,sK3) | k1_xboole_0 = sK3),
% 1.44/0.63    inference(subsumption_resolution,[],[f817,f65])).
% 1.44/0.63  fof(f817,plain,(
% 1.44/0.63    sP2(sK7,sK5,sK4,sK3) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3),
% 1.44/0.63    inference(subsumption_resolution,[],[f800,f66])).
% 1.44/0.63  fof(f800,plain,(
% 1.44/0.63    sP2(sK7,sK5,sK4,sK3) | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | k1_xboole_0 = sK3),
% 1.44/0.63    inference(resolution,[],[f113,f112])).
% 1.44/0.63  fof(f112,plain,(
% 1.44/0.63    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 1.44/0.63    inference(definition_unfolding,[],[f62,f86])).
% 1.44/0.63  fof(f86,plain,(
% 1.44/0.63    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f12])).
% 1.44/0.63  fof(f12,axiom,(
% 1.44/0.63    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.44/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.44/0.63  fof(f62,plain,(
% 1.44/0.63    m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))),
% 1.44/0.63    inference(cnf_transformation,[],[f38])).
% 1.44/0.63  fof(f113,plain,(
% 1.44/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | sP2(X3,X2,X1,X0) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.44/0.63    inference(definition_unfolding,[],[f102,f86])).
% 1.44/0.63  fof(f102,plain,(
% 1.44/0.63    ( ! [X2,X0,X3,X1] : (sP2(X3,X2,X1,X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.44/0.63    inference(cnf_transformation,[],[f36])).
% 1.44/0.63  fof(f36,plain,(
% 1.44/0.63    ! [X0,X1,X2] : (! [X3] : (sP2(X3,X2,X1,X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.44/0.63    inference(definition_folding,[],[f30,f35])).
% 1.44/0.63  fof(f35,plain,(
% 1.44/0.63    ! [X3,X2,X1,X0] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~sP2(X3,X2,X1,X0))),
% 1.44/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.44/0.63  fof(f30,plain,(
% 1.44/0.63    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.44/0.63    inference(ennf_transformation,[],[f17])).
% 1.44/0.63  fof(f17,axiom,(
% 1.44/0.63    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.44/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 1.44/0.63  fof(f718,plain,(
% 1.44/0.63    spl13_1 | ~spl13_15),
% 1.44/0.63    inference(avatar_contradiction_clause,[],[f717])).
% 1.44/0.63  fof(f717,plain,(
% 1.44/0.63    $false | (spl13_1 | ~spl13_15)),
% 1.44/0.63    inference(subsumption_resolution,[],[f714,f72])).
% 1.44/0.63  fof(f72,plain,(
% 1.44/0.63    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.44/0.63    inference(cnf_transformation,[],[f10])).
% 1.44/0.63  fof(f10,axiom,(
% 1.44/0.63    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.44/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.44/0.63  fof(f714,plain,(
% 1.44/0.63    ~v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | (spl13_1 | ~spl13_15)),
% 1.44/0.63    inference(resolution,[],[f689,f150])).
% 1.44/0.63  fof(f150,plain,(
% 1.44/0.63    r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | spl13_1),
% 1.44/0.63    inference(subsumption_resolution,[],[f148,f140])).
% 1.44/0.63  fof(f140,plain,(
% 1.44/0.63    ~v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | spl13_1),
% 1.44/0.63    inference(avatar_component_clause,[],[f138])).
% 1.44/0.63  fof(f148,plain,(
% 1.44/0.63    r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 1.44/0.63    inference(resolution,[],[f74,f112])).
% 1.44/0.63  fof(f74,plain,(
% 1.44/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f43])).
% 1.44/0.63  fof(f43,plain,(
% 1.44/0.63    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.44/0.63    inference(nnf_transformation,[],[f23])).
% 1.44/0.63  fof(f23,plain,(
% 1.44/0.63    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.44/0.63    inference(ennf_transformation,[],[f8])).
% 1.44/0.63  fof(f8,axiom,(
% 1.44/0.63    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.44/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.44/0.63  fof(f689,plain,(
% 1.44/0.63    ( ! [X0] : (~r2_hidden(sK7,X0) | ~v1_relat_1(X0)) ) | ~spl13_15),
% 1.44/0.63    inference(avatar_component_clause,[],[f688])).
% 1.44/0.63  fof(f688,plain,(
% 1.44/0.63    spl13_15 <=> ! [X0] : (~r2_hidden(sK7,X0) | ~v1_relat_1(X0))),
% 1.44/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_15])])).
% 1.44/0.63  fof(f698,plain,(
% 1.44/0.63    spl13_1 | spl13_16),
% 1.44/0.63    inference(avatar_contradiction_clause,[],[f697])).
% 1.44/0.63  fof(f697,plain,(
% 1.44/0.63    $false | (spl13_1 | spl13_16)),
% 1.44/0.63    inference(subsumption_resolution,[],[f695,f162])).
% 1.44/0.63  fof(f162,plain,(
% 1.44/0.63    r2_hidden(k2_mcart_1(sK7),sK5) | spl13_1),
% 1.44/0.63    inference(resolution,[],[f88,f150])).
% 1.44/0.63  fof(f88,plain,(
% 1.44/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f29])).
% 1.44/0.63  fof(f29,plain,(
% 1.44/0.63    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.44/0.63    inference(ennf_transformation,[],[f15])).
% 1.44/0.63  fof(f15,axiom,(
% 1.44/0.63    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.44/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.44/0.63  fof(f695,plain,(
% 1.44/0.63    ~r2_hidden(k2_mcart_1(sK7),sK5) | spl13_16),
% 1.44/0.63    inference(resolution,[],[f693,f152])).
% 1.44/0.63  fof(f152,plain,(
% 1.44/0.63    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) )),
% 1.44/0.63    inference(subsumption_resolution,[],[f75,f69])).
% 1.44/0.63  fof(f75,plain,(
% 1.44/0.63    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f43])).
% 1.44/0.63  fof(f693,plain,(
% 1.44/0.63    ~m1_subset_1(k2_mcart_1(sK7),sK5) | spl13_16),
% 1.44/0.63    inference(avatar_component_clause,[],[f691])).
% 1.44/0.63  fof(f691,plain,(
% 1.44/0.63    spl13_16 <=> m1_subset_1(k2_mcart_1(sK7),sK5)),
% 1.44/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).
% 1.44/0.63  fof(f694,plain,(
% 1.44/0.63    spl13_15 | spl13_14 | ~spl13_16 | spl13_1),
% 1.44/0.63    inference(avatar_split_clause,[],[f686,f138,f691,f524,f688])).
% 1.44/0.63  fof(f524,plain,(
% 1.44/0.63    spl13_14 <=> sK6 = k2_mcart_1(sK7)),
% 1.44/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).
% 1.44/0.63  fof(f686,plain,(
% 1.44/0.63    ( ! [X0] : (~m1_subset_1(k2_mcart_1(sK7),sK5) | sK6 = k2_mcart_1(sK7) | ~r2_hidden(sK7,X0) | ~v1_relat_1(X0)) ) | spl13_1),
% 1.44/0.63    inference(trivial_inequality_removal,[],[f685])).
% 1.44/0.63  fof(f685,plain,(
% 1.44/0.63    ( ! [X0] : (sK7 != sK7 | ~m1_subset_1(k2_mcart_1(sK7),sK5) | sK6 = k2_mcart_1(sK7) | ~r2_hidden(sK7,X0) | ~v1_relat_1(X0)) ) | spl13_1),
% 1.44/0.63    inference(resolution,[],[f675,f254])).
% 1.44/0.63  fof(f254,plain,(
% 1.44/0.63    sP0(k1_mcart_1(sK7),sK4,sK3) | spl13_1),
% 1.44/0.63    inference(resolution,[],[f251,f156])).
% 1.44/0.63  fof(f156,plain,(
% 1.44/0.63    r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK3,sK4)) | spl13_1),
% 1.44/0.63    inference(resolution,[],[f87,f150])).
% 1.44/0.63  fof(f87,plain,(
% 1.44/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f29])).
% 1.44/0.63  fof(f251,plain,(
% 1.44/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | sP0(X0,X2,X1)) )),
% 1.44/0.63    inference(resolution,[],[f89,f123])).
% 1.44/0.63  fof(f89,plain,(
% 1.44/0.63    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | sP0(X4,X1,X0)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f52])).
% 1.44/0.63  fof(f675,plain,(
% 1.44/0.63    ( ! [X0,X1] : (~sP0(k1_mcart_1(X0),sK4,sK3) | sK7 != X0 | ~m1_subset_1(k2_mcart_1(X0),sK5) | k2_mcart_1(X0) = sK6 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 1.44/0.63    inference(superposition,[],[f674,f78])).
% 1.44/0.63  fof(f78,plain,(
% 1.44/0.63    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f25])).
% 1.44/0.63  fof(f25,plain,(
% 1.44/0.63    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 1.44/0.63    inference(flattening,[],[f24])).
% 1.44/0.63  fof(f24,plain,(
% 1.44/0.63    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 1.44/0.63    inference(ennf_transformation,[],[f16])).
% 1.44/0.63  fof(f16,axiom,(
% 1.44/0.63    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 1.44/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).
% 1.44/0.63  fof(f674,plain,(
% 1.44/0.63    ( ! [X0,X1] : (sK7 != k4_tarski(X1,X0) | ~sP0(X1,sK4,sK3) | ~m1_subset_1(X0,sK5) | sK6 = X0) )),
% 1.44/0.63    inference(duplicate_literal_removal,[],[f673])).
% 1.44/0.63  fof(f673,plain,(
% 1.44/0.63    ( ! [X0,X1] : (sK6 = X0 | ~sP0(X1,sK4,sK3) | ~m1_subset_1(X0,sK5) | sK7 != k4_tarski(X1,X0) | ~sP0(X1,sK4,sK3)) )),
% 1.44/0.63    inference(resolution,[],[f672,f93])).
% 1.44/0.63  fof(f93,plain,(
% 1.44/0.63    ( ! [X2,X0,X1] : (r2_hidden(sK11(X0,X1,X2),X2) | ~sP0(X0,X1,X2)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f56])).
% 1.44/0.63  fof(f672,plain,(
% 1.44/0.63    ( ! [X2,X0,X1] : (~r2_hidden(sK11(X0,sK4,X2),sK3) | sK6 = X1 | ~sP0(X0,sK4,X2) | ~m1_subset_1(X1,sK5) | k4_tarski(X0,X1) != sK7) )),
% 1.44/0.63    inference(duplicate_literal_removal,[],[f671])).
% 1.44/0.63  fof(f671,plain,(
% 1.44/0.63    ( ! [X2,X0,X1] : (k4_tarski(X0,X1) != sK7 | sK6 = X1 | ~sP0(X0,sK4,X2) | ~m1_subset_1(X1,sK5) | ~r2_hidden(sK11(X0,sK4,X2),sK3) | ~sP0(X0,sK4,X2)) )),
% 1.44/0.63    inference(resolution,[],[f669,f94])).
% 1.44/0.63  fof(f94,plain,(
% 1.44/0.63    ( ! [X2,X0,X1] : (r2_hidden(sK12(X0,X1,X2),X1) | ~sP0(X0,X1,X2)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f56])).
% 1.44/0.63  fof(f669,plain,(
% 1.44/0.63    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK12(X1,X2,X3),sK4) | sK7 != k4_tarski(X1,X0) | sK6 = X0 | ~sP0(X1,X2,X3) | ~m1_subset_1(X0,sK5) | ~r2_hidden(sK11(X1,X2,X3),sK3)) )),
% 1.44/0.63    inference(resolution,[],[f667,f152])).
% 1.44/0.63  fof(f667,plain,(
% 1.44/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK11(X1,X2,X3),sK3) | ~m1_subset_1(X0,sK5) | sK7 != k4_tarski(X1,X0) | sK6 = X0 | ~sP0(X1,X2,X3) | ~r2_hidden(sK12(X1,X2,X3),sK4)) )),
% 1.44/0.63    inference(resolution,[],[f659,f152])).
% 1.44/0.63  fof(f659,plain,(
% 1.44/0.63    ( ! [X14,X15,X13,X16] : (~m1_subset_1(sK12(X13,X14,X15),sK4) | sK6 = X16 | ~m1_subset_1(X16,sK5) | sK7 != k4_tarski(X13,X16) | ~m1_subset_1(sK11(X13,X14,X15),sK3) | ~sP0(X13,X14,X15)) )),
% 1.44/0.63    inference(superposition,[],[f111,f95])).
% 1.44/0.63  fof(f95,plain,(
% 1.44/0.63    ( ! [X2,X0,X1] : (k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)) = X0 | ~sP0(X0,X1,X2)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f56])).
% 1.44/0.63  fof(f111,plain,(
% 1.44/0.63    ( ! [X6,X7,X5] : (sK7 != k4_tarski(k4_tarski(X5,X6),X7) | sK6 = X7 | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4) | ~m1_subset_1(X5,sK3)) )),
% 1.44/0.63    inference(definition_unfolding,[],[f63,f85])).
% 1.44/0.63  fof(f85,plain,(
% 1.44/0.63    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f11])).
% 1.44/0.63  fof(f11,axiom,(
% 1.44/0.63    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.44/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.44/0.63  fof(f63,plain,(
% 1.44/0.63    ( ! [X6,X7,X5] : (sK6 = X7 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4) | ~m1_subset_1(X5,sK3)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f38])).
% 1.44/0.63  fof(f527,plain,(
% 1.44/0.63    ~spl13_13 | ~spl13_14),
% 1.44/0.63    inference(avatar_split_clause,[],[f518,f524,f520])).
% 1.44/0.63  fof(f518,plain,(
% 1.44/0.63    sK6 != k2_mcart_1(sK7) | ~sP2(sK7,sK5,sK4,sK3)),
% 1.44/0.63    inference(superposition,[],[f67,f101])).
% 1.44/0.63  fof(f101,plain,(
% 1.44/0.63    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0) | ~sP2(X0,X1,X2,X3)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f59])).
% 1.44/0.63  fof(f59,plain,(
% 1.44/0.63    ! [X0,X1,X2,X3] : ((k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0) & k6_mcart_1(X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(X0)) & k5_mcart_1(X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(X0))) | ~sP2(X0,X1,X2,X3))),
% 1.44/0.63    inference(rectify,[],[f58])).
% 1.44/0.63  fof(f58,plain,(
% 1.44/0.63    ! [X3,X2,X1,X0] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~sP2(X3,X2,X1,X0))),
% 1.44/0.63    inference(nnf_transformation,[],[f35])).
% 1.44/0.63  fof(f67,plain,(
% 1.44/0.63    sK6 != k7_mcart_1(sK3,sK4,sK5,sK7)),
% 1.44/0.63    inference(cnf_transformation,[],[f38])).
% 1.44/0.63  % SZS output end Proof for theBenchmark
% 1.44/0.63  % (4867)------------------------------
% 1.44/0.63  % (4867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.63  % (4867)Termination reason: Refutation
% 1.44/0.63  
% 1.44/0.63  % (4867)Memory used [KB]: 6652
% 1.44/0.63  % (4867)Time elapsed: 0.190 s
% 1.44/0.63  % (4867)------------------------------
% 1.44/0.63  % (4867)------------------------------
% 1.44/0.63  % (4838)Success in time 0.266 s
%------------------------------------------------------------------------------
