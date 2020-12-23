%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:29 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 323 expanded)
%              Number of leaves         :   26 (  94 expanded)
%              Depth                    :   20
%              Number of atoms          :  522 (1748 expanded)
%              Number of equality atoms :  209 ( 802 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1752,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f484,f1318,f1402,f1440,f1647,f1732,f1751])).

fof(f1751,plain,
    ( spl13_26
    | ~ spl13_1 ),
    inference(avatar_split_clause,[],[f1344,f133,f1533])).

fof(f1533,plain,
    ( spl13_26
  <=> k1_xboole_0 = k2_zfmisc_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_26])])).

fof(f133,plain,
    ( spl13_1
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f1344,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | ~ spl13_1 ),
    inference(subsumption_resolution,[],[f1328,f64])).

fof(f64,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f20,f36])).

fof(f36,plain,
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

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

fof(f1328,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | k1_xboole_0 = sK5
    | ~ spl13_1 ),
    inference(resolution,[],[f134,f1100])).

fof(f1100,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X1,X0))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(condensation,[],[f1099])).

fof(f1099,plain,(
    ! [X14,X12,X13] :
      ( k1_xboole_0 = X14
      | k1_xboole_0 = X13
      | k1_xboole_0 = X12
      | ~ v1_xboole_0(k2_zfmisc_1(X12,X13)) ) ),
    inference(trivial_inequality_removal,[],[f1089])).

fof(f1089,plain,(
    ! [X14,X12,X13] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = X14
      | k1_xboole_0 = X13
      | k1_xboole_0 = X12
      | ~ v1_xboole_0(k2_zfmisc_1(X12,X13)) ) ),
    inference(superposition,[],[f109,f607])).

fof(f607,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f228,f67])).

fof(f67,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK8(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f39,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK8(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f228,plain,(
    ! [X2,X3] :
      ( r2_hidden(k1_mcart_1(sK9(k2_zfmisc_1(X2,X3))),X2)
      | k1_xboole_0 = k2_zfmisc_1(X2,X3) ) ),
    inference(resolution,[],[f81,f69])).

fof(f69,plain,(
    ! [X0] :
      ( r2_hidden(sK9(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK9(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f21,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK9(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f93,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f134,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | ~ spl13_1 ),
    inference(avatar_component_clause,[],[f133])).

fof(f1732,plain,(
    ~ spl13_26 ),
    inference(avatar_contradiction_clause,[],[f1731])).

fof(f1731,plain,
    ( $false
    | ~ spl13_26 ),
    inference(subsumption_resolution,[],[f1730,f63])).

fof(f63,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f37])).

fof(f1730,plain,
    ( k1_xboole_0 = sK4
    | ~ spl13_26 ),
    inference(subsumption_resolution,[],[f1729,f62])).

fof(f62,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f37])).

fof(f1729,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK4
    | ~ spl13_26 ),
    inference(subsumption_resolution,[],[f1686,f66])).

fof(f66,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1686,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK4
    | ~ spl13_26 ),
    inference(superposition,[],[f1100,f1535])).

fof(f1535,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | ~ spl13_26 ),
    inference(avatar_component_clause,[],[f1533])).

fof(f1647,plain,
    ( spl13_26
    | ~ spl13_20 ),
    inference(avatar_split_clause,[],[f1646,f1308,f1533])).

fof(f1308,plain,
    ( spl13_20
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK7,k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = X0
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_20])])).

fof(f1646,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | ~ spl13_20 ),
    inference(subsumption_resolution,[],[f1627,f64])).

fof(f1627,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | k1_xboole_0 = sK5
    | ~ spl13_20 ),
    inference(resolution,[],[f1309,f105])).

fof(f105,plain,(
    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f60,f80])).

fof(f60,plain,(
    m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f37])).

fof(f1309,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK7,k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = X0
        | k1_xboole_0 = X1 )
    | ~ spl13_20 ),
    inference(avatar_component_clause,[],[f1308])).

fof(f1440,plain,
    ( spl13_20
    | spl13_1
    | spl13_19
    | ~ spl13_21 ),
    inference(avatar_split_clause,[],[f1439,f1311,f481,f133,f1308])).

fof(f481,plain,
    ( spl13_19
  <=> sK6 = k2_mcart_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_19])])).

fof(f1311,plain,
    ( spl13_21
  <=> m1_subset_1(k2_mcart_1(sK7),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_21])])).

fof(f1439,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK7,k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | spl13_1
    | spl13_19
    | ~ spl13_21 ),
    inference(subsumption_resolution,[],[f1438,f483])).

fof(f483,plain,
    ( sK6 != k2_mcart_1(sK7)
    | spl13_19 ),
    inference(avatar_component_clause,[],[f481])).

fof(f1438,plain,
    ( ! [X0,X1] :
        ( sK6 = k2_mcart_1(sK7)
        | ~ m1_subset_1(sK7,k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | spl13_1
    | ~ spl13_21 ),
    inference(subsumption_resolution,[],[f1437,f1312])).

fof(f1312,plain,
    ( m1_subset_1(k2_mcart_1(sK7),sK5)
    | ~ spl13_21 ),
    inference(avatar_component_clause,[],[f1311])).

fof(f1437,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k2_mcart_1(sK7),sK5)
        | sK6 = k2_mcart_1(sK7)
        | ~ m1_subset_1(sK7,k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | spl13_1 ),
    inference(trivial_inequality_removal,[],[f1431])).

fof(f1431,plain,
    ( ! [X0,X1] :
        ( sK7 != sK7
        | ~ m1_subset_1(k2_mcart_1(sK7),sK5)
        | sK6 = k2_mcart_1(sK7)
        | ~ m1_subset_1(sK7,k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | spl13_1 ),
    inference(resolution,[],[f400,f1300])).

fof(f1300,plain,(
    ! [X12,X10,X11] :
      ( ~ sP0(k1_mcart_1(X10),sK4,sK3)
      | sK7 != X10
      | ~ m1_subset_1(k2_mcart_1(X10),sK5)
      | sK6 = k2_mcart_1(X10)
      | ~ m1_subset_1(X10,k2_zfmisc_1(X11,X12))
      | k1_xboole_0 = X12
      | k1_xboole_0 = X11 ) ),
    inference(superposition,[],[f1074,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2
          | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).

fof(f1074,plain,(
    ! [X0,X1] :
      ( sK7 != k4_tarski(X1,X0)
      | ~ sP0(X1,sK4,sK3)
      | ~ m1_subset_1(X0,sK5)
      | sK6 = X0 ) ),
    inference(duplicate_literal_removal,[],[f1073])).

fof(f1073,plain,(
    ! [X0,X1] :
      ( sK6 = X0
      | ~ sP0(X1,sK4,sK3)
      | ~ m1_subset_1(X0,sK5)
      | sK7 != k4_tarski(X1,X0)
      | ~ sP0(X1,sK4,sK3) ) ),
    inference(resolution,[],[f1072,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK11(X0,X1,X2),X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f52,f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X5,X6] :
          ( k4_tarski(X5,X6) = X0
          & r2_hidden(X6,X1)
          & r2_hidden(X5,X2) )
     => ( k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)) = X0
        & r2_hidden(sK12(X0,X1,X2),X1)
        & r2_hidden(sK11(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
    inference(rectify,[],[f51])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X3,X1,X0] :
      ( sP0(X3,X1,X0)
    <=> ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X4,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1072,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK11(X0,sK4,X2),sK3)
      | sK6 = X1
      | ~ sP0(X0,sK4,X2)
      | ~ m1_subset_1(X1,sK5)
      | k4_tarski(X0,X1) != sK7 ) ),
    inference(duplicate_literal_removal,[],[f1071])).

fof(f1071,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X0,X1) != sK7
      | sK6 = X1
      | ~ sP0(X0,sK4,X2)
      | ~ m1_subset_1(X1,sK5)
      | ~ r2_hidden(sK11(X0,sK4,X2),sK3)
      | ~ sP0(X0,sK4,X2) ) ),
    inference(resolution,[],[f1069,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK12(X0,X1,X2),X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f1069,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK12(X1,X2,X3),sK4)
      | sK7 != k4_tarski(X1,X0)
      | sK6 = X0
      | ~ sP0(X1,X2,X3)
      | ~ m1_subset_1(X0,sK5)
      | ~ r2_hidden(sK11(X1,X2,X3),sK3) ) ),
    inference(resolution,[],[f1067,f223])).

fof(f223,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f71,f67])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f1067,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK11(X1,X2,X3),sK3)
      | ~ m1_subset_1(X0,sK5)
      | sK7 != k4_tarski(X1,X0)
      | sK6 = X0
      | ~ sP0(X1,X2,X3)
      | ~ r2_hidden(sK12(X1,X2,X3),sK4) ) ),
    inference(resolution,[],[f990,f223])).

fof(f990,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ m1_subset_1(sK12(X5,X6,X7),sK4)
      | sK6 = X8
      | ~ m1_subset_1(X8,sK5)
      | sK7 != k4_tarski(X5,X8)
      | ~ m1_subset_1(sK11(X5,X6,X7),sK3)
      | ~ sP0(X5,X6,X7) ) ),
    inference(superposition,[],[f104,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)) = X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f104,plain,(
    ! [X6,X7,X5] :
      ( sK7 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK6 = X7
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4)
      | ~ m1_subset_1(X5,sK3) ) ),
    inference(definition_unfolding,[],[f61,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f61,plain,(
    ! [X6,X7,X5] :
      ( sK6 = X7
      | k3_mcart_1(X5,X6,X7) != sK7
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4)
      | ~ m1_subset_1(X5,sK3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f400,plain,
    ( sP0(k1_mcart_1(sK7),sK4,sK3)
    | spl13_1 ),
    inference(resolution,[],[f393,f226])).

fof(f226,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK3,sK4))
    | spl13_1 ),
    inference(resolution,[],[f81,f217])).

fof(f217,plain,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | spl13_1 ),
    inference(subsumption_resolution,[],[f215,f135])).

fof(f135,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | spl13_1 ),
    inference(avatar_component_clause,[],[f133])).

fof(f215,plain,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(resolution,[],[f70,f105])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f393,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | sP0(X0,X2,X1) ) ),
    inference(resolution,[],[f83,f117])).

fof(f117,plain,(
    ! [X0,X1] : sP1(X0,X1,k2_zfmisc_1(X0,X1)) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f4,f32,f31])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP0(X4,X1,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f48,f49])).

fof(f49,plain,(
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

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f1402,plain,(
    spl13_18 ),
    inference(avatar_split_clause,[],[f1401,f477])).

fof(f477,plain,
    ( spl13_18
  <=> sP2(sK7,sK5,sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).

fof(f1401,plain,(
    sP2(sK7,sK5,sK4,sK3) ),
    inference(subsumption_resolution,[],[f1400,f62])).

fof(f1400,plain,
    ( sP2(sK7,sK5,sK4,sK3)
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f1399,f63])).

fof(f1399,plain,
    ( sP2(sK7,sK5,sK4,sK3)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f1374,f64])).

fof(f1374,plain,
    ( sP2(sK7,sK5,sK4,sK3)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f110,f105])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | sP2(X3,X2,X1,X0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f100,f80])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X3,X2,X1,X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( sP2(X3,X2,X1,X0)
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f27,f34])).

fof(f34,plain,(
    ! [X3,X2,X1,X0] :
      ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
        & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
        & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
      | ~ sP2(X3,X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f1318,plain,
    ( spl13_1
    | spl13_21 ),
    inference(avatar_contradiction_clause,[],[f1317])).

fof(f1317,plain,
    ( $false
    | spl13_1
    | spl13_21 ),
    inference(subsumption_resolution,[],[f1315,f247])).

fof(f247,plain,
    ( r2_hidden(k2_mcart_1(sK7),sK5)
    | spl13_1 ),
    inference(resolution,[],[f82,f217])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1315,plain,
    ( ~ r2_hidden(k2_mcart_1(sK7),sK5)
    | spl13_21 ),
    inference(resolution,[],[f1313,f223])).

fof(f1313,plain,
    ( ~ m1_subset_1(k2_mcart_1(sK7),sK5)
    | spl13_21 ),
    inference(avatar_component_clause,[],[f1311])).

fof(f484,plain,
    ( ~ spl13_18
    | ~ spl13_19 ),
    inference(avatar_split_clause,[],[f475,f481,f477])).

fof(f475,plain,
    ( sK6 != k2_mcart_1(sK7)
    | ~ sP2(sK7,sK5,sK4,sK3) ),
    inference(superposition,[],[f65,f99])).

fof(f99,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f65,plain,(
    sK6 != k7_mcart_1(sK3,sK4,sK5,sK7) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (2267)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (2276)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.51  % (2266)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (2261)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (2270)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (2259)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (2273)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (2260)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (2288)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (2285)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (2262)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.36/0.53  % (2257)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.36/0.54  % (2283)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.36/0.54  % (2284)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.54  % (2280)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.36/0.54  % (2274)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.36/0.54  % (2272)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.36/0.54  % (2278)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.36/0.54  % (2279)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.36/0.55  % (2263)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.36/0.55  % (2275)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.36/0.55  % (2268)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.36/0.55  % (2271)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.36/0.55  % (2264)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.36/0.55  % (2269)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.51/0.57  % (2258)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.51/0.58  % (2286)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.51/0.59  % (2265)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.51/0.60  % (2281)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.51/0.60  % (2277)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.51/0.61  % (2277)Refutation not found, incomplete strategy% (2277)------------------------------
% 1.51/0.61  % (2277)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.61  % (2277)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.61  
% 1.51/0.61  % (2277)Memory used [KB]: 10746
% 1.51/0.61  % (2277)Time elapsed: 0.194 s
% 1.51/0.61  % (2277)------------------------------
% 1.51/0.61  % (2277)------------------------------
% 1.51/0.62  % (2285)Refutation found. Thanks to Tanya!
% 1.51/0.62  % SZS status Theorem for theBenchmark
% 1.51/0.62  % SZS output start Proof for theBenchmark
% 1.51/0.62  fof(f1752,plain,(
% 1.51/0.62    $false),
% 1.51/0.62    inference(avatar_sat_refutation,[],[f484,f1318,f1402,f1440,f1647,f1732,f1751])).
% 1.51/0.62  fof(f1751,plain,(
% 1.51/0.62    spl13_26 | ~spl13_1),
% 1.51/0.62    inference(avatar_split_clause,[],[f1344,f133,f1533])).
% 1.51/0.62  fof(f1533,plain,(
% 1.51/0.62    spl13_26 <=> k1_xboole_0 = k2_zfmisc_1(sK3,sK4)),
% 1.51/0.62    introduced(avatar_definition,[new_symbols(naming,[spl13_26])])).
% 1.51/0.62  fof(f133,plain,(
% 1.51/0.62    spl13_1 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 1.51/0.62    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 1.51/0.62  fof(f1344,plain,(
% 1.51/0.62    k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | ~spl13_1),
% 1.51/0.62    inference(subsumption_resolution,[],[f1328,f64])).
% 1.51/0.62  fof(f64,plain,(
% 1.51/0.62    k1_xboole_0 != sK5),
% 1.51/0.62    inference(cnf_transformation,[],[f37])).
% 1.51/0.62  fof(f37,plain,(
% 1.51/0.62    sK6 != k7_mcart_1(sK3,sK4,sK5,sK7) & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & ! [X5] : (! [X6] : (! [X7] : (sK6 = X7 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) | ~m1_subset_1(X5,sK3)) & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))),
% 1.51/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f20,f36])).
% 1.51/0.62  fof(f36,plain,(
% 1.51/0.62    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK6 != k7_mcart_1(sK3,sK4,sK5,sK7) & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & ! [X5] : (! [X6] : (! [X7] : (sK6 = X7 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) | ~m1_subset_1(X5,sK3)) & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)))),
% 1.51/0.62    introduced(choice_axiom,[])).
% 1.51/0.62  fof(f20,plain,(
% 1.51/0.62    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.51/0.62    inference(flattening,[],[f19])).
% 1.51/0.62  fof(f19,plain,(
% 1.51/0.62    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.51/0.62    inference(ennf_transformation,[],[f18])).
% 1.51/0.62  fof(f18,negated_conjecture,(
% 1.51/0.62    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.51/0.62    inference(negated_conjecture,[],[f17])).
% 1.51/0.62  fof(f17,conjecture,(
% 1.51/0.62    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.51/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).
% 1.51/0.62  fof(f1328,plain,(
% 1.51/0.62    k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | k1_xboole_0 = sK5 | ~spl13_1),
% 1.51/0.62    inference(resolution,[],[f134,f1100])).
% 1.51/0.62  fof(f1100,plain,(
% 1.51/0.62    ( ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.51/0.62    inference(condensation,[],[f1099])).
% 1.51/0.62  fof(f1099,plain,(
% 1.51/0.62    ( ! [X14,X12,X13] : (k1_xboole_0 = X14 | k1_xboole_0 = X13 | k1_xboole_0 = X12 | ~v1_xboole_0(k2_zfmisc_1(X12,X13))) )),
% 1.51/0.62    inference(trivial_inequality_removal,[],[f1089])).
% 1.51/0.62  fof(f1089,plain,(
% 1.51/0.62    ( ! [X14,X12,X13] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = X14 | k1_xboole_0 = X13 | k1_xboole_0 = X12 | ~v1_xboole_0(k2_zfmisc_1(X12,X13))) )),
% 1.51/0.62    inference(superposition,[],[f109,f607])).
% 1.51/0.62  fof(f607,plain,(
% 1.51/0.62    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~v1_xboole_0(X0)) )),
% 1.51/0.62    inference(resolution,[],[f228,f67])).
% 1.51/0.62  fof(f67,plain,(
% 1.51/0.62    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.51/0.62    inference(cnf_transformation,[],[f41])).
% 1.51/0.62  fof(f41,plain,(
% 1.51/0.62    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK8(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.51/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f39,f40])).
% 1.51/0.62  fof(f40,plain,(
% 1.51/0.62    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK8(X0),X0))),
% 1.51/0.62    introduced(choice_axiom,[])).
% 1.51/0.62  fof(f39,plain,(
% 1.51/0.62    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.51/0.62    inference(rectify,[],[f38])).
% 1.51/0.62  fof(f38,plain,(
% 1.51/0.62    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.51/0.62    inference(nnf_transformation,[],[f1])).
% 1.51/0.62  fof(f1,axiom,(
% 1.51/0.62    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.51/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.51/0.62  fof(f228,plain,(
% 1.51/0.62    ( ! [X2,X3] : (r2_hidden(k1_mcart_1(sK9(k2_zfmisc_1(X2,X3))),X2) | k1_xboole_0 = k2_zfmisc_1(X2,X3)) )),
% 1.51/0.62    inference(resolution,[],[f81,f69])).
% 1.51/0.62  fof(f69,plain,(
% 1.51/0.62    ( ! [X0] : (r2_hidden(sK9(X0),X0) | k1_xboole_0 = X0) )),
% 1.51/0.62    inference(cnf_transformation,[],[f43])).
% 1.51/0.62  fof(f43,plain,(
% 1.51/0.62    ! [X0] : (r2_hidden(sK9(X0),X0) | k1_xboole_0 = X0)),
% 1.51/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f21,f42])).
% 1.51/0.62  fof(f42,plain,(
% 1.51/0.62    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK9(X0),X0))),
% 1.51/0.62    introduced(choice_axiom,[])).
% 1.51/0.62  fof(f21,plain,(
% 1.51/0.62    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.51/0.62    inference(ennf_transformation,[],[f3])).
% 1.51/0.62  fof(f3,axiom,(
% 1.51/0.62    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.51/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.51/0.62  fof(f81,plain,(
% 1.51/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.51/0.62    inference(cnf_transformation,[],[f26])).
% 1.51/0.62  fof(f26,plain,(
% 1.51/0.62    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.51/0.62    inference(ennf_transformation,[],[f13])).
% 1.51/0.62  fof(f13,axiom,(
% 1.51/0.62    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.51/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.51/0.62  fof(f109,plain,(
% 1.51/0.62    ( ! [X2,X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.51/0.62    inference(definition_unfolding,[],[f93,f80])).
% 1.51/0.62  fof(f80,plain,(
% 1.51/0.62    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.51/0.62    inference(cnf_transformation,[],[f9])).
% 1.51/0.62  fof(f9,axiom,(
% 1.51/0.62    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.51/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.51/0.62  fof(f93,plain,(
% 1.51/0.62    ( ! [X2,X0,X1] : (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.51/0.62    inference(cnf_transformation,[],[f57])).
% 1.51/0.62  fof(f57,plain,(
% 1.51/0.62    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.51/0.62    inference(flattening,[],[f56])).
% 1.51/0.62  fof(f56,plain,(
% 1.51/0.62    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | (k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.51/0.62    inference(nnf_transformation,[],[f15])).
% 1.51/0.62  fof(f15,axiom,(
% 1.51/0.62    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2))),
% 1.51/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).
% 1.51/0.62  fof(f134,plain,(
% 1.51/0.62    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | ~spl13_1),
% 1.51/0.62    inference(avatar_component_clause,[],[f133])).
% 1.51/0.62  fof(f1732,plain,(
% 1.51/0.62    ~spl13_26),
% 1.51/0.62    inference(avatar_contradiction_clause,[],[f1731])).
% 1.51/0.62  fof(f1731,plain,(
% 1.51/0.62    $false | ~spl13_26),
% 1.51/0.62    inference(subsumption_resolution,[],[f1730,f63])).
% 1.51/0.62  fof(f63,plain,(
% 1.51/0.62    k1_xboole_0 != sK4),
% 1.51/0.62    inference(cnf_transformation,[],[f37])).
% 1.51/0.62  fof(f1730,plain,(
% 1.51/0.62    k1_xboole_0 = sK4 | ~spl13_26),
% 1.51/0.62    inference(subsumption_resolution,[],[f1729,f62])).
% 1.51/0.62  fof(f62,plain,(
% 1.51/0.62    k1_xboole_0 != sK3),
% 1.51/0.62    inference(cnf_transformation,[],[f37])).
% 1.51/0.62  fof(f1729,plain,(
% 1.51/0.62    k1_xboole_0 = sK3 | k1_xboole_0 = sK4 | ~spl13_26),
% 1.51/0.62    inference(subsumption_resolution,[],[f1686,f66])).
% 1.51/0.62  fof(f66,plain,(
% 1.51/0.62    v1_xboole_0(k1_xboole_0)),
% 1.51/0.62    inference(cnf_transformation,[],[f2])).
% 1.51/0.62  fof(f2,axiom,(
% 1.51/0.62    v1_xboole_0(k1_xboole_0)),
% 1.51/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.51/0.62  fof(f1686,plain,(
% 1.51/0.62    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK3 | k1_xboole_0 = sK4 | ~spl13_26),
% 1.51/0.62    inference(superposition,[],[f1100,f1535])).
% 1.51/0.62  fof(f1535,plain,(
% 1.51/0.62    k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | ~spl13_26),
% 1.51/0.62    inference(avatar_component_clause,[],[f1533])).
% 1.51/0.62  fof(f1647,plain,(
% 1.51/0.62    spl13_26 | ~spl13_20),
% 1.51/0.62    inference(avatar_split_clause,[],[f1646,f1308,f1533])).
% 1.51/0.62  fof(f1308,plain,(
% 1.51/0.62    spl13_20 <=> ! [X1,X0] : (~m1_subset_1(sK7,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0 | k1_xboole_0 = X1)),
% 1.51/0.62    introduced(avatar_definition,[new_symbols(naming,[spl13_20])])).
% 1.51/0.62  fof(f1646,plain,(
% 1.51/0.62    k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | ~spl13_20),
% 1.51/0.62    inference(subsumption_resolution,[],[f1627,f64])).
% 1.51/0.62  fof(f1627,plain,(
% 1.51/0.62    k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | k1_xboole_0 = sK5 | ~spl13_20),
% 1.51/0.62    inference(resolution,[],[f1309,f105])).
% 1.51/0.62  fof(f105,plain,(
% 1.51/0.62    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 1.51/0.62    inference(definition_unfolding,[],[f60,f80])).
% 1.51/0.62  fof(f60,plain,(
% 1.51/0.62    m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))),
% 1.51/0.62    inference(cnf_transformation,[],[f37])).
% 1.51/0.62  fof(f1309,plain,(
% 1.51/0.62    ( ! [X0,X1] : (~m1_subset_1(sK7,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0 | k1_xboole_0 = X1) ) | ~spl13_20),
% 1.51/0.62    inference(avatar_component_clause,[],[f1308])).
% 1.51/0.62  fof(f1440,plain,(
% 1.51/0.62    spl13_20 | spl13_1 | spl13_19 | ~spl13_21),
% 1.51/0.62    inference(avatar_split_clause,[],[f1439,f1311,f481,f133,f1308])).
% 1.51/0.62  fof(f481,plain,(
% 1.51/0.62    spl13_19 <=> sK6 = k2_mcart_1(sK7)),
% 1.51/0.62    introduced(avatar_definition,[new_symbols(naming,[spl13_19])])).
% 1.51/0.62  fof(f1311,plain,(
% 1.51/0.62    spl13_21 <=> m1_subset_1(k2_mcart_1(sK7),sK5)),
% 1.51/0.62    introduced(avatar_definition,[new_symbols(naming,[spl13_21])])).
% 1.51/0.62  fof(f1439,plain,(
% 1.51/0.62    ( ! [X0,X1] : (~m1_subset_1(sK7,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | (spl13_1 | spl13_19 | ~spl13_21)),
% 1.51/0.62    inference(subsumption_resolution,[],[f1438,f483])).
% 1.51/0.62  fof(f483,plain,(
% 1.51/0.62    sK6 != k2_mcart_1(sK7) | spl13_19),
% 1.51/0.62    inference(avatar_component_clause,[],[f481])).
% 1.51/0.62  fof(f1438,plain,(
% 1.51/0.62    ( ! [X0,X1] : (sK6 = k2_mcart_1(sK7) | ~m1_subset_1(sK7,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | (spl13_1 | ~spl13_21)),
% 1.51/0.62    inference(subsumption_resolution,[],[f1437,f1312])).
% 1.51/0.62  fof(f1312,plain,(
% 1.51/0.62    m1_subset_1(k2_mcart_1(sK7),sK5) | ~spl13_21),
% 1.51/0.62    inference(avatar_component_clause,[],[f1311])).
% 1.51/0.62  fof(f1437,plain,(
% 1.51/0.62    ( ! [X0,X1] : (~m1_subset_1(k2_mcart_1(sK7),sK5) | sK6 = k2_mcart_1(sK7) | ~m1_subset_1(sK7,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | spl13_1),
% 1.51/0.62    inference(trivial_inequality_removal,[],[f1431])).
% 1.51/0.62  fof(f1431,plain,(
% 1.51/0.62    ( ! [X0,X1] : (sK7 != sK7 | ~m1_subset_1(k2_mcart_1(sK7),sK5) | sK6 = k2_mcart_1(sK7) | ~m1_subset_1(sK7,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | spl13_1),
% 1.51/0.62    inference(resolution,[],[f400,f1300])).
% 1.51/0.62  fof(f1300,plain,(
% 1.51/0.62    ( ! [X12,X10,X11] : (~sP0(k1_mcart_1(X10),sK4,sK3) | sK7 != X10 | ~m1_subset_1(k2_mcart_1(X10),sK5) | sK6 = k2_mcart_1(X10) | ~m1_subset_1(X10,k2_zfmisc_1(X11,X12)) | k1_xboole_0 = X12 | k1_xboole_0 = X11) )),
% 1.51/0.62    inference(superposition,[],[f1074,f78])).
% 1.51/0.62  fof(f78,plain,(
% 1.51/0.62    ( ! [X2,X0,X1] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.51/0.62    inference(cnf_transformation,[],[f25])).
% 1.51/0.62  fof(f25,plain,(
% 1.51/0.62    ! [X0,X1] : (! [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.51/0.62    inference(ennf_transformation,[],[f14])).
% 1.51/0.62  fof(f14,axiom,(
% 1.51/0.62    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.51/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).
% 1.51/0.62  fof(f1074,plain,(
% 1.51/0.62    ( ! [X0,X1] : (sK7 != k4_tarski(X1,X0) | ~sP0(X1,sK4,sK3) | ~m1_subset_1(X0,sK5) | sK6 = X0) )),
% 1.51/0.62    inference(duplicate_literal_removal,[],[f1073])).
% 1.51/0.62  fof(f1073,plain,(
% 1.51/0.62    ( ! [X0,X1] : (sK6 = X0 | ~sP0(X1,sK4,sK3) | ~m1_subset_1(X0,sK5) | sK7 != k4_tarski(X1,X0) | ~sP0(X1,sK4,sK3)) )),
% 1.51/0.62    inference(resolution,[],[f1072,f87])).
% 1.51/0.62  fof(f87,plain,(
% 1.51/0.62    ( ! [X2,X0,X1] : (r2_hidden(sK11(X0,X1,X2),X2) | ~sP0(X0,X1,X2)) )),
% 1.51/0.62    inference(cnf_transformation,[],[f54])).
% 1.51/0.62  fof(f54,plain,(
% 1.51/0.62    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3,X4] : (k4_tarski(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2))) & ((k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)) = X0 & r2_hidden(sK12(X0,X1,X2),X1) & r2_hidden(sK11(X0,X1,X2),X2)) | ~sP0(X0,X1,X2)))),
% 1.51/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f52,f53])).
% 1.51/0.62  fof(f53,plain,(
% 1.51/0.62    ! [X2,X1,X0] : (? [X5,X6] : (k4_tarski(X5,X6) = X0 & r2_hidden(X6,X1) & r2_hidden(X5,X2)) => (k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)) = X0 & r2_hidden(sK12(X0,X1,X2),X1) & r2_hidden(sK11(X0,X1,X2),X2)))),
% 1.51/0.62    introduced(choice_axiom,[])).
% 1.51/0.62  fof(f52,plain,(
% 1.51/0.62    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3,X4] : (k4_tarski(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2))) & (? [X5,X6] : (k4_tarski(X5,X6) = X0 & r2_hidden(X6,X1) & r2_hidden(X5,X2)) | ~sP0(X0,X1,X2)))),
% 1.51/0.62    inference(rectify,[],[f51])).
% 1.51/0.62  fof(f51,plain,(
% 1.51/0.62    ! [X3,X1,X0] : ((sP0(X3,X1,X0) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~sP0(X3,X1,X0)))),
% 1.51/0.62    inference(nnf_transformation,[],[f31])).
% 1.51/0.62  fof(f31,plain,(
% 1.51/0.62    ! [X3,X1,X0] : (sP0(X3,X1,X0) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)))),
% 1.51/0.62    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.08/0.64  fof(f1072,plain,(
% 2.08/0.64    ( ! [X2,X0,X1] : (~r2_hidden(sK11(X0,sK4,X2),sK3) | sK6 = X1 | ~sP0(X0,sK4,X2) | ~m1_subset_1(X1,sK5) | k4_tarski(X0,X1) != sK7) )),
% 2.08/0.64    inference(duplicate_literal_removal,[],[f1071])).
% 2.08/0.64  fof(f1071,plain,(
% 2.08/0.64    ( ! [X2,X0,X1] : (k4_tarski(X0,X1) != sK7 | sK6 = X1 | ~sP0(X0,sK4,X2) | ~m1_subset_1(X1,sK5) | ~r2_hidden(sK11(X0,sK4,X2),sK3) | ~sP0(X0,sK4,X2)) )),
% 2.08/0.64    inference(resolution,[],[f1069,f88])).
% 2.08/0.64  fof(f88,plain,(
% 2.08/0.64    ( ! [X2,X0,X1] : (r2_hidden(sK12(X0,X1,X2),X1) | ~sP0(X0,X1,X2)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f54])).
% 2.08/0.64  fof(f1069,plain,(
% 2.08/0.64    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK12(X1,X2,X3),sK4) | sK7 != k4_tarski(X1,X0) | sK6 = X0 | ~sP0(X1,X2,X3) | ~m1_subset_1(X0,sK5) | ~r2_hidden(sK11(X1,X2,X3),sK3)) )),
% 2.08/0.64    inference(resolution,[],[f1067,f223])).
% 2.08/0.64  fof(f223,plain,(
% 2.08/0.64    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) )),
% 2.08/0.64    inference(subsumption_resolution,[],[f71,f67])).
% 2.08/0.64  fof(f71,plain,(
% 2.08/0.64    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f44])).
% 2.08/0.64  fof(f44,plain,(
% 2.08/0.64    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.08/0.64    inference(nnf_transformation,[],[f22])).
% 2.08/0.64  fof(f22,plain,(
% 2.08/0.64    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.08/0.64    inference(ennf_transformation,[],[f6])).
% 2.08/0.64  fof(f6,axiom,(
% 2.08/0.64    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 2.08/0.64  fof(f1067,plain,(
% 2.08/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK11(X1,X2,X3),sK3) | ~m1_subset_1(X0,sK5) | sK7 != k4_tarski(X1,X0) | sK6 = X0 | ~sP0(X1,X2,X3) | ~r2_hidden(sK12(X1,X2,X3),sK4)) )),
% 2.08/0.64    inference(resolution,[],[f990,f223])).
% 2.08/0.64  fof(f990,plain,(
% 2.08/0.64    ( ! [X6,X8,X7,X5] : (~m1_subset_1(sK12(X5,X6,X7),sK4) | sK6 = X8 | ~m1_subset_1(X8,sK5) | sK7 != k4_tarski(X5,X8) | ~m1_subset_1(sK11(X5,X6,X7),sK3) | ~sP0(X5,X6,X7)) )),
% 2.08/0.64    inference(superposition,[],[f104,f89])).
% 2.08/0.64  fof(f89,plain,(
% 2.08/0.64    ( ! [X2,X0,X1] : (k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)) = X0 | ~sP0(X0,X1,X2)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f54])).
% 2.08/0.64  fof(f104,plain,(
% 2.08/0.64    ( ! [X6,X7,X5] : (sK7 != k4_tarski(k4_tarski(X5,X6),X7) | sK6 = X7 | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4) | ~m1_subset_1(X5,sK3)) )),
% 2.08/0.64    inference(definition_unfolding,[],[f61,f79])).
% 2.08/0.64  fof(f79,plain,(
% 2.08/0.64    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f8])).
% 2.08/0.64  fof(f8,axiom,(
% 2.08/0.64    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 2.08/0.64  fof(f61,plain,(
% 2.08/0.64    ( ! [X6,X7,X5] : (sK6 = X7 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4) | ~m1_subset_1(X5,sK3)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f37])).
% 2.08/0.64  fof(f400,plain,(
% 2.08/0.64    sP0(k1_mcart_1(sK7),sK4,sK3) | spl13_1),
% 2.08/0.64    inference(resolution,[],[f393,f226])).
% 2.08/0.64  fof(f226,plain,(
% 2.08/0.64    r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK3,sK4)) | spl13_1),
% 2.08/0.64    inference(resolution,[],[f81,f217])).
% 2.08/0.64  fof(f217,plain,(
% 2.08/0.64    r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | spl13_1),
% 2.08/0.64    inference(subsumption_resolution,[],[f215,f135])).
% 2.08/0.64  fof(f135,plain,(
% 2.08/0.64    ~v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | spl13_1),
% 2.08/0.64    inference(avatar_component_clause,[],[f133])).
% 2.08/0.64  fof(f215,plain,(
% 2.08/0.64    r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 2.08/0.64    inference(resolution,[],[f70,f105])).
% 2.08/0.64  fof(f70,plain,(
% 2.08/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f44])).
% 2.08/0.64  fof(f393,plain,(
% 2.08/0.64    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | sP0(X0,X2,X1)) )),
% 2.08/0.64    inference(resolution,[],[f83,f117])).
% 2.08/0.64  fof(f117,plain,(
% 2.08/0.64    ( ! [X0,X1] : (sP1(X0,X1,k2_zfmisc_1(X0,X1))) )),
% 2.08/0.64    inference(equality_resolution,[],[f91])).
% 2.08/0.64  fof(f91,plain,(
% 2.08/0.64    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.08/0.64    inference(cnf_transformation,[],[f55])).
% 2.08/0.64  fof(f55,plain,(
% 2.08/0.64    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k2_zfmisc_1(X0,X1) != X2))),
% 2.08/0.64    inference(nnf_transformation,[],[f33])).
% 2.08/0.64  fof(f33,plain,(
% 2.08/0.64    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 2.08/0.64    inference(definition_folding,[],[f4,f32,f31])).
% 2.08/0.64  fof(f32,plain,(
% 2.08/0.64    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X3,X1,X0)))),
% 2.08/0.64    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.08/0.64  fof(f4,axiom,(
% 2.08/0.64    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 2.08/0.64  fof(f83,plain,(
% 2.08/0.64    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | sP0(X4,X1,X0)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f50])).
% 2.08/0.64  fof(f50,plain,(
% 2.08/0.64    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(sK10(X0,X1,X2),X1,X0) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (sP0(sK10(X0,X1,X2),X1,X0) | r2_hidden(sK10(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X4,X1,X0)) & (sP0(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 2.08/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f48,f49])).
% 2.08/0.64  fof(f49,plain,(
% 2.08/0.64    ! [X2,X1,X0] : (? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2))) => ((~sP0(sK10(X0,X1,X2),X1,X0) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (sP0(sK10(X0,X1,X2),X1,X0) | r2_hidden(sK10(X0,X1,X2),X2))))),
% 2.08/0.64    introduced(choice_axiom,[])).
% 2.08/0.64  fof(f48,plain,(
% 2.08/0.64    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X4,X1,X0)) & (sP0(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 2.08/0.64    inference(rectify,[],[f47])).
% 2.08/0.64  fof(f47,plain,(
% 2.08/0.64    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X3,X1,X0)) & (sP0(X3,X1,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 2.08/0.64    inference(nnf_transformation,[],[f32])).
% 2.08/0.64  fof(f1402,plain,(
% 2.08/0.64    spl13_18),
% 2.08/0.64    inference(avatar_split_clause,[],[f1401,f477])).
% 2.08/0.64  fof(f477,plain,(
% 2.08/0.64    spl13_18 <=> sP2(sK7,sK5,sK4,sK3)),
% 2.08/0.64    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).
% 2.08/0.64  fof(f1401,plain,(
% 2.08/0.64    sP2(sK7,sK5,sK4,sK3)),
% 2.08/0.64    inference(subsumption_resolution,[],[f1400,f62])).
% 2.08/0.64  fof(f1400,plain,(
% 2.08/0.64    sP2(sK7,sK5,sK4,sK3) | k1_xboole_0 = sK3),
% 2.08/0.64    inference(subsumption_resolution,[],[f1399,f63])).
% 2.08/0.64  fof(f1399,plain,(
% 2.08/0.64    sP2(sK7,sK5,sK4,sK3) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3),
% 2.08/0.64    inference(subsumption_resolution,[],[f1374,f64])).
% 2.08/0.64  fof(f1374,plain,(
% 2.08/0.64    sP2(sK7,sK5,sK4,sK3) | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | k1_xboole_0 = sK3),
% 2.08/0.64    inference(resolution,[],[f110,f105])).
% 2.08/0.64  fof(f110,plain,(
% 2.08/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | sP2(X3,X2,X1,X0) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.08/0.64    inference(definition_unfolding,[],[f100,f80])).
% 2.08/0.64  fof(f100,plain,(
% 2.08/0.64    ( ! [X2,X0,X3,X1] : (sP2(X3,X2,X1,X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.08/0.64    inference(cnf_transformation,[],[f35])).
% 2.08/0.64  fof(f35,plain,(
% 2.08/0.64    ! [X0,X1,X2] : (! [X3] : (sP2(X3,X2,X1,X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.08/0.64    inference(definition_folding,[],[f27,f34])).
% 2.08/0.64  fof(f34,plain,(
% 2.08/0.64    ! [X3,X2,X1,X0] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~sP2(X3,X2,X1,X0))),
% 2.08/0.64    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.08/0.64  fof(f27,plain,(
% 2.08/0.64    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.08/0.64    inference(ennf_transformation,[],[f16])).
% 2.08/0.64  fof(f16,axiom,(
% 2.08/0.64    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 2.08/0.64  fof(f1318,plain,(
% 2.08/0.64    spl13_1 | spl13_21),
% 2.08/0.64    inference(avatar_contradiction_clause,[],[f1317])).
% 2.08/0.64  fof(f1317,plain,(
% 2.08/0.64    $false | (spl13_1 | spl13_21)),
% 2.08/0.64    inference(subsumption_resolution,[],[f1315,f247])).
% 2.08/0.64  fof(f247,plain,(
% 2.08/0.64    r2_hidden(k2_mcart_1(sK7),sK5) | spl13_1),
% 2.08/0.64    inference(resolution,[],[f82,f217])).
% 2.08/0.64  fof(f82,plain,(
% 2.08/0.64    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f26])).
% 2.08/0.64  fof(f1315,plain,(
% 2.08/0.64    ~r2_hidden(k2_mcart_1(sK7),sK5) | spl13_21),
% 2.08/0.64    inference(resolution,[],[f1313,f223])).
% 2.08/0.64  fof(f1313,plain,(
% 2.08/0.64    ~m1_subset_1(k2_mcart_1(sK7),sK5) | spl13_21),
% 2.08/0.64    inference(avatar_component_clause,[],[f1311])).
% 2.08/0.64  fof(f484,plain,(
% 2.08/0.64    ~spl13_18 | ~spl13_19),
% 2.08/0.64    inference(avatar_split_clause,[],[f475,f481,f477])).
% 2.08/0.64  fof(f475,plain,(
% 2.08/0.64    sK6 != k2_mcart_1(sK7) | ~sP2(sK7,sK5,sK4,sK3)),
% 2.08/0.64    inference(superposition,[],[f65,f99])).
% 2.08/0.64  fof(f99,plain,(
% 2.08/0.64    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0) | ~sP2(X0,X1,X2,X3)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f59])).
% 2.08/0.64  fof(f59,plain,(
% 2.08/0.64    ! [X0,X1,X2,X3] : ((k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0) & k6_mcart_1(X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(X0)) & k5_mcart_1(X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(X0))) | ~sP2(X0,X1,X2,X3))),
% 2.08/0.64    inference(rectify,[],[f58])).
% 2.08/0.64  fof(f58,plain,(
% 2.08/0.64    ! [X3,X2,X1,X0] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~sP2(X3,X2,X1,X0))),
% 2.08/0.64    inference(nnf_transformation,[],[f34])).
% 2.08/0.65  fof(f65,plain,(
% 2.08/0.65    sK6 != k7_mcart_1(sK3,sK4,sK5,sK7)),
% 2.08/0.65    inference(cnf_transformation,[],[f37])).
% 2.08/0.65  % SZS output end Proof for theBenchmark
% 2.08/0.65  % (2285)------------------------------
% 2.08/0.65  % (2285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.65  % (2285)Termination reason: Refutation
% 2.08/0.65  
% 2.08/0.65  % (2285)Memory used [KB]: 6780
% 2.08/0.65  % (2285)Time elapsed: 0.226 s
% 2.08/0.65  % (2285)------------------------------
% 2.08/0.65  % (2285)------------------------------
% 2.08/0.65  % (2250)Success in time 0.291 s
%------------------------------------------------------------------------------
