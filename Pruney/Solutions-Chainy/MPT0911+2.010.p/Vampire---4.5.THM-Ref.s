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
% DateTime   : Thu Dec  3 12:59:30 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 538 expanded)
%              Number of leaves         :   27 ( 151 expanded)
%              Depth                    :   21
%              Number of atoms          :  573 (3276 expanded)
%              Number of equality atoms :  255 (1741 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f840,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f458,f606,f633,f649,f725,f833])).

fof(f833,plain,(
    ~ spl15_13 ),
    inference(avatar_contradiction_clause,[],[f832])).

fof(f832,plain,
    ( $false
    | ~ spl15_13 ),
    inference(subsumption_resolution,[],[f767,f724])).

fof(f724,plain,
    ( ! [X12] : k1_xboole_0 = X12
    | ~ spl15_13 ),
    inference(avatar_component_clause,[],[f723])).

fof(f723,plain,
    ( spl15_13
  <=> ! [X12] : k1_xboole_0 = X12 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_13])])).

fof(f767,plain,
    ( k1_xboole_0 != sK5
    | ~ spl15_13 ),
    inference(backward_demodulation,[],[f568,f724])).

fof(f568,plain,(
    sK5 != k2_mcart_1(sK6) ),
    inference(superposition,[],[f64,f550])).

fof(f550,plain,(
    k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6) ),
    inference(subsumption_resolution,[],[f549,f61])).

fof(f61,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( sK5 != k7_mcart_1(sK2,sK3,sK4,sK6)
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK5 = X7
                | k3_mcart_1(X5,X6,X7) != sK6
                | ~ m1_subset_1(X7,sK4) )
            | ~ m1_subset_1(X6,sK3) )
        | ~ m1_subset_1(X5,sK2) )
    & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f21,f36])).

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
   => ( sK5 != k7_mcart_1(sK2,sK3,sK4,sK6)
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK5 = X7
                  | k3_mcart_1(X5,X6,X7) != sK6
                  | ~ m1_subset_1(X7,sK4) )
              | ~ m1_subset_1(X6,sK3) )
          | ~ m1_subset_1(X5,sK2) )
      & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f20])).

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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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

fof(f549,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f548,f62])).

fof(f62,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f37])).

fof(f548,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f540,f63])).

fof(f63,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f37])).

fof(f540,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f113,f109])).

fof(f109,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(definition_unfolding,[],[f59,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f59,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f37])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f99,f75])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f64,plain,(
    sK5 != k7_mcart_1(sK2,sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f725,plain,
    ( spl15_13
    | spl15_13
    | ~ spl15_5 ),
    inference(avatar_split_clause,[],[f721,f429,f723,f723])).

fof(f429,plain,
    ( spl15_5
  <=> ! [X8] : ~ r2_hidden(X8,k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_5])])).

fof(f721,plain,
    ( ! [X12,X13] :
        ( k1_xboole_0 = X13
        | k1_xboole_0 = X12 )
    | ~ spl15_5 ),
    inference(subsumption_resolution,[],[f720,f348])).

fof(f348,plain,(
    ! [X3] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3) ),
    inference(backward_demodulation,[],[f128,f338])).

fof(f338,plain,(
    ! [X5] : k1_xboole_0 = k2_zfmisc_1(X5,k1_xboole_0) ),
    inference(resolution,[],[f327,f138])).

fof(f138,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f68,f66])).

fof(f66,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK7(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f39,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK7(X0),X0) ) ),
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

fof(f68,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5,X6] :
            ( r1_xboole_0(X2,X0)
            | ~ r2_hidden(X6,sK8(X0))
            | ~ r2_hidden(X5,X6)
            | ~ r2_hidden(X4,X5)
            | ~ r2_hidden(X3,X4)
            | ~ r2_hidden(X2,X3) )
        & r2_hidden(sK8(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f23,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
     => ( ! [X6,X5,X4,X3,X2] :
            ( r1_xboole_0(X2,X0)
            | ~ r2_hidden(X6,sK8(X0))
            | ~ r2_hidden(X5,X6)
            | ~ r2_hidden(X4,X5)
            | ~ r2_hidden(X3,X4)
            | ~ r2_hidden(X2,X3) )
        & r2_hidden(sK8(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

fof(f327,plain,(
    ! [X4] : v1_xboole_0(k2_zfmisc_1(X4,k1_xboole_0)) ),
    inference(resolution,[],[f168,f135])).

fof(f135,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f73,f65])).

fof(f65,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f168,plain,(
    ! [X0,X1] :
      ( r2_hidden(k2_mcart_1(sK7(k2_zfmisc_1(X0,X1))),X1)
      | v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    inference(resolution,[],[f77,f67])).

fof(f67,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f128,plain,(
    ! [X0,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) ),
    inference(equality_resolution,[],[f118])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f105,f107])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f100,f75])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f720,plain,
    ( ! [X12,X13] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X13)
        | k1_xboole_0 = X13
        | k1_xboole_0 = X12 )
    | ~ spl15_5 ),
    inference(forward_demodulation,[],[f719,f348])).

fof(f719,plain,
    ( ! [X12,X13] :
        ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12),X13)
        | k1_xboole_0 = X13
        | k1_xboole_0 = X12 )
    | ~ spl15_5 ),
    inference(subsumption_resolution,[],[f718,f61])).

fof(f718,plain,
    ( ! [X12,X13] :
        ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12),X13)
        | k1_xboole_0 = X13
        | k1_xboole_0 = X12
        | k1_xboole_0 = sK2 )
    | ~ spl15_5 ),
    inference(subsumption_resolution,[],[f694,f62])).

fof(f694,plain,
    ( ! [X12,X13] :
        ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12),X13)
        | k1_xboole_0 = X13
        | k1_xboole_0 = X12
        | k1_xboole_0 = sK3
        | k1_xboole_0 = sK2 )
    | ~ spl15_5 ),
    inference(superposition,[],[f121,f662])).

fof(f662,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK2,sK3)
    | ~ spl15_5 ),
    inference(resolution,[],[f430,f68])).

fof(f430,plain,
    ( ! [X8] : ~ r2_hidden(X8,k2_zfmisc_1(sK2,sK3))
    | ~ spl15_5 ),
    inference(avatar_component_clause,[],[f429])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f102,f107])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f649,plain,(
    ~ spl15_6 ),
    inference(avatar_contradiction_clause,[],[f648])).

fof(f648,plain,
    ( $false
    | ~ spl15_6 ),
    inference(subsumption_resolution,[],[f638,f63])).

fof(f638,plain,
    ( k1_xboole_0 = sK4
    | ~ spl15_6 ),
    inference(resolution,[],[f433,f68])).

fof(f433,plain,
    ( ! [X7] : ~ r2_hidden(X7,sK4)
    | ~ spl15_6 ),
    inference(avatar_component_clause,[],[f432])).

fof(f432,plain,
    ( spl15_6
  <=> ! [X7] : ~ r2_hidden(X7,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_6])])).

fof(f633,plain,
    ( spl15_5
    | spl15_6
    | ~ spl15_2 ),
    inference(avatar_split_clause,[],[f427,f153,f432,f429])).

fof(f153,plain,
    ( spl15_2
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).

fof(f427,plain,
    ( ! [X8,X7] :
        ( ~ r2_hidden(X7,sK4)
        | ~ r2_hidden(X8,k2_zfmisc_1(sK2,sK3)) )
    | ~ spl15_2 ),
    inference(subsumption_resolution,[],[f423,f135])).

fof(f423,plain,
    ( ! [X8,X7] :
        ( ~ r2_hidden(X7,sK4)
        | ~ r2_hidden(X8,k2_zfmisc_1(sK2,sK3))
        | r2_hidden(k4_tarski(X8,X7),k1_xboole_0) )
    | ~ spl15_2 ),
    inference(resolution,[],[f125,f160])).

fof(f160,plain,
    ( sP1(sK4,k2_zfmisc_1(sK2,sK3),k1_xboole_0)
    | ~ spl15_2 ),
    inference(superposition,[],[f126,f157])).

fof(f157,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
    | ~ spl15_2 ),
    inference(resolution,[],[f155,f138])).

fof(f155,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
    | ~ spl15_2 ),
    inference(avatar_component_clause,[],[f153])).

fof(f126,plain,(
    ! [X0,X1] : sP1(X1,X0,k2_zfmisc_1(X0,X1)) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ~ sP1(X1,X0,X2) )
      & ( sP1(X1,X0,X2)
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> sP1(X1,X0,X2) ) ),
    inference(definition_folding,[],[f5,f34])).

fof(f34,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f125,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X10,X0)
      | ~ r2_hidden(X9,X1)
      | r2_hidden(k4_tarski(X9,X10),X2) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X0)
      | ~ r2_hidden(X9,X1)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK10(X0,X1,X2)
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X1) )
            | ~ r2_hidden(sK10(X0,X1,X2),X2) )
          & ( ( sK10(X0,X1,X2) = k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2))
              & r2_hidden(sK12(X0,X1,X2),X0)
              & r2_hidden(sK11(X0,X1,X2),X1) )
            | r2_hidden(sK10(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X0)
                  | ~ r2_hidden(X9,X1) ) )
            & ( ( k4_tarski(sK13(X0,X1,X8),sK14(X0,X1,X8)) = X8
                & r2_hidden(sK14(X0,X1,X8),X0)
                & r2_hidden(sK13(X0,X1,X8),X1) )
              | ~ r2_hidden(X8,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12,sK13,sK14])],[f51,f54,f53,f52])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X0)
                & r2_hidden(X6,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK10(X0,X1,X2)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X1) )
          | ~ r2_hidden(sK10(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK10(X0,X1,X2)
              & r2_hidden(X7,X0)
              & r2_hidden(X6,X1) )
          | r2_hidden(sK10(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK10(X0,X1,X2)
          & r2_hidden(X7,X0)
          & r2_hidden(X6,X1) )
     => ( sK10(X0,X1,X2) = k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2))
        & r2_hidden(sK12(X0,X1,X2),X0)
        & r2_hidden(sK11(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X0)
          & r2_hidden(X11,X1) )
     => ( k4_tarski(sK13(X0,X1,X8),sK14(X0,X1,X8)) = X8
        & r2_hidden(sK14(X0,X1,X8),X0)
        & r2_hidden(sK13(X0,X1,X8),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X0)
                  | ~ r2_hidden(X4,X1) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X0)
                  & r2_hidden(X6,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X0)
                  | ~ r2_hidden(X9,X1) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X0)
                  & r2_hidden(X11,X1) )
              | ~ r2_hidden(X8,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
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
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f606,plain,(
    ~ spl15_1 ),
    inference(avatar_contradiction_clause,[],[f605])).

fof(f605,plain,
    ( $false
    | ~ spl15_1 ),
    inference(subsumption_resolution,[],[f604,f531])).

fof(f531,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2)
    | ~ spl15_1 ),
    inference(resolution,[],[f520,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f520,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK2)
    | ~ spl15_1 ),
    inference(resolution,[],[f507,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f507,plain,
    ( r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK2,sK3))
    | ~ spl15_1 ),
    inference(resolution,[],[f151,f76])).

fof(f151,plain,
    ( r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
    | ~ spl15_1 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl15_1
  <=> r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).

fof(f604,plain,
    ( ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2)
    | ~ spl15_1 ),
    inference(subsumption_resolution,[],[f603,f523])).

fof(f523,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ spl15_1 ),
    inference(resolution,[],[f519,f72])).

fof(f519,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ spl15_1 ),
    inference(resolution,[],[f507,f77])).

fof(f603,plain,
    ( ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2)
    | ~ spl15_1 ),
    inference(subsumption_resolution,[],[f602,f510])).

fof(f510,plain,
    ( m1_subset_1(k2_mcart_1(sK6),sK4)
    | ~ spl15_1 ),
    inference(resolution,[],[f506,f72])).

fof(f506,plain,
    ( r2_hidden(k2_mcart_1(sK6),sK4)
    | ~ spl15_1 ),
    inference(resolution,[],[f151,f77])).

fof(f602,plain,
    ( ~ m1_subset_1(k2_mcart_1(sK6),sK4)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) ),
    inference(subsumption_resolution,[],[f601,f568])).

fof(f601,plain,
    ( sK5 = k2_mcart_1(sK6)
    | ~ m1_subset_1(k2_mcart_1(sK6),sK4)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) ),
    inference(trivial_inequality_removal,[],[f598])).

fof(f598,plain,
    ( sK6 != sK6
    | sK5 = k2_mcart_1(sK6)
    | ~ m1_subset_1(k2_mcart_1(sK6),sK4)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) ),
    inference(superposition,[],[f108,f594])).

fof(f594,plain,(
    sK6 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))),k2_mcart_1(sK6)) ),
    inference(forward_demodulation,[],[f593,f579])).

fof(f579,plain,(
    k1_mcart_1(k1_mcart_1(sK6)) = k5_mcart_1(sK2,sK3,sK4,sK6) ),
    inference(subsumption_resolution,[],[f578,f61])).

fof(f578,plain,
    ( k1_mcart_1(k1_mcart_1(sK6)) = k5_mcart_1(sK2,sK3,sK4,sK6)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f577,f62])).

fof(f577,plain,
    ( k1_mcart_1(k1_mcart_1(sK6)) = k5_mcart_1(sK2,sK3,sK4,sK6)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f569,f63])).

fof(f569,plain,
    ( k1_mcart_1(k1_mcart_1(sK6)) = k5_mcart_1(sK2,sK3,sK4,sK6)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f115,f109])).

fof(f115,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f97,f75])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f593,plain,(
    sK6 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK6),k2_mcart_1(k1_mcart_1(sK6))),k2_mcart_1(sK6)) ),
    inference(forward_demodulation,[],[f592,f564])).

fof(f564,plain,(
    k2_mcart_1(k1_mcart_1(sK6)) = k6_mcart_1(sK2,sK3,sK4,sK6) ),
    inference(subsumption_resolution,[],[f563,f61])).

fof(f563,plain,
    ( k2_mcart_1(k1_mcart_1(sK6)) = k6_mcart_1(sK2,sK3,sK4,sK6)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f562,f62])).

fof(f562,plain,
    ( k2_mcart_1(k1_mcart_1(sK6)) = k6_mcart_1(sK2,sK3,sK4,sK6)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f554,f63])).

fof(f554,plain,
    ( k2_mcart_1(k1_mcart_1(sK6)) = k6_mcart_1(sK2,sK3,sK4,sK6)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f114,f109])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f98,f75])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f592,plain,(
    sK6 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK6),k6_mcart_1(sK2,sK3,sK4,sK6)),k2_mcart_1(sK6)) ),
    inference(forward_demodulation,[],[f591,f550])).

fof(f591,plain,(
    sK6 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK6),k6_mcart_1(sK2,sK3,sK4,sK6)),k7_mcart_1(sK2,sK3,sK4,sK6)) ),
    inference(subsumption_resolution,[],[f590,f61])).

fof(f590,plain,
    ( sK6 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK6),k6_mcart_1(sK2,sK3,sK4,sK6)),k7_mcart_1(sK2,sK3,sK4,sK6))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f589,f62])).

fof(f589,plain,
    ( sK6 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK6),k6_mcart_1(sK2,sK3,sK4,sK6)),k7_mcart_1(sK2,sK3,sK4,sK6))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f581,f63])).

fof(f581,plain,
    ( sK6 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK6),k6_mcart_1(sK2,sK3,sK4,sK6)),k7_mcart_1(sK2,sK3,sK4,sK6))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f112,f109])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f96,f74,f75])).

fof(f74,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f108,plain,(
    ! [X6,X7,X5] :
      ( sK6 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK5 = X7
      | ~ m1_subset_1(X7,sK4)
      | ~ m1_subset_1(X6,sK3)
      | ~ m1_subset_1(X5,sK2) ) ),
    inference(definition_unfolding,[],[f60,f74])).

fof(f60,plain,(
    ! [X6,X7,X5] :
      ( sK5 = X7
      | k3_mcart_1(X5,X6,X7) != sK6
      | ~ m1_subset_1(X7,sK4)
      | ~ m1_subset_1(X6,sK3)
      | ~ m1_subset_1(X5,sK2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f458,plain,
    ( spl15_1
    | spl15_2 ),
    inference(avatar_split_clause,[],[f457,f153,f149])).

fof(f457,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
    | r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(resolution,[],[f109,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:41:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (17227)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.50  % (17241)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (17219)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (17216)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (17231)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.51  % (17216)Refutation not found, incomplete strategy% (17216)------------------------------
% 0.20/0.51  % (17216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (17216)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (17216)Memory used [KB]: 1663
% 0.20/0.51  % (17216)Time elapsed: 0.106 s
% 0.20/0.51  % (17216)------------------------------
% 0.20/0.51  % (17216)------------------------------
% 0.20/0.51  % (17227)Refutation not found, incomplete strategy% (17227)------------------------------
% 0.20/0.51  % (17227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (17227)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (17227)Memory used [KB]: 10618
% 0.20/0.51  % (17227)Time elapsed: 0.102 s
% 0.20/0.51  % (17227)------------------------------
% 0.20/0.51  % (17227)------------------------------
% 0.20/0.51  % (17237)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (17222)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  % (17228)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.51  % (17233)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.51  % (17224)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (17235)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.52  % (17223)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.52  % (17217)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (17231)Refutation not found, incomplete strategy% (17231)------------------------------
% 0.20/0.52  % (17231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (17231)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (17231)Memory used [KB]: 10746
% 0.20/0.52  % (17231)Time elapsed: 0.118 s
% 0.20/0.52  % (17231)------------------------------
% 0.20/0.52  % (17231)------------------------------
% 0.20/0.52  % (17238)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.52  % (17229)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (17215)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (17229)Refutation not found, incomplete strategy% (17229)------------------------------
% 0.20/0.52  % (17229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (17229)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (17229)Memory used [KB]: 1791
% 0.20/0.52  % (17229)Time elapsed: 0.085 s
% 0.20/0.52  % (17229)------------------------------
% 0.20/0.52  % (17229)------------------------------
% 0.20/0.52  % (17241)Refutation not found, incomplete strategy% (17241)------------------------------
% 0.20/0.52  % (17241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (17241)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (17241)Memory used [KB]: 6268
% 0.20/0.52  % (17241)Time elapsed: 0.115 s
% 0.20/0.52  % (17241)------------------------------
% 0.20/0.52  % (17241)------------------------------
% 0.20/0.52  % (17226)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.52  % (17233)Refutation not found, incomplete strategy% (17233)------------------------------
% 0.20/0.52  % (17233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (17233)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (17233)Memory used [KB]: 1791
% 0.20/0.52  % (17233)Time elapsed: 0.115 s
% 0.20/0.52  % (17233)------------------------------
% 0.20/0.52  % (17233)------------------------------
% 0.20/0.52  % (17218)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (17230)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (17243)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (17234)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.53  % (17220)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (17239)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.53  % (17221)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (17240)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.54  % (17239)Refutation not found, incomplete strategy% (17239)------------------------------
% 0.20/0.54  % (17239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (17239)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (17239)Memory used [KB]: 10874
% 0.20/0.54  % (17239)Time elapsed: 0.132 s
% 0.20/0.54  % (17239)------------------------------
% 0.20/0.54  % (17239)------------------------------
% 0.20/0.54  % (17232)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.54  % (17225)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.54  % (17244)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (17244)Refutation not found, incomplete strategy% (17244)------------------------------
% 0.20/0.54  % (17244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (17244)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (17244)Memory used [KB]: 1663
% 0.20/0.54  % (17244)Time elapsed: 0.003 s
% 0.20/0.54  % (17244)------------------------------
% 0.20/0.54  % (17244)------------------------------
% 0.20/0.55  % (17236)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.46/0.55  % (17242)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.46/0.55  % (17242)Refutation not found, incomplete strategy% (17242)------------------------------
% 1.46/0.55  % (17242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (17242)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (17242)Memory used [KB]: 6396
% 1.46/0.55  % (17242)Time elapsed: 0.129 s
% 1.46/0.55  % (17242)------------------------------
% 1.46/0.55  % (17242)------------------------------
% 1.64/0.58  % (17221)Refutation found. Thanks to Tanya!
% 1.64/0.58  % SZS status Theorem for theBenchmark
% 1.64/0.58  % SZS output start Proof for theBenchmark
% 1.64/0.58  fof(f840,plain,(
% 1.64/0.58    $false),
% 1.64/0.58    inference(avatar_sat_refutation,[],[f458,f606,f633,f649,f725,f833])).
% 1.64/0.58  fof(f833,plain,(
% 1.64/0.58    ~spl15_13),
% 1.64/0.58    inference(avatar_contradiction_clause,[],[f832])).
% 1.64/0.58  fof(f832,plain,(
% 1.64/0.58    $false | ~spl15_13),
% 1.64/0.58    inference(subsumption_resolution,[],[f767,f724])).
% 1.64/0.58  fof(f724,plain,(
% 1.64/0.58    ( ! [X12] : (k1_xboole_0 = X12) ) | ~spl15_13),
% 1.64/0.58    inference(avatar_component_clause,[],[f723])).
% 1.64/0.58  fof(f723,plain,(
% 1.64/0.58    spl15_13 <=> ! [X12] : k1_xboole_0 = X12),
% 1.64/0.58    introduced(avatar_definition,[new_symbols(naming,[spl15_13])])).
% 1.64/0.58  fof(f767,plain,(
% 1.64/0.58    k1_xboole_0 != sK5 | ~spl15_13),
% 1.64/0.58    inference(backward_demodulation,[],[f568,f724])).
% 1.64/0.58  fof(f568,plain,(
% 1.64/0.58    sK5 != k2_mcart_1(sK6)),
% 1.64/0.58    inference(superposition,[],[f64,f550])).
% 1.64/0.58  fof(f550,plain,(
% 1.64/0.58    k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6)),
% 1.64/0.58    inference(subsumption_resolution,[],[f549,f61])).
% 1.64/0.58  fof(f61,plain,(
% 1.64/0.58    k1_xboole_0 != sK2),
% 1.64/0.58    inference(cnf_transformation,[],[f37])).
% 1.64/0.58  fof(f37,plain,(
% 1.64/0.58    sK5 != k7_mcart_1(sK2,sK3,sK4,sK6) & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & ! [X5] : (! [X6] : (! [X7] : (sK5 = X7 | k3_mcart_1(X5,X6,X7) != sK6 | ~m1_subset_1(X7,sK4)) | ~m1_subset_1(X6,sK3)) | ~m1_subset_1(X5,sK2)) & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4))),
% 1.64/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f21,f36])).
% 1.64/0.58  fof(f36,plain,(
% 1.64/0.58    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK5 != k7_mcart_1(sK2,sK3,sK4,sK6) & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & ! [X5] : (! [X6] : (! [X7] : (sK5 = X7 | k3_mcart_1(X5,X6,X7) != sK6 | ~m1_subset_1(X7,sK4)) | ~m1_subset_1(X6,sK3)) | ~m1_subset_1(X5,sK2)) & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)))),
% 1.64/0.58    introduced(choice_axiom,[])).
% 1.64/0.58  fof(f21,plain,(
% 1.64/0.58    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.64/0.58    inference(flattening,[],[f20])).
% 1.64/0.58  fof(f20,plain,(
% 1.64/0.58    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.64/0.58    inference(ennf_transformation,[],[f19])).
% 1.64/0.58  fof(f19,negated_conjecture,(
% 1.64/0.58    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.64/0.58    inference(negated_conjecture,[],[f18])).
% 1.64/0.58  fof(f18,conjecture,(
% 1.64/0.58    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).
% 1.64/0.58  fof(f549,plain,(
% 1.64/0.58    k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6) | k1_xboole_0 = sK2),
% 1.64/0.58    inference(subsumption_resolution,[],[f548,f62])).
% 1.64/0.58  fof(f62,plain,(
% 1.64/0.58    k1_xboole_0 != sK3),
% 1.64/0.58    inference(cnf_transformation,[],[f37])).
% 1.64/0.58  fof(f548,plain,(
% 1.64/0.58    k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 1.64/0.58    inference(subsumption_resolution,[],[f540,f63])).
% 1.64/0.58  fof(f63,plain,(
% 1.64/0.58    k1_xboole_0 != sK4),
% 1.64/0.58    inference(cnf_transformation,[],[f37])).
% 1.64/0.58  fof(f540,plain,(
% 1.64/0.58    k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 1.64/0.58    inference(resolution,[],[f113,f109])).
% 1.64/0.58  fof(f109,plain,(
% 1.64/0.58    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 1.64/0.58    inference(definition_unfolding,[],[f59,f75])).
% 1.64/0.58  fof(f75,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f10])).
% 1.64/0.58  fof(f10,axiom,(
% 1.64/0.58    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.64/0.58  fof(f59,plain,(
% 1.64/0.58    m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4))),
% 1.64/0.58    inference(cnf_transformation,[],[f37])).
% 1.64/0.58  fof(f113,plain,(
% 1.64/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.64/0.58    inference(definition_unfolding,[],[f99,f75])).
% 1.64/0.58  fof(f99,plain,(
% 1.64/0.58    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.64/0.58    inference(cnf_transformation,[],[f30])).
% 1.64/0.58  fof(f30,plain,(
% 1.64/0.58    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.64/0.58    inference(ennf_transformation,[],[f15])).
% 1.64/0.58  fof(f15,axiom,(
% 1.64/0.58    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 1.64/0.58  fof(f64,plain,(
% 1.64/0.58    sK5 != k7_mcart_1(sK2,sK3,sK4,sK6)),
% 1.64/0.58    inference(cnf_transformation,[],[f37])).
% 1.64/0.58  fof(f725,plain,(
% 1.64/0.58    spl15_13 | spl15_13 | ~spl15_5),
% 1.64/0.58    inference(avatar_split_clause,[],[f721,f429,f723,f723])).
% 1.64/0.58  fof(f429,plain,(
% 1.64/0.58    spl15_5 <=> ! [X8] : ~r2_hidden(X8,k2_zfmisc_1(sK2,sK3))),
% 1.64/0.58    introduced(avatar_definition,[new_symbols(naming,[spl15_5])])).
% 1.64/0.58  fof(f721,plain,(
% 1.64/0.58    ( ! [X12,X13] : (k1_xboole_0 = X13 | k1_xboole_0 = X12) ) | ~spl15_5),
% 1.64/0.58    inference(subsumption_resolution,[],[f720,f348])).
% 1.64/0.58  fof(f348,plain,(
% 1.64/0.58    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3)) )),
% 1.64/0.58    inference(backward_demodulation,[],[f128,f338])).
% 1.64/0.58  fof(f338,plain,(
% 1.64/0.58    ( ! [X5] : (k1_xboole_0 = k2_zfmisc_1(X5,k1_xboole_0)) )),
% 1.64/0.58    inference(resolution,[],[f327,f138])).
% 1.64/0.58  fof(f138,plain,(
% 1.64/0.58    ( ! [X1] : (~v1_xboole_0(X1) | k1_xboole_0 = X1) )),
% 1.64/0.58    inference(resolution,[],[f68,f66])).
% 1.64/0.58  fof(f66,plain,(
% 1.64/0.58    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f41])).
% 1.64/0.58  fof(f41,plain,(
% 1.64/0.58    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK7(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.64/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f39,f40])).
% 1.64/0.58  fof(f40,plain,(
% 1.64/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK7(X0),X0))),
% 1.64/0.58    introduced(choice_axiom,[])).
% 1.64/0.58  fof(f39,plain,(
% 1.64/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.64/0.58    inference(rectify,[],[f38])).
% 1.64/0.58  fof(f38,plain,(
% 1.64/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.64/0.58    inference(nnf_transformation,[],[f1])).
% 1.64/0.58  fof(f1,axiom,(
% 1.64/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.64/0.58  fof(f68,plain,(
% 1.64/0.58    ( ! [X0] : (r2_hidden(sK8(X0),X0) | k1_xboole_0 = X0) )),
% 1.64/0.58    inference(cnf_transformation,[],[f43])).
% 1.64/0.58  fof(f43,plain,(
% 1.64/0.58    ! [X0] : ((! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,sK8(X0)) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(sK8(X0),X0)) | k1_xboole_0 = X0)),
% 1.64/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f23,f42])).
% 1.64/0.58  fof(f42,plain,(
% 1.64/0.58    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) => (! [X6,X5,X4,X3,X2] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,sK8(X0)) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(sK8(X0),X0)))),
% 1.64/0.58    introduced(choice_axiom,[])).
% 1.64/0.58  fof(f23,plain,(
% 1.64/0.58    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.64/0.58    inference(flattening,[],[f22])).
% 1.64/0.58  fof(f22,plain,(
% 1.64/0.58    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | (~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.64/0.58    inference(ennf_transformation,[],[f17])).
% 1.64/0.58  fof(f17,axiom,(
% 1.64/0.58    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).
% 1.64/0.58  fof(f327,plain,(
% 1.64/0.58    ( ! [X4] : (v1_xboole_0(k2_zfmisc_1(X4,k1_xboole_0))) )),
% 1.64/0.58    inference(resolution,[],[f168,f135])).
% 1.64/0.58  fof(f135,plain,(
% 1.64/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.64/0.58    inference(resolution,[],[f73,f65])).
% 1.64/0.58  fof(f65,plain,(
% 1.64/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f2])).
% 1.64/0.58  fof(f2,axiom,(
% 1.64/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.64/0.58  fof(f73,plain,(
% 1.64/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f27])).
% 1.64/0.58  fof(f27,plain,(
% 1.64/0.58    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.64/0.58    inference(ennf_transformation,[],[f8])).
% 1.64/0.58  fof(f8,axiom,(
% 1.64/0.58    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.64/0.58  fof(f168,plain,(
% 1.64/0.58    ( ! [X0,X1] : (r2_hidden(k2_mcart_1(sK7(k2_zfmisc_1(X0,X1))),X1) | v1_xboole_0(k2_zfmisc_1(X0,X1))) )),
% 1.64/0.58    inference(resolution,[],[f77,f67])).
% 1.64/0.58  fof(f67,plain,(
% 1.64/0.58    ( ! [X0] : (r2_hidden(sK7(X0),X0) | v1_xboole_0(X0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f41])).
% 1.64/0.58  fof(f77,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f28])).
% 1.64/0.58  fof(f28,plain,(
% 1.64/0.58    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.64/0.58    inference(ennf_transformation,[],[f13])).
% 1.64/0.58  fof(f13,axiom,(
% 1.64/0.58    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.64/0.58  fof(f128,plain,(
% 1.64/0.58    ( ! [X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3)) )),
% 1.64/0.58    inference(equality_resolution,[],[f118])).
% 1.64/0.58  fof(f118,plain,(
% 1.64/0.58    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.64/0.58    inference(definition_unfolding,[],[f105,f107])).
% 1.64/0.58  fof(f107,plain,(
% 1.64/0.58    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.64/0.58    inference(definition_unfolding,[],[f100,f75])).
% 1.64/0.58  fof(f100,plain,(
% 1.64/0.58    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f11])).
% 1.64/0.58  fof(f11,axiom,(
% 1.64/0.58    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.64/0.58  fof(f105,plain,(
% 1.64/0.58    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f58])).
% 1.64/0.58  fof(f58,plain,(
% 1.64/0.58    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.64/0.58    inference(flattening,[],[f57])).
% 1.64/0.58  fof(f57,plain,(
% 1.64/0.58    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.64/0.58    inference(nnf_transformation,[],[f16])).
% 1.64/0.58  fof(f16,axiom,(
% 1.64/0.58    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).
% 1.64/0.58  fof(f720,plain,(
% 1.64/0.58    ( ! [X12,X13] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X13) | k1_xboole_0 = X13 | k1_xboole_0 = X12) ) | ~spl15_5),
% 1.64/0.58    inference(forward_demodulation,[],[f719,f348])).
% 1.64/0.58  fof(f719,plain,(
% 1.64/0.58    ( ! [X12,X13] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12),X13) | k1_xboole_0 = X13 | k1_xboole_0 = X12) ) | ~spl15_5),
% 1.64/0.58    inference(subsumption_resolution,[],[f718,f61])).
% 1.64/0.58  fof(f718,plain,(
% 1.64/0.58    ( ! [X12,X13] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12),X13) | k1_xboole_0 = X13 | k1_xboole_0 = X12 | k1_xboole_0 = sK2) ) | ~spl15_5),
% 1.64/0.58    inference(subsumption_resolution,[],[f694,f62])).
% 1.64/0.58  fof(f694,plain,(
% 1.64/0.58    ( ! [X12,X13] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12),X13) | k1_xboole_0 = X13 | k1_xboole_0 = X12 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2) ) | ~spl15_5),
% 1.64/0.58    inference(superposition,[],[f121,f662])).
% 1.64/0.58  fof(f662,plain,(
% 1.64/0.58    k1_xboole_0 = k2_zfmisc_1(sK2,sK3) | ~spl15_5),
% 1.64/0.58    inference(resolution,[],[f430,f68])).
% 1.64/0.58  fof(f430,plain,(
% 1.64/0.58    ( ! [X8] : (~r2_hidden(X8,k2_zfmisc_1(sK2,sK3))) ) | ~spl15_5),
% 1.64/0.58    inference(avatar_component_clause,[],[f429])).
% 1.64/0.58  fof(f121,plain,(
% 1.64/0.58    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.64/0.58    inference(definition_unfolding,[],[f102,f107])).
% 1.64/0.58  fof(f102,plain,(
% 1.64/0.58    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.64/0.58    inference(cnf_transformation,[],[f58])).
% 1.64/0.58  fof(f649,plain,(
% 1.64/0.58    ~spl15_6),
% 1.64/0.58    inference(avatar_contradiction_clause,[],[f648])).
% 1.64/0.58  fof(f648,plain,(
% 1.64/0.58    $false | ~spl15_6),
% 1.64/0.58    inference(subsumption_resolution,[],[f638,f63])).
% 1.64/0.58  fof(f638,plain,(
% 1.64/0.58    k1_xboole_0 = sK4 | ~spl15_6),
% 1.64/0.58    inference(resolution,[],[f433,f68])).
% 1.64/0.58  fof(f433,plain,(
% 1.64/0.58    ( ! [X7] : (~r2_hidden(X7,sK4)) ) | ~spl15_6),
% 1.64/0.58    inference(avatar_component_clause,[],[f432])).
% 1.64/0.58  fof(f432,plain,(
% 1.64/0.58    spl15_6 <=> ! [X7] : ~r2_hidden(X7,sK4)),
% 1.64/0.58    introduced(avatar_definition,[new_symbols(naming,[spl15_6])])).
% 1.64/0.58  fof(f633,plain,(
% 1.64/0.58    spl15_5 | spl15_6 | ~spl15_2),
% 1.64/0.58    inference(avatar_split_clause,[],[f427,f153,f432,f429])).
% 1.64/0.58  fof(f153,plain,(
% 1.64/0.58    spl15_2 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 1.64/0.58    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).
% 1.64/0.58  fof(f427,plain,(
% 1.64/0.58    ( ! [X8,X7] : (~r2_hidden(X7,sK4) | ~r2_hidden(X8,k2_zfmisc_1(sK2,sK3))) ) | ~spl15_2),
% 1.64/0.58    inference(subsumption_resolution,[],[f423,f135])).
% 1.64/0.58  fof(f423,plain,(
% 1.64/0.58    ( ! [X8,X7] : (~r2_hidden(X7,sK4) | ~r2_hidden(X8,k2_zfmisc_1(sK2,sK3)) | r2_hidden(k4_tarski(X8,X7),k1_xboole_0)) ) | ~spl15_2),
% 1.64/0.58    inference(resolution,[],[f125,f160])).
% 1.64/0.58  fof(f160,plain,(
% 1.64/0.58    sP1(sK4,k2_zfmisc_1(sK2,sK3),k1_xboole_0) | ~spl15_2),
% 1.64/0.58    inference(superposition,[],[f126,f157])).
% 1.64/0.58  fof(f157,plain,(
% 1.64/0.58    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) | ~spl15_2),
% 1.64/0.58    inference(resolution,[],[f155,f138])).
% 1.64/0.58  fof(f155,plain,(
% 1.64/0.58    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) | ~spl15_2),
% 1.64/0.58    inference(avatar_component_clause,[],[f153])).
% 1.64/0.58  fof(f126,plain,(
% 1.64/0.58    ( ! [X0,X1] : (sP1(X1,X0,k2_zfmisc_1(X0,X1))) )),
% 1.64/0.58    inference(equality_resolution,[],[f94])).
% 1.64/0.58  fof(f94,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.64/0.58    inference(cnf_transformation,[],[f56])).
% 1.64/0.58  fof(f56,plain,(
% 1.64/0.58    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | k2_zfmisc_1(X0,X1) != X2))),
% 1.64/0.58    inference(nnf_transformation,[],[f35])).
% 1.64/0.58  fof(f35,plain,(
% 1.64/0.58    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> sP1(X1,X0,X2))),
% 1.64/0.58    inference(definition_folding,[],[f5,f34])).
% 1.64/0.58  fof(f34,plain,(
% 1.64/0.58    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.64/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.64/0.58  fof(f5,axiom,(
% 1.64/0.58    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.64/0.58  fof(f125,plain,(
% 1.64/0.58    ( ! [X2,X0,X10,X1,X9] : (~sP1(X0,X1,X2) | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1) | r2_hidden(k4_tarski(X9,X10),X2)) )),
% 1.64/0.58    inference(equality_resolution,[],[f89])).
% 1.64/0.58  fof(f89,plain,(
% 1.64/0.58    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1) | ~sP1(X0,X1,X2)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f55])).
% 1.64/0.58  fof(f55,plain,(
% 1.64/0.58    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((! [X4,X5] : (k4_tarski(X4,X5) != sK10(X0,X1,X2) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(sK10(X0,X1,X2),X2)) & ((sK10(X0,X1,X2) = k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)) & r2_hidden(sK12(X0,X1,X2),X0) & r2_hidden(sK11(X0,X1,X2),X1)) | r2_hidden(sK10(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1))) & ((k4_tarski(sK13(X0,X1,X8),sK14(X0,X1,X8)) = X8 & r2_hidden(sK14(X0,X1,X8),X0) & r2_hidden(sK13(X0,X1,X8),X1)) | ~r2_hidden(X8,X2))) | ~sP1(X0,X1,X2)))),
% 1.64/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12,sK13,sK14])],[f51,f54,f53,f52])).
% 1.64/0.58  fof(f52,plain,(
% 1.64/0.58    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK10(X0,X1,X2) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK10(X0,X1,X2) & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(sK10(X0,X1,X2),X2))))),
% 1.64/0.58    introduced(choice_axiom,[])).
% 1.64/0.58  fof(f53,plain,(
% 1.64/0.58    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK10(X0,X1,X2) & r2_hidden(X7,X0) & r2_hidden(X6,X1)) => (sK10(X0,X1,X2) = k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)) & r2_hidden(sK12(X0,X1,X2),X0) & r2_hidden(sK11(X0,X1,X2),X1)))),
% 1.64/0.58    introduced(choice_axiom,[])).
% 1.64/0.58  fof(f54,plain,(
% 1.64/0.58    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X0) & r2_hidden(X11,X1)) => (k4_tarski(sK13(X0,X1,X8),sK14(X0,X1,X8)) = X8 & r2_hidden(sK14(X0,X1,X8),X0) & r2_hidden(sK13(X0,X1,X8),X1)))),
% 1.64/0.58    introduced(choice_axiom,[])).
% 1.64/0.58  fof(f51,plain,(
% 1.64/0.58    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X0) & r2_hidden(X11,X1)) | ~r2_hidden(X8,X2))) | ~sP1(X0,X1,X2)))),
% 1.64/0.58    inference(rectify,[],[f50])).
% 1.64/0.58  fof(f50,plain,(
% 1.64/0.58    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 1.64/0.58    inference(nnf_transformation,[],[f34])).
% 1.64/0.58  fof(f606,plain,(
% 1.64/0.58    ~spl15_1),
% 1.64/0.58    inference(avatar_contradiction_clause,[],[f605])).
% 1.64/0.58  fof(f605,plain,(
% 1.64/0.58    $false | ~spl15_1),
% 1.64/0.58    inference(subsumption_resolution,[],[f604,f531])).
% 1.64/0.58  fof(f531,plain,(
% 1.64/0.58    m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) | ~spl15_1),
% 1.64/0.58    inference(resolution,[],[f520,f72])).
% 1.64/0.58  fof(f72,plain,(
% 1.64/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f26])).
% 1.64/0.58  fof(f26,plain,(
% 1.64/0.58    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.64/0.58    inference(ennf_transformation,[],[f6])).
% 1.64/0.58  fof(f6,axiom,(
% 1.64/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.64/0.58  fof(f520,plain,(
% 1.64/0.58    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK2) | ~spl15_1),
% 1.64/0.58    inference(resolution,[],[f507,f76])).
% 1.64/0.58  fof(f76,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f28])).
% 1.64/0.58  fof(f507,plain,(
% 1.64/0.58    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK2,sK3)) | ~spl15_1),
% 1.64/0.58    inference(resolution,[],[f151,f76])).
% 1.64/0.58  fof(f151,plain,(
% 1.64/0.58    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) | ~spl15_1),
% 1.64/0.58    inference(avatar_component_clause,[],[f149])).
% 1.64/0.58  fof(f149,plain,(
% 1.64/0.58    spl15_1 <=> r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 1.64/0.58    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).
% 1.64/0.58  fof(f604,plain,(
% 1.64/0.58    ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) | ~spl15_1),
% 1.64/0.58    inference(subsumption_resolution,[],[f603,f523])).
% 1.64/0.58  fof(f523,plain,(
% 1.64/0.58    m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) | ~spl15_1),
% 1.64/0.58    inference(resolution,[],[f519,f72])).
% 1.64/0.58  fof(f519,plain,(
% 1.64/0.58    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3) | ~spl15_1),
% 1.64/0.58    inference(resolution,[],[f507,f77])).
% 1.64/0.58  fof(f603,plain,(
% 1.64/0.58    ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) | ~spl15_1),
% 1.64/0.58    inference(subsumption_resolution,[],[f602,f510])).
% 1.64/0.58  fof(f510,plain,(
% 1.64/0.58    m1_subset_1(k2_mcart_1(sK6),sK4) | ~spl15_1),
% 1.64/0.58    inference(resolution,[],[f506,f72])).
% 1.64/0.58  fof(f506,plain,(
% 1.64/0.58    r2_hidden(k2_mcart_1(sK6),sK4) | ~spl15_1),
% 1.64/0.58    inference(resolution,[],[f151,f77])).
% 1.64/0.58  fof(f602,plain,(
% 1.64/0.58    ~m1_subset_1(k2_mcart_1(sK6),sK4) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2)),
% 1.64/0.58    inference(subsumption_resolution,[],[f601,f568])).
% 1.64/0.58  fof(f601,plain,(
% 1.64/0.58    sK5 = k2_mcart_1(sK6) | ~m1_subset_1(k2_mcart_1(sK6),sK4) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2)),
% 1.64/0.58    inference(trivial_inequality_removal,[],[f598])).
% 1.64/0.58  fof(f598,plain,(
% 1.64/0.58    sK6 != sK6 | sK5 = k2_mcart_1(sK6) | ~m1_subset_1(k2_mcart_1(sK6),sK4) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2)),
% 1.64/0.58    inference(superposition,[],[f108,f594])).
% 1.64/0.58  fof(f594,plain,(
% 1.64/0.58    sK6 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))),k2_mcart_1(sK6))),
% 1.64/0.58    inference(forward_demodulation,[],[f593,f579])).
% 1.64/0.58  fof(f579,plain,(
% 1.64/0.58    k1_mcart_1(k1_mcart_1(sK6)) = k5_mcart_1(sK2,sK3,sK4,sK6)),
% 1.64/0.58    inference(subsumption_resolution,[],[f578,f61])).
% 1.64/0.58  fof(f578,plain,(
% 1.64/0.58    k1_mcart_1(k1_mcart_1(sK6)) = k5_mcart_1(sK2,sK3,sK4,sK6) | k1_xboole_0 = sK2),
% 1.64/0.58    inference(subsumption_resolution,[],[f577,f62])).
% 1.64/0.58  fof(f577,plain,(
% 1.64/0.58    k1_mcart_1(k1_mcart_1(sK6)) = k5_mcart_1(sK2,sK3,sK4,sK6) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 1.64/0.58    inference(subsumption_resolution,[],[f569,f63])).
% 1.64/0.58  fof(f569,plain,(
% 1.64/0.58    k1_mcart_1(k1_mcart_1(sK6)) = k5_mcart_1(sK2,sK3,sK4,sK6) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 1.64/0.58    inference(resolution,[],[f115,f109])).
% 1.64/0.58  fof(f115,plain,(
% 1.64/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.64/0.58    inference(definition_unfolding,[],[f97,f75])).
% 1.64/0.58  fof(f97,plain,(
% 1.64/0.58    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.64/0.58    inference(cnf_transformation,[],[f30])).
% 1.64/0.58  fof(f593,plain,(
% 1.64/0.58    sK6 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK6),k2_mcart_1(k1_mcart_1(sK6))),k2_mcart_1(sK6))),
% 1.64/0.58    inference(forward_demodulation,[],[f592,f564])).
% 1.64/0.58  fof(f564,plain,(
% 1.64/0.58    k2_mcart_1(k1_mcart_1(sK6)) = k6_mcart_1(sK2,sK3,sK4,sK6)),
% 1.64/0.58    inference(subsumption_resolution,[],[f563,f61])).
% 1.64/0.58  fof(f563,plain,(
% 1.64/0.58    k2_mcart_1(k1_mcart_1(sK6)) = k6_mcart_1(sK2,sK3,sK4,sK6) | k1_xboole_0 = sK2),
% 1.64/0.58    inference(subsumption_resolution,[],[f562,f62])).
% 1.64/0.58  fof(f562,plain,(
% 1.64/0.58    k2_mcart_1(k1_mcart_1(sK6)) = k6_mcart_1(sK2,sK3,sK4,sK6) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 1.64/0.58    inference(subsumption_resolution,[],[f554,f63])).
% 1.64/0.58  fof(f554,plain,(
% 1.64/0.58    k2_mcart_1(k1_mcart_1(sK6)) = k6_mcart_1(sK2,sK3,sK4,sK6) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 1.64/0.58    inference(resolution,[],[f114,f109])).
% 1.64/0.58  fof(f114,plain,(
% 1.64/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.64/0.58    inference(definition_unfolding,[],[f98,f75])).
% 1.64/0.58  fof(f98,plain,(
% 1.64/0.58    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.64/0.58    inference(cnf_transformation,[],[f30])).
% 1.64/0.58  fof(f592,plain,(
% 1.64/0.58    sK6 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK6),k6_mcart_1(sK2,sK3,sK4,sK6)),k2_mcart_1(sK6))),
% 1.64/0.58    inference(forward_demodulation,[],[f591,f550])).
% 1.64/0.58  fof(f591,plain,(
% 1.64/0.58    sK6 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK6),k6_mcart_1(sK2,sK3,sK4,sK6)),k7_mcart_1(sK2,sK3,sK4,sK6))),
% 1.64/0.58    inference(subsumption_resolution,[],[f590,f61])).
% 1.64/0.58  fof(f590,plain,(
% 1.64/0.58    sK6 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK6),k6_mcart_1(sK2,sK3,sK4,sK6)),k7_mcart_1(sK2,sK3,sK4,sK6)) | k1_xboole_0 = sK2),
% 1.64/0.58    inference(subsumption_resolution,[],[f589,f62])).
% 1.64/0.58  fof(f589,plain,(
% 1.64/0.58    sK6 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK6),k6_mcart_1(sK2,sK3,sK4,sK6)),k7_mcart_1(sK2,sK3,sK4,sK6)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 1.64/0.58    inference(subsumption_resolution,[],[f581,f63])).
% 1.64/0.58  fof(f581,plain,(
% 1.64/0.58    sK6 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK6),k6_mcart_1(sK2,sK3,sK4,sK6)),k7_mcart_1(sK2,sK3,sK4,sK6)) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 1.64/0.58    inference(resolution,[],[f112,f109])).
% 1.64/0.58  fof(f112,plain,(
% 1.64/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.64/0.58    inference(definition_unfolding,[],[f96,f74,f75])).
% 1.64/0.58  fof(f74,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f9])).
% 1.64/0.58  fof(f9,axiom,(
% 1.64/0.58    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.64/0.58  fof(f96,plain,(
% 1.64/0.58    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.64/0.58    inference(cnf_transformation,[],[f29])).
% 1.64/0.58  fof(f29,plain,(
% 1.64/0.58    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.64/0.58    inference(ennf_transformation,[],[f14])).
% 1.64/0.58  fof(f14,axiom,(
% 1.64/0.58    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).
% 1.64/0.58  fof(f108,plain,(
% 1.64/0.58    ( ! [X6,X7,X5] : (sK6 != k4_tarski(k4_tarski(X5,X6),X7) | sK5 = X7 | ~m1_subset_1(X7,sK4) | ~m1_subset_1(X6,sK3) | ~m1_subset_1(X5,sK2)) )),
% 1.64/0.58    inference(definition_unfolding,[],[f60,f74])).
% 1.64/0.58  fof(f60,plain,(
% 1.64/0.58    ( ! [X6,X7,X5] : (sK5 = X7 | k3_mcart_1(X5,X6,X7) != sK6 | ~m1_subset_1(X7,sK4) | ~m1_subset_1(X6,sK3) | ~m1_subset_1(X5,sK2)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f37])).
% 1.64/0.58  fof(f458,plain,(
% 1.64/0.58    spl15_1 | spl15_2),
% 1.64/0.58    inference(avatar_split_clause,[],[f457,f153,f149])).
% 1.64/0.58  fof(f457,plain,(
% 1.64/0.58    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) | r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 1.64/0.58    inference(resolution,[],[f109,f71])).
% 1.64/0.58  fof(f71,plain,(
% 1.64/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f25])).
% 1.64/0.58  fof(f25,plain,(
% 1.64/0.58    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.64/0.58    inference(flattening,[],[f24])).
% 1.64/0.58  fof(f24,plain,(
% 1.64/0.58    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.64/0.58    inference(ennf_transformation,[],[f7])).
% 1.64/0.58  fof(f7,axiom,(
% 1.64/0.58    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.64/0.58  % SZS output end Proof for theBenchmark
% 1.64/0.58  % (17221)------------------------------
% 1.64/0.58  % (17221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.58  % (17221)Termination reason: Refutation
% 1.64/0.58  
% 1.64/0.58  % (17221)Memory used [KB]: 11129
% 1.64/0.58  % (17221)Time elapsed: 0.152 s
% 1.64/0.58  % (17221)------------------------------
% 1.64/0.58  % (17221)------------------------------
% 1.64/0.59  % (17214)Success in time 0.226 s
%------------------------------------------------------------------------------
