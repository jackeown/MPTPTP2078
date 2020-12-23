%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:45 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 613 expanded)
%              Number of leaves         :   24 ( 167 expanded)
%              Depth                    :   20
%              Number of atoms          :  742 (4577 expanded)
%              Number of equality atoms :  399 (2695 expanded)
%              Maximal formula depth    :   29 (   8 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f503,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f279,f291,f303,f311,f319,f344,f395,f488])).

fof(f488,plain,(
    ~ spl6_11 ),
    inference(avatar_contradiction_clause,[],[f487])).

fof(f487,plain,
    ( $false
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f486,f37])).

fof(f37,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5)
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X6] :
        ( ! [X7] :
            ( ! [X8] :
                ( ! [X9] :
                    ( sK4 = X8
                    | k4_mcart_1(X6,X7,X8,X9) != sK5
                    | ~ m1_subset_1(X9,sK3) )
                | ~ m1_subset_1(X8,sK2) )
            | ~ m1_subset_1(X7,sK1) )
        | ~ m1_subset_1(X6,sK0) )
    & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f19,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( k10_mcart_1(X0,X1,X2,X3,X5) != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X6] :
            ( ! [X7] :
                ( ! [X8] :
                    ( ! [X9] :
                        ( X4 = X8
                        | k4_mcart_1(X6,X7,X8,X9) != X5
                        | ~ m1_subset_1(X9,X3) )
                    | ~ m1_subset_1(X8,X2) )
                | ~ m1_subset_1(X7,X1) )
            | ~ m1_subset_1(X6,X0) )
        & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) )
   => ( sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5)
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( sK4 = X8
                      | k4_mcart_1(X6,X7,X8,X9) != sK5
                      | ~ m1_subset_1(X9,sK3) )
                  | ~ m1_subset_1(X8,sK2) )
              | ~ m1_subset_1(X7,sK1) )
          | ~ m1_subset_1(X6,sK0) )
      & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X8
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X8
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
       => ( ! [X6] :
              ( m1_subset_1(X6,X0)
             => ! [X7] :
                  ( m1_subset_1(X7,X1)
                 => ! [X8] :
                      ( m1_subset_1(X8,X2)
                     => ! [X9] :
                          ( m1_subset_1(X9,X3)
                         => ( k4_mcart_1(X6,X7,X8,X9) = X5
                           => X4 = X8 ) ) ) ) )
         => ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
            | k1_xboole_0 = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X0)
           => ! [X7] :
                ( m1_subset_1(X7,X1)
               => ! [X8] :
                    ( m1_subset_1(X8,X2)
                   => ! [X9] :
                        ( m1_subset_1(X9,X3)
                       => ( k4_mcart_1(X6,X7,X8,X9) = X5
                         => X4 = X8 ) ) ) ) )
       => ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_mcart_1)).

fof(f486,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f485,f38])).

fof(f38,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f32])).

fof(f485,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f484,f39])).

fof(f39,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f484,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f476,f40])).

fof(f40,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f32])).

fof(f476,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_11 ),
    inference(trivial_inequality_removal,[],[f467])).

fof(f467,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_11 ),
    inference(superposition,[],[f73,f457])).

fof(f457,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | ~ spl6_11 ),
    inference(resolution,[],[f442,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f442,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | ~ spl6_11 ),
    inference(resolution,[],[f423,f68])).

fof(f68,plain,(
    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    inference(definition_unfolding,[],[f35,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f51,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f35,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f423,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
        | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )
    | ~ spl6_11 ),
    inference(resolution,[],[f414,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f414,plain,
    ( ! [X2,X0,X3,X1] : ~ r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
    | ~ spl6_11 ),
    inference(resolution,[],[f404,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f404,plain,
    ( ! [X2,X0,X1] : ~ r2_hidden(k1_mcart_1(sK5),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
    | ~ spl6_11 ),
    inference(resolution,[],[f278,f48])).

fof(f278,plain,
    ( ! [X6,X7] : ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK5)),k2_zfmisc_1(X6,X7))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl6_11
  <=> ! [X7,X6] : ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK5)),k2_zfmisc_1(X6,X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f52,f66])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f395,plain,(
    ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f394])).

fof(f394,plain,
    ( $false
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f393,f37])).

fof(f393,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f392,f38])).

fof(f392,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f391,f39])).

fof(f391,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f386,f40])).

fof(f386,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_10 ),
    inference(trivial_inequality_removal,[],[f379])).

fof(f379,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_10 ),
    inference(superposition,[],[f73,f373])).

fof(f373,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | ~ spl6_10 ),
    inference(resolution,[],[f365,f42])).

fof(f365,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | ~ spl6_10 ),
    inference(resolution,[],[f357,f68])).

fof(f357,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
        | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )
    | ~ spl6_10 ),
    inference(resolution,[],[f350,f45])).

fof(f350,plain,
    ( ! [X2,X0,X1] : ~ r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
    | ~ spl6_10 ),
    inference(resolution,[],[f275,f48])).

fof(f275,plain,
    ( ! [X8,X9] : ~ r2_hidden(k1_mcart_1(sK5),k2_zfmisc_1(X8,X9))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl6_10
  <=> ! [X9,X8] : ~ r2_hidden(k1_mcart_1(sK5),k2_zfmisc_1(X8,X9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f344,plain,(
    ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f343])).

fof(f343,plain,
    ( $false
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f342,f37])).

fof(f342,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f341,f38])).

fof(f341,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f340,f39])).

fof(f340,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f335,f40])).

fof(f335,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_9 ),
    inference(trivial_inequality_removal,[],[f330])).

fof(f330,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_9 ),
    inference(superposition,[],[f73,f326])).

fof(f326,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | ~ spl6_9 ),
    inference(resolution,[],[f323,f42])).

fof(f323,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | ~ spl6_9 ),
    inference(resolution,[],[f320,f68])).

fof(f320,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK5,k2_zfmisc_1(X0,X1))
        | v1_xboole_0(k2_zfmisc_1(X0,X1)) )
    | ~ spl6_9 ),
    inference(resolution,[],[f272,f45])).

fof(f272,plain,
    ( ! [X10,X11] : ~ r2_hidden(sK5,k2_zfmisc_1(X10,X11))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl6_9
  <=> ! [X11,X10] : ~ r2_hidden(sK5,k2_zfmisc_1(X10,X11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f319,plain,(
    ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f318])).

fof(f318,plain,
    ( $false
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f317,f37])).

fof(f317,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f316,f40])).

fof(f316,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f312,f39])).

fof(f312,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | ~ spl6_8 ),
    inference(resolution,[],[f249,f68])).

fof(f249,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,sK1),X1),X0))
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = X2 )
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl6_8
  <=> ! [X1,X0,X2] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = X1
        | ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,sK1),X1),X0))
        | k1_xboole_0 = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f311,plain,(
    ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f310])).

fof(f310,plain,
    ( $false
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f309,f38])).

fof(f309,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f308,f39])).

fof(f308,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f304,f40])).

fof(f304,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | ~ spl6_5 ),
    inference(resolution,[],[f238,f68])).

fof(f238,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,X3),X4),X5))
        | k1_xboole_0 = X5
        | k1_xboole_0 = X4
        | k1_xboole_0 = X3 )
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f237])).

fof(f237,plain,
    ( spl6_5
  <=> ! [X3,X5,X4] :
        ( ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,X3),X4),X5))
        | k1_xboole_0 = X5
        | k1_xboole_0 = X4
        | k1_xboole_0 = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f303,plain,(
    spl6_7 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | spl6_7 ),
    inference(subsumption_resolution,[],[f301,f37])).

fof(f301,plain,
    ( k1_xboole_0 = sK0
    | spl6_7 ),
    inference(subsumption_resolution,[],[f300,f38])).

fof(f300,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl6_7 ),
    inference(subsumption_resolution,[],[f296,f39])).

fof(f296,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl6_7 ),
    inference(resolution,[],[f293,f68])).

fof(f293,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),sK3))
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | spl6_7 ),
    inference(subsumption_resolution,[],[f292,f40])).

fof(f292,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),sK3))
        | k1_xboole_0 = sK3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | spl6_7 ),
    inference(resolution,[],[f246,f169])).

fof(f169,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_mcart_1(X4),X3)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_mcart_1(X4),X3)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f78,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f60,f66])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
            & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
            & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
            & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
                & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
                & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) ) ),
    inference(definition_unfolding,[],[f61,f66])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_mcart_1)).

fof(f246,plain,
    ( ~ m1_subset_1(k2_mcart_1(sK5),sK3)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl6_7
  <=> m1_subset_1(k2_mcart_1(sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f291,plain,(
    spl6_6 ),
    inference(avatar_contradiction_clause,[],[f290])).

fof(f290,plain,
    ( $false
    | spl6_6 ),
    inference(subsumption_resolution,[],[f289,f37])).

fof(f289,plain,
    ( k1_xboole_0 = sK0
    | spl6_6 ),
    inference(subsumption_resolution,[],[f288,f38])).

fof(f288,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl6_6 ),
    inference(subsumption_resolution,[],[f284,f40])).

fof(f284,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl6_6 ),
    inference(resolution,[],[f282,f68])).

fof(f282,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK2),X2))
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | spl6_6 ),
    inference(subsumption_resolution,[],[f280,f39])).

fof(f280,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK2),X2))
        | k1_xboole_0 = X2
        | k1_xboole_0 = sK2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | spl6_6 ),
    inference(resolution,[],[f242,f174])).

fof(f174,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_mcart_1(k1_mcart_1(X4)),X2)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f173])).

fof(f173,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_mcart_1(k1_mcart_1(X4)),X2)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f81,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f59,f66])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) ) ),
    inference(definition_unfolding,[],[f64,f66])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_mcart_1)).

fof(f242,plain,
    ( ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl6_6
  <=> m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f279,plain,
    ( spl6_9
    | spl6_10
    | spl6_11
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8 ),
    inference(avatar_split_clause,[],[f269,f248,f244,f240,f237,f277,f274,f271])).

fof(f269,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X11,X9] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(k2_mcart_1(sK5),sK3)
      | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2)
      | ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,X3),X4),X5))
      | ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,sK1),X1),X0))
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK5)),k2_zfmisc_1(X6,X7))
      | k1_xboole_0 = X4
      | ~ r2_hidden(k1_mcart_1(sK5),k2_zfmisc_1(X8,X9))
      | k1_xboole_0 = X5
      | ~ r2_hidden(sK5,k2_zfmisc_1(X10,X11))
      | k1_xboole_0 = X3 ) ),
    inference(subsumption_resolution,[],[f268,f179])).

fof(f179,plain,(
    sK4 != k2_mcart_1(k1_mcart_1(sK5)) ),
    inference(subsumption_resolution,[],[f178,f37])).

fof(f178,plain,
    ( sK4 != k2_mcart_1(k1_mcart_1(sK5))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f177,f38])).

fof(f177,plain,
    ( sK4 != k2_mcart_1(k1_mcart_1(sK5))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f176,f39])).

fof(f176,plain,
    ( sK4 != k2_mcart_1(k1_mcart_1(sK5))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f175,f40])).

fof(f175,plain,
    ( sK4 != k2_mcart_1(k1_mcart_1(sK5))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f172,f68])).

fof(f172,plain,
    ( sK4 != k2_mcart_1(k1_mcart_1(sK5))
    | ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f41,f75])).

fof(f41,plain,(
    sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f32])).

fof(f268,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X11,X9] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | sK4 = k2_mcart_1(k1_mcart_1(sK5))
      | ~ m1_subset_1(k2_mcart_1(sK5),sK3)
      | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2)
      | ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,X3),X4),X5))
      | ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,sK1),X1),X0))
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK5)),k2_zfmisc_1(X6,X7))
      | k1_xboole_0 = X4
      | ~ r2_hidden(k1_mcart_1(sK5),k2_zfmisc_1(X8,X9))
      | k1_xboole_0 = X5
      | ~ r2_hidden(sK5,k2_zfmisc_1(X10,X11))
      | k1_xboole_0 = X3 ) ),
    inference(equality_resolution,[],[f258])).

fof(f258,plain,(
    ! [X6,X4,X2,X0,X12,X10,X8,X7,X5,X3,X1,X11,X9] :
      ( sK5 != X4
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k2_mcart_1(k1_mcart_1(X4)) = sK4
      | ~ m1_subset_1(k2_mcart_1(X4),sK3)
      | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(X4)),sK2)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X5),X6))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,sK1),X2),X1))
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(X4)),k2_zfmisc_1(X7,X8))
      | k1_xboole_0 = X5
      | ~ r2_hidden(k1_mcart_1(X4),k2_zfmisc_1(X9,X10))
      | k1_xboole_0 = X6
      | ~ r2_hidden(X4,k2_zfmisc_1(X11,X12))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f252,f43])).

fof(f43,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f252,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X11,X9] :
      ( ~ v1_relat_1(X7)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X4
      | sK4 = k2_mcart_1(k1_mcart_1(X5))
      | ~ m1_subset_1(k2_mcart_1(X5),sK3)
      | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(X5)),sK2)
      | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X0),X6))
      | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,sK1),X3),X2))
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(X5)),X7)
      | k1_xboole_0 = X0
      | ~ r2_hidden(k1_mcart_1(X5),k2_zfmisc_1(X8,X9))
      | k1_xboole_0 = X6
      | ~ r2_hidden(X5,k2_zfmisc_1(X10,X11))
      | sK5 != X5 ) ),
    inference(resolution,[],[f200,f43])).

fof(f200,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( ~ v1_relat_1(X8)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X4
      | k1_xboole_0 = X5
      | sK4 = k2_mcart_1(k1_mcart_1(X6))
      | ~ m1_subset_1(k2_mcart_1(X6),sK3)
      | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(X6)),sK2)
      | ~ m1_subset_1(X6,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,X2),X1),X0))
      | ~ m1_subset_1(X6,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X5,sK1),X4),X3))
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(X6)),X7)
      | ~ v1_relat_1(X7)
      | ~ r2_hidden(k1_mcart_1(X6),X8)
      | k1_xboole_0 = X0
      | ~ r2_hidden(X6,k2_zfmisc_1(X9,X10))
      | sK5 != X6 ) ),
    inference(resolution,[],[f197,f43])).

fof(f197,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( ~ v1_relat_1(X9)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X4
      | k1_xboole_0 = X5
      | k1_xboole_0 = X6
      | sK4 = k2_mcart_1(k1_mcart_1(X0))
      | ~ m1_subset_1(k2_mcart_1(X0),sK3)
      | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(X0)),sK2)
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,X3),X2),X1))
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X6,sK1),X5),X4))
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(X0)),X7)
      | ~ v1_relat_1(X7)
      | ~ r2_hidden(k1_mcart_1(X0),X8)
      | ~ v1_relat_1(X8)
      | ~ r2_hidden(X0,X9)
      | sK5 != X0 ) ),
    inference(superposition,[],[f194,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f194,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sK5 != k4_tarski(k1_mcart_1(X0),X1)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X4
      | k1_xboole_0 = X5
      | k1_xboole_0 = X6
      | k1_xboole_0 = X7
      | sK4 = k2_mcart_1(k1_mcart_1(X0))
      | ~ m1_subset_1(X1,sK3)
      | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(X0)),sK2)
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,X4),X3),X2))
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X7,sK1),X6),X5))
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(X0)),X8)
      | ~ v1_relat_1(X8)
      | ~ r2_hidden(k1_mcart_1(X0),X9)
      | ~ v1_relat_1(X9) ) ),
    inference(superposition,[],[f191,f44])).

fof(f191,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sK5 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(X0)),X7),X8)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X4
      | k1_xboole_0 = X5
      | k1_xboole_0 = X6
      | sK4 = X7
      | ~ m1_subset_1(X8,sK3)
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X2),X3))
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X6,sK1),X5),X4))
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(X0)),X9)
      | ~ v1_relat_1(X9) ) ),
    inference(subsumption_resolution,[],[f188,f37])).

fof(f188,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = X4
      | k1_xboole_0 = X5
      | k1_xboole_0 = X6
      | sK4 = X7
      | ~ m1_subset_1(X8,sK3)
      | ~ m1_subset_1(X7,sK2)
      | sK5 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(X0)),X7),X8)
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X6,sK1),X5),X4))
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(X0)),X9)
      | ~ v1_relat_1(X9) ) ),
    inference(resolution,[],[f187,f185])).

fof(f185,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(X0))),sK0)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | sK4 = X4
      | ~ m1_subset_1(X5,sK3)
      | ~ m1_subset_1(X4,sK2)
      | sK5 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(X0)),X4),X5)
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,sK1),X2),X3))
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(X0)),X6)
      | ~ v1_relat_1(X6) ) ),
    inference(subsumption_resolution,[],[f184,f38])).

fof(f184,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,sK1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = X1
      | sK4 = X4
      | ~ m1_subset_1(X5,sK3)
      | ~ m1_subset_1(X4,sK2)
      | sK5 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(X0)),X4),X5)
      | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(X0))),sK0)
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(X0)),X6)
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f183,f135])).

fof(f135,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_mcart_1(X0),sK1)
      | sK4 = X1
      | ~ m1_subset_1(X2,sK3)
      | ~ m1_subset_1(X1,sK2)
      | k4_tarski(k4_tarski(X0,X1),X2) != sK5
      | ~ m1_subset_1(k1_mcart_1(X0),sK0)
      | ~ r2_hidden(X0,X3)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f67,f44])).

fof(f67,plain,(
    ! [X6,X8,X7,X9] :
      ( sK5 != k4_tarski(k4_tarski(k4_tarski(X6,X7),X8),X9)
      | sK4 = X8
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X6,sK0) ) ),
    inference(definition_unfolding,[],[f36,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f50,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f36,plain,(
    ! [X6,X8,X7,X9] :
      ( sK4 = X8
      | k4_mcart_1(X6,X7,X8,X9) != sK5
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X6,sK0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f183,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))),X1)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f182])).

fof(f182,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))),X1)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f79,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f58,f66])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) ) ),
    inference(definition_unfolding,[],[f62,f66])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_mcart_1)).

fof(f187,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))),X0)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f186])).

fof(f186,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))),X0)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f80,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f57,f66])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) ) ),
    inference(definition_unfolding,[],[f63,f66])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:44:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (24993)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.50  % (24998)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (25002)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (25010)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (25006)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (24995)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (24996)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (25014)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (25018)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (24994)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (25000)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (25015)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (25014)Refutation not found, incomplete strategy% (25014)------------------------------
% 0.21/0.53  % (25014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (25014)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (25014)Memory used [KB]: 10874
% 0.21/0.53  % (25014)Time elapsed: 0.109 s
% 0.21/0.53  % (25014)------------------------------
% 0.21/0.53  % (25014)------------------------------
% 0.21/0.54  % (25015)Refutation not found, incomplete strategy% (25015)------------------------------
% 0.21/0.54  % (25015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (25015)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (25015)Memory used [KB]: 1791
% 0.21/0.54  % (25015)Time elapsed: 0.080 s
% 0.21/0.54  % (25015)------------------------------
% 0.21/0.54  % (25015)------------------------------
% 0.21/0.54  % (24997)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (25019)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (25017)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (24999)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (25021)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (25020)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (25003)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (25007)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (24994)Refutation not found, incomplete strategy% (24994)------------------------------
% 0.21/0.55  % (24994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (24994)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (24994)Memory used [KB]: 10746
% 0.21/0.55  % (24994)Time elapsed: 0.135 s
% 0.21/0.55  % (24994)------------------------------
% 0.21/0.55  % (24994)------------------------------
% 0.21/0.55  % (25016)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (25012)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (25013)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (25011)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.56  % (25012)Refutation not found, incomplete strategy% (25012)------------------------------
% 0.21/0.56  % (25012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (25012)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (25012)Memory used [KB]: 10746
% 0.21/0.56  % (25012)Time elapsed: 0.140 s
% 0.21/0.56  % (25012)------------------------------
% 0.21/0.56  % (25012)------------------------------
% 0.21/0.56  % (25013)Refutation not found, incomplete strategy% (25013)------------------------------
% 0.21/0.56  % (25013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (25013)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (25013)Memory used [KB]: 1791
% 0.21/0.56  % (25013)Time elapsed: 0.139 s
% 0.21/0.56  % (25013)------------------------------
% 0.21/0.56  % (25013)------------------------------
% 0.21/0.56  % (25008)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (25004)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (25005)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.72/0.60  % (24992)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.72/0.61  % (24992)Refutation not found, incomplete strategy% (24992)------------------------------
% 1.72/0.61  % (24992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.61  % (25009)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.72/0.61  % (24992)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.61  
% 1.72/0.61  % (24992)Memory used [KB]: 1663
% 1.72/0.61  % (24992)Time elapsed: 0.162 s
% 1.72/0.61  % (24992)------------------------------
% 1.72/0.61  % (24992)------------------------------
% 1.72/0.61  % (25009)Refutation not found, incomplete strategy% (25009)------------------------------
% 1.72/0.61  % (25009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.61  % (25009)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.61  
% 1.72/0.61  % (25009)Memory used [KB]: 10618
% 1.72/0.61  % (25009)Time elapsed: 0.173 s
% 1.72/0.61  % (25009)------------------------------
% 1.72/0.61  % (25009)------------------------------
% 1.72/0.61  % (25001)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.72/0.63  % (24995)Refutation found. Thanks to Tanya!
% 1.72/0.63  % SZS status Theorem for theBenchmark
% 1.72/0.63  % SZS output start Proof for theBenchmark
% 1.72/0.63  fof(f503,plain,(
% 1.72/0.63    $false),
% 1.72/0.63    inference(avatar_sat_refutation,[],[f279,f291,f303,f311,f319,f344,f395,f488])).
% 1.72/0.63  fof(f488,plain,(
% 1.72/0.63    ~spl6_11),
% 1.72/0.63    inference(avatar_contradiction_clause,[],[f487])).
% 1.72/0.63  fof(f487,plain,(
% 1.72/0.63    $false | ~spl6_11),
% 1.72/0.63    inference(subsumption_resolution,[],[f486,f37])).
% 1.72/0.63  fof(f37,plain,(
% 1.72/0.63    k1_xboole_0 != sK0),
% 1.72/0.63    inference(cnf_transformation,[],[f32])).
% 1.72/0.63  fof(f32,plain,(
% 1.72/0.63    sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK4 = X8 | k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X9,sK3)) | ~m1_subset_1(X8,sK2)) | ~m1_subset_1(X7,sK1)) | ~m1_subset_1(X6,sK0)) & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 1.72/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f19,f31])).
% 1.72/0.63  fof(f31,plain,(
% 1.72/0.63    ? [X0,X1,X2,X3,X4,X5] : (k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) => (sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK4 = X8 | k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X9,sK3)) | ~m1_subset_1(X8,sK2)) | ~m1_subset_1(X7,sK1)) | ~m1_subset_1(X6,sK0)) & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)))),
% 1.72/0.63    introduced(choice_axiom,[])).
% 1.72/0.63  fof(f19,plain,(
% 1.72/0.63    ? [X0,X1,X2,X3,X4,X5] : (k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.72/0.63    inference(flattening,[],[f18])).
% 1.72/0.63  fof(f18,plain,(
% 1.72/0.63    ? [X0,X1,X2,X3,X4,X5] : (((k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.72/0.63    inference(ennf_transformation,[],[f17])).
% 1.72/0.63  fof(f17,negated_conjecture,(
% 1.72/0.63    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X8))))) => (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.72/0.63    inference(negated_conjecture,[],[f16])).
% 1.72/0.63  fof(f16,conjecture,(
% 1.72/0.63    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X8))))) => (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.72/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_mcart_1)).
% 1.72/0.63  fof(f486,plain,(
% 1.72/0.63    k1_xboole_0 = sK0 | ~spl6_11),
% 1.72/0.63    inference(subsumption_resolution,[],[f485,f38])).
% 1.72/0.63  fof(f38,plain,(
% 1.72/0.63    k1_xboole_0 != sK1),
% 1.72/0.63    inference(cnf_transformation,[],[f32])).
% 1.72/0.63  fof(f485,plain,(
% 1.72/0.63    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_11),
% 1.72/0.63    inference(subsumption_resolution,[],[f484,f39])).
% 1.72/0.63  fof(f39,plain,(
% 1.72/0.63    k1_xboole_0 != sK2),
% 1.72/0.63    inference(cnf_transformation,[],[f32])).
% 1.72/0.63  fof(f484,plain,(
% 1.72/0.63    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_11),
% 1.72/0.63    inference(subsumption_resolution,[],[f476,f40])).
% 1.72/0.63  fof(f40,plain,(
% 1.72/0.63    k1_xboole_0 != sK3),
% 1.72/0.63    inference(cnf_transformation,[],[f32])).
% 1.72/0.63  fof(f476,plain,(
% 1.72/0.63    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_11),
% 1.72/0.63    inference(trivial_inequality_removal,[],[f467])).
% 1.72/0.63  fof(f467,plain,(
% 1.72/0.63    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_11),
% 1.72/0.63    inference(superposition,[],[f73,f457])).
% 1.72/0.63  fof(f457,plain,(
% 1.72/0.63    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | ~spl6_11),
% 1.72/0.63    inference(resolution,[],[f442,f42])).
% 1.72/0.63  fof(f42,plain,(
% 1.72/0.63    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.72/0.63    inference(cnf_transformation,[],[f20])).
% 1.72/0.63  fof(f20,plain,(
% 1.72/0.63    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.72/0.63    inference(ennf_transformation,[],[f1])).
% 1.72/0.63  fof(f1,axiom,(
% 1.72/0.63    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.72/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.72/0.63  fof(f442,plain,(
% 1.72/0.63    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | ~spl6_11),
% 1.72/0.63    inference(resolution,[],[f423,f68])).
% 1.72/0.63  fof(f68,plain,(
% 1.72/0.63    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 1.72/0.63    inference(definition_unfolding,[],[f35,f66])).
% 1.72/0.63  fof(f66,plain,(
% 1.72/0.63    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.72/0.63    inference(definition_unfolding,[],[f51,f47])).
% 1.72/0.63  fof(f47,plain,(
% 1.72/0.63    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.72/0.63    inference(cnf_transformation,[],[f5])).
% 1.72/0.63  fof(f5,axiom,(
% 1.72/0.63    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.72/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.72/0.63  fof(f51,plain,(
% 1.72/0.63    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.72/0.63    inference(cnf_transformation,[],[f7])).
% 1.72/0.63  fof(f7,axiom,(
% 1.72/0.63    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.72/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.72/0.63  fof(f35,plain,(
% 1.72/0.63    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 1.72/0.63    inference(cnf_transformation,[],[f32])).
% 1.72/0.63  fof(f423,plain,(
% 1.72/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))) ) | ~spl6_11),
% 1.72/0.63    inference(resolution,[],[f414,f45])).
% 1.72/0.63  fof(f45,plain,(
% 1.72/0.63    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.72/0.63    inference(cnf_transformation,[],[f24])).
% 1.72/0.63  fof(f24,plain,(
% 1.72/0.63    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.72/0.63    inference(flattening,[],[f23])).
% 1.72/0.63  fof(f23,plain,(
% 1.72/0.63    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.72/0.63    inference(ennf_transformation,[],[f2])).
% 1.72/0.63  fof(f2,axiom,(
% 1.72/0.63    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.72/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.72/0.63  fof(f414,plain,(
% 1.72/0.63    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))) ) | ~spl6_11),
% 1.72/0.63    inference(resolution,[],[f404,f48])).
% 1.72/0.63  fof(f48,plain,(
% 1.72/0.63    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.72/0.63    inference(cnf_transformation,[],[f25])).
% 1.72/0.63  fof(f25,plain,(
% 1.72/0.63    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.72/0.63    inference(ennf_transformation,[],[f12])).
% 1.72/0.63  fof(f12,axiom,(
% 1.72/0.63    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.72/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.72/0.63  fof(f404,plain,(
% 1.72/0.63    ( ! [X2,X0,X1] : (~r2_hidden(k1_mcart_1(sK5),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) ) | ~spl6_11),
% 1.72/0.63    inference(resolution,[],[f278,f48])).
% 1.72/0.63  fof(f278,plain,(
% 1.72/0.63    ( ! [X6,X7] : (~r2_hidden(k1_mcart_1(k1_mcart_1(sK5)),k2_zfmisc_1(X6,X7))) ) | ~spl6_11),
% 1.72/0.63    inference(avatar_component_clause,[],[f277])).
% 1.72/0.63  fof(f277,plain,(
% 1.72/0.63    spl6_11 <=> ! [X7,X6] : ~r2_hidden(k1_mcart_1(k1_mcart_1(sK5)),k2_zfmisc_1(X6,X7))),
% 1.72/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.72/0.63  fof(f73,plain,(
% 1.72/0.63    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.72/0.63    inference(definition_unfolding,[],[f52,f66])).
% 1.72/0.63  fof(f52,plain,(
% 1.72/0.63    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.72/0.63    inference(cnf_transformation,[],[f34])).
% 1.72/0.63  fof(f34,plain,(
% 1.72/0.63    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.72/0.63    inference(flattening,[],[f33])).
% 1.72/0.63  fof(f33,plain,(
% 1.72/0.63    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.72/0.63    inference(nnf_transformation,[],[f14])).
% 1.72/0.63  fof(f14,axiom,(
% 1.72/0.63    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 1.72/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).
% 1.72/0.63  fof(f395,plain,(
% 1.72/0.63    ~spl6_10),
% 1.72/0.63    inference(avatar_contradiction_clause,[],[f394])).
% 1.72/0.63  fof(f394,plain,(
% 1.72/0.63    $false | ~spl6_10),
% 1.72/0.63    inference(subsumption_resolution,[],[f393,f37])).
% 1.72/0.63  fof(f393,plain,(
% 1.72/0.63    k1_xboole_0 = sK0 | ~spl6_10),
% 1.72/0.63    inference(subsumption_resolution,[],[f392,f38])).
% 1.72/0.63  fof(f392,plain,(
% 1.72/0.63    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_10),
% 1.72/0.63    inference(subsumption_resolution,[],[f391,f39])).
% 1.72/0.63  fof(f391,plain,(
% 1.72/0.63    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_10),
% 1.72/0.63    inference(subsumption_resolution,[],[f386,f40])).
% 1.72/0.63  fof(f386,plain,(
% 1.72/0.63    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_10),
% 1.72/0.63    inference(trivial_inequality_removal,[],[f379])).
% 1.72/0.63  fof(f379,plain,(
% 1.72/0.63    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_10),
% 1.72/0.63    inference(superposition,[],[f73,f373])).
% 1.72/0.63  fof(f373,plain,(
% 1.72/0.63    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | ~spl6_10),
% 1.72/0.63    inference(resolution,[],[f365,f42])).
% 1.72/0.63  fof(f365,plain,(
% 1.72/0.63    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | ~spl6_10),
% 1.72/0.63    inference(resolution,[],[f357,f68])).
% 1.72/0.63  fof(f357,plain,(
% 1.72/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) ) | ~spl6_10),
% 1.72/0.63    inference(resolution,[],[f350,f45])).
% 1.72/0.63  fof(f350,plain,(
% 1.72/0.63    ( ! [X2,X0,X1] : (~r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) ) | ~spl6_10),
% 1.72/0.63    inference(resolution,[],[f275,f48])).
% 1.72/0.63  fof(f275,plain,(
% 1.72/0.63    ( ! [X8,X9] : (~r2_hidden(k1_mcart_1(sK5),k2_zfmisc_1(X8,X9))) ) | ~spl6_10),
% 1.72/0.63    inference(avatar_component_clause,[],[f274])).
% 1.72/0.63  fof(f274,plain,(
% 1.72/0.63    spl6_10 <=> ! [X9,X8] : ~r2_hidden(k1_mcart_1(sK5),k2_zfmisc_1(X8,X9))),
% 1.72/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.72/0.63  fof(f344,plain,(
% 1.72/0.63    ~spl6_9),
% 1.72/0.63    inference(avatar_contradiction_clause,[],[f343])).
% 1.72/0.63  fof(f343,plain,(
% 1.72/0.63    $false | ~spl6_9),
% 1.72/0.63    inference(subsumption_resolution,[],[f342,f37])).
% 1.72/0.63  fof(f342,plain,(
% 1.72/0.63    k1_xboole_0 = sK0 | ~spl6_9),
% 1.72/0.63    inference(subsumption_resolution,[],[f341,f38])).
% 1.72/0.63  fof(f341,plain,(
% 1.72/0.63    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_9),
% 1.72/0.63    inference(subsumption_resolution,[],[f340,f39])).
% 1.72/0.63  fof(f340,plain,(
% 1.72/0.63    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_9),
% 1.72/0.63    inference(subsumption_resolution,[],[f335,f40])).
% 1.72/0.63  fof(f335,plain,(
% 1.72/0.63    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_9),
% 1.72/0.63    inference(trivial_inequality_removal,[],[f330])).
% 1.72/0.63  fof(f330,plain,(
% 1.72/0.63    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_9),
% 1.72/0.63    inference(superposition,[],[f73,f326])).
% 1.72/0.63  fof(f326,plain,(
% 1.72/0.63    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | ~spl6_9),
% 1.72/0.63    inference(resolution,[],[f323,f42])).
% 1.72/0.63  fof(f323,plain,(
% 1.72/0.63    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | ~spl6_9),
% 1.72/0.63    inference(resolution,[],[f320,f68])).
% 1.72/0.63  fof(f320,plain,(
% 1.72/0.63    ( ! [X0,X1] : (~m1_subset_1(sK5,k2_zfmisc_1(X0,X1)) | v1_xboole_0(k2_zfmisc_1(X0,X1))) ) | ~spl6_9),
% 1.72/0.63    inference(resolution,[],[f272,f45])).
% 1.72/0.63  fof(f272,plain,(
% 1.72/0.63    ( ! [X10,X11] : (~r2_hidden(sK5,k2_zfmisc_1(X10,X11))) ) | ~spl6_9),
% 1.72/0.63    inference(avatar_component_clause,[],[f271])).
% 1.72/0.63  fof(f271,plain,(
% 1.72/0.63    spl6_9 <=> ! [X11,X10] : ~r2_hidden(sK5,k2_zfmisc_1(X10,X11))),
% 1.72/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.72/0.63  fof(f319,plain,(
% 1.72/0.63    ~spl6_8),
% 1.72/0.63    inference(avatar_contradiction_clause,[],[f318])).
% 1.72/0.63  fof(f318,plain,(
% 1.72/0.63    $false | ~spl6_8),
% 1.72/0.63    inference(subsumption_resolution,[],[f317,f37])).
% 1.72/0.63  fof(f317,plain,(
% 1.72/0.63    k1_xboole_0 = sK0 | ~spl6_8),
% 1.72/0.63    inference(subsumption_resolution,[],[f316,f40])).
% 1.72/0.63  fof(f316,plain,(
% 1.72/0.63    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | ~spl6_8),
% 1.72/0.63    inference(subsumption_resolution,[],[f312,f39])).
% 1.72/0.63  fof(f312,plain,(
% 1.72/0.63    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | ~spl6_8),
% 1.72/0.63    inference(resolution,[],[f249,f68])).
% 1.72/0.63  fof(f249,plain,(
% 1.72/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,sK1),X1),X0)) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2) ) | ~spl6_8),
% 1.72/0.63    inference(avatar_component_clause,[],[f248])).
% 1.72/0.63  fof(f248,plain,(
% 1.72/0.63    spl6_8 <=> ! [X1,X0,X2] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | ~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,sK1),X1),X0)) | k1_xboole_0 = X2)),
% 1.72/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.72/0.63  fof(f311,plain,(
% 1.72/0.63    ~spl6_5),
% 1.72/0.63    inference(avatar_contradiction_clause,[],[f310])).
% 1.72/0.63  fof(f310,plain,(
% 1.72/0.63    $false | ~spl6_5),
% 1.72/0.63    inference(subsumption_resolution,[],[f309,f38])).
% 1.72/0.63  fof(f309,plain,(
% 1.72/0.63    k1_xboole_0 = sK1 | ~spl6_5),
% 1.72/0.63    inference(subsumption_resolution,[],[f308,f39])).
% 1.72/0.63  fof(f308,plain,(
% 1.72/0.63    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | ~spl6_5),
% 1.72/0.63    inference(subsumption_resolution,[],[f304,f40])).
% 1.72/0.63  fof(f304,plain,(
% 1.72/0.63    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | ~spl6_5),
% 1.72/0.63    inference(resolution,[],[f238,f68])).
% 1.72/0.63  fof(f238,plain,(
% 1.72/0.63    ( ! [X4,X5,X3] : (~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,X3),X4),X5)) | k1_xboole_0 = X5 | k1_xboole_0 = X4 | k1_xboole_0 = X3) ) | ~spl6_5),
% 1.72/0.63    inference(avatar_component_clause,[],[f237])).
% 1.72/0.63  fof(f237,plain,(
% 1.72/0.63    spl6_5 <=> ! [X3,X5,X4] : (~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,X3),X4),X5)) | k1_xboole_0 = X5 | k1_xboole_0 = X4 | k1_xboole_0 = X3)),
% 1.72/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.72/0.63  fof(f303,plain,(
% 1.72/0.63    spl6_7),
% 1.72/0.63    inference(avatar_contradiction_clause,[],[f302])).
% 1.72/0.63  fof(f302,plain,(
% 1.72/0.63    $false | spl6_7),
% 1.72/0.63    inference(subsumption_resolution,[],[f301,f37])).
% 1.72/0.63  fof(f301,plain,(
% 1.72/0.63    k1_xboole_0 = sK0 | spl6_7),
% 1.72/0.63    inference(subsumption_resolution,[],[f300,f38])).
% 1.72/0.63  fof(f300,plain,(
% 1.72/0.63    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl6_7),
% 1.72/0.63    inference(subsumption_resolution,[],[f296,f39])).
% 1.72/0.63  fof(f296,plain,(
% 1.72/0.63    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl6_7),
% 1.72/0.63    inference(resolution,[],[f293,f68])).
% 1.72/0.63  fof(f293,plain,(
% 1.72/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),sK3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | spl6_7),
% 1.72/0.63    inference(subsumption_resolution,[],[f292,f40])).
% 1.72/0.63  fof(f292,plain,(
% 1.72/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | spl6_7),
% 1.72/0.63    inference(resolution,[],[f246,f169])).
% 1.72/0.63  fof(f169,plain,(
% 1.72/0.63    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k2_mcart_1(X4),X3) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.72/0.63    inference(duplicate_literal_removal,[],[f168])).
% 1.72/0.63  fof(f168,plain,(
% 1.72/0.63    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k2_mcart_1(X4),X3) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.72/0.63    inference(superposition,[],[f78,f74])).
% 1.72/0.63  fof(f74,plain,(
% 1.72/0.63    ( ! [X4,X2,X0,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.72/0.63    inference(definition_unfolding,[],[f60,f66])).
% 1.72/0.63  fof(f60,plain,(
% 1.72/0.63    ( ! [X4,X2,X0,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.72/0.63    inference(cnf_transformation,[],[f26])).
% 1.72/0.63  fof(f26,plain,(
% 1.72/0.63    ! [X0,X1,X2,X3] : (! [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.72/0.63    inference(ennf_transformation,[],[f15])).
% 1.72/0.63  fof(f15,axiom,(
% 1.72/0.63    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.72/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).
% 1.72/0.63  fof(f78,plain,(
% 1.72/0.63    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))) )),
% 1.72/0.63    inference(definition_unfolding,[],[f61,f66])).
% 1.72/0.63  fof(f61,plain,(
% 1.72/0.63    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 1.72/0.63    inference(cnf_transformation,[],[f27])).
% 1.72/0.63  fof(f27,plain,(
% 1.72/0.63    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.72/0.63    inference(ennf_transformation,[],[f9])).
% 1.72/0.63  fof(f9,axiom,(
% 1.72/0.63    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3))),
% 1.72/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_mcart_1)).
% 1.72/0.63  fof(f246,plain,(
% 1.72/0.63    ~m1_subset_1(k2_mcart_1(sK5),sK3) | spl6_7),
% 1.72/0.63    inference(avatar_component_clause,[],[f244])).
% 1.72/0.63  fof(f244,plain,(
% 1.72/0.63    spl6_7 <=> m1_subset_1(k2_mcart_1(sK5),sK3)),
% 1.72/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.72/0.63  fof(f291,plain,(
% 1.72/0.63    spl6_6),
% 1.72/0.63    inference(avatar_contradiction_clause,[],[f290])).
% 1.72/0.63  fof(f290,plain,(
% 1.72/0.63    $false | spl6_6),
% 1.72/0.63    inference(subsumption_resolution,[],[f289,f37])).
% 1.72/0.63  fof(f289,plain,(
% 1.72/0.63    k1_xboole_0 = sK0 | spl6_6),
% 1.72/0.63    inference(subsumption_resolution,[],[f288,f38])).
% 1.72/0.63  fof(f288,plain,(
% 1.72/0.63    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl6_6),
% 1.72/0.63    inference(subsumption_resolution,[],[f284,f40])).
% 1.72/0.63  fof(f284,plain,(
% 1.72/0.63    k1_xboole_0 = sK3 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl6_6),
% 1.72/0.63    inference(resolution,[],[f282,f68])).
% 1.72/0.63  fof(f282,plain,(
% 1.72/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK2),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | spl6_6),
% 1.72/0.63    inference(subsumption_resolution,[],[f280,f39])).
% 1.72/0.63  fof(f280,plain,(
% 1.72/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK2),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = sK2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | spl6_6),
% 1.72/0.63    inference(resolution,[],[f242,f174])).
% 1.72/0.63  fof(f174,plain,(
% 1.72/0.63    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k2_mcart_1(k1_mcart_1(X4)),X2) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.72/0.63    inference(duplicate_literal_removal,[],[f173])).
% 1.72/0.63  fof(f173,plain,(
% 1.72/0.63    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k2_mcart_1(k1_mcart_1(X4)),X2) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.72/0.63    inference(superposition,[],[f81,f75])).
% 1.72/0.63  fof(f75,plain,(
% 1.72/0.63    ( ! [X4,X2,X0,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.72/0.63    inference(definition_unfolding,[],[f59,f66])).
% 1.72/0.63  fof(f59,plain,(
% 1.72/0.63    ( ! [X4,X2,X0,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.72/0.63    inference(cnf_transformation,[],[f26])).
% 1.72/0.63  fof(f81,plain,(
% 1.72/0.63    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))) )),
% 1.72/0.63    inference(definition_unfolding,[],[f64,f66])).
% 1.72/0.63  fof(f64,plain,(
% 1.72/0.63    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 1.72/0.63    inference(cnf_transformation,[],[f30])).
% 1.72/0.65  fof(f30,plain,(
% 1.72/0.65    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.72/0.65    inference(ennf_transformation,[],[f8])).
% 1.72/0.65  fof(f8,axiom,(
% 1.72/0.65    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2))),
% 1.72/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_mcart_1)).
% 1.72/0.65  fof(f242,plain,(
% 1.72/0.65    ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2) | spl6_6),
% 1.72/0.65    inference(avatar_component_clause,[],[f240])).
% 1.72/0.65  fof(f240,plain,(
% 1.72/0.65    spl6_6 <=> m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2)),
% 1.72/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.72/0.65  fof(f279,plain,(
% 1.72/0.65    spl6_9 | spl6_10 | spl6_11 | spl6_5 | ~spl6_6 | ~spl6_7 | spl6_8),
% 1.72/0.65    inference(avatar_split_clause,[],[f269,f248,f244,f240,f237,f277,f274,f271])).
% 1.72/0.65  fof(f269,plain,(
% 1.72/0.65    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X11,X9] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(k2_mcart_1(sK5),sK3) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2) | ~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,X3),X4),X5)) | ~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,sK1),X1),X0)) | ~r2_hidden(k1_mcart_1(k1_mcart_1(sK5)),k2_zfmisc_1(X6,X7)) | k1_xboole_0 = X4 | ~r2_hidden(k1_mcart_1(sK5),k2_zfmisc_1(X8,X9)) | k1_xboole_0 = X5 | ~r2_hidden(sK5,k2_zfmisc_1(X10,X11)) | k1_xboole_0 = X3) )),
% 1.72/0.65    inference(subsumption_resolution,[],[f268,f179])).
% 1.72/0.65  fof(f179,plain,(
% 1.72/0.65    sK4 != k2_mcart_1(k1_mcart_1(sK5))),
% 1.72/0.65    inference(subsumption_resolution,[],[f178,f37])).
% 1.72/0.65  fof(f178,plain,(
% 1.72/0.65    sK4 != k2_mcart_1(k1_mcart_1(sK5)) | k1_xboole_0 = sK0),
% 1.72/0.65    inference(subsumption_resolution,[],[f177,f38])).
% 1.72/0.65  fof(f177,plain,(
% 1.72/0.65    sK4 != k2_mcart_1(k1_mcart_1(sK5)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.72/0.65    inference(subsumption_resolution,[],[f176,f39])).
% 1.72/0.65  fof(f176,plain,(
% 1.72/0.65    sK4 != k2_mcart_1(k1_mcart_1(sK5)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.72/0.65    inference(subsumption_resolution,[],[f175,f40])).
% 1.72/0.65  fof(f175,plain,(
% 1.72/0.65    sK4 != k2_mcart_1(k1_mcart_1(sK5)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.72/0.65    inference(subsumption_resolution,[],[f172,f68])).
% 1.72/0.65  fof(f172,plain,(
% 1.72/0.65    sK4 != k2_mcart_1(k1_mcart_1(sK5)) | ~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.72/0.65    inference(superposition,[],[f41,f75])).
% 1.72/0.65  fof(f41,plain,(
% 1.72/0.65    sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 1.72/0.65    inference(cnf_transformation,[],[f32])).
% 1.72/0.65  fof(f268,plain,(
% 1.72/0.65    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X11,X9] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | sK4 = k2_mcart_1(k1_mcart_1(sK5)) | ~m1_subset_1(k2_mcart_1(sK5),sK3) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2) | ~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,X3),X4),X5)) | ~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,sK1),X1),X0)) | ~r2_hidden(k1_mcart_1(k1_mcart_1(sK5)),k2_zfmisc_1(X6,X7)) | k1_xboole_0 = X4 | ~r2_hidden(k1_mcart_1(sK5),k2_zfmisc_1(X8,X9)) | k1_xboole_0 = X5 | ~r2_hidden(sK5,k2_zfmisc_1(X10,X11)) | k1_xboole_0 = X3) )),
% 1.72/0.65    inference(equality_resolution,[],[f258])).
% 1.72/0.65  fof(f258,plain,(
% 1.72/0.65    ( ! [X6,X4,X2,X0,X12,X10,X8,X7,X5,X3,X1,X11,X9] : (sK5 != X4 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k2_mcart_1(k1_mcart_1(X4)) = sK4 | ~m1_subset_1(k2_mcart_1(X4),sK3) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(X4)),sK2) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X5),X6)) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,sK1),X2),X1)) | ~r2_hidden(k1_mcart_1(k1_mcart_1(X4)),k2_zfmisc_1(X7,X8)) | k1_xboole_0 = X5 | ~r2_hidden(k1_mcart_1(X4),k2_zfmisc_1(X9,X10)) | k1_xboole_0 = X6 | ~r2_hidden(X4,k2_zfmisc_1(X11,X12)) | k1_xboole_0 = X0) )),
% 1.72/0.65    inference(resolution,[],[f252,f43])).
% 1.72/0.65  fof(f43,plain,(
% 1.72/0.65    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.72/0.65    inference(cnf_transformation,[],[f3])).
% 1.72/0.65  fof(f3,axiom,(
% 1.72/0.65    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.72/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.72/0.65  fof(f252,plain,(
% 1.72/0.65    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X11,X9] : (~v1_relat_1(X7) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X4 | sK4 = k2_mcart_1(k1_mcart_1(X5)) | ~m1_subset_1(k2_mcart_1(X5),sK3) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(X5)),sK2) | ~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X0),X6)) | ~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,sK1),X3),X2)) | ~r2_hidden(k1_mcart_1(k1_mcart_1(X5)),X7) | k1_xboole_0 = X0 | ~r2_hidden(k1_mcart_1(X5),k2_zfmisc_1(X8,X9)) | k1_xboole_0 = X6 | ~r2_hidden(X5,k2_zfmisc_1(X10,X11)) | sK5 != X5) )),
% 1.72/0.65    inference(resolution,[],[f200,f43])).
% 1.72/0.65  fof(f200,plain,(
% 1.72/0.65    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] : (~v1_relat_1(X8) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X4 | k1_xboole_0 = X5 | sK4 = k2_mcart_1(k1_mcart_1(X6)) | ~m1_subset_1(k2_mcart_1(X6),sK3) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(X6)),sK2) | ~m1_subset_1(X6,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,X2),X1),X0)) | ~m1_subset_1(X6,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X5,sK1),X4),X3)) | ~r2_hidden(k1_mcart_1(k1_mcart_1(X6)),X7) | ~v1_relat_1(X7) | ~r2_hidden(k1_mcart_1(X6),X8) | k1_xboole_0 = X0 | ~r2_hidden(X6,k2_zfmisc_1(X9,X10)) | sK5 != X6) )),
% 1.72/0.65    inference(resolution,[],[f197,f43])).
% 1.72/0.65  fof(f197,plain,(
% 1.72/0.65    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (~v1_relat_1(X9) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X4 | k1_xboole_0 = X5 | k1_xboole_0 = X6 | sK4 = k2_mcart_1(k1_mcart_1(X0)) | ~m1_subset_1(k2_mcart_1(X0),sK3) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(X0)),sK2) | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,X3),X2),X1)) | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X6,sK1),X5),X4)) | ~r2_hidden(k1_mcart_1(k1_mcart_1(X0)),X7) | ~v1_relat_1(X7) | ~r2_hidden(k1_mcart_1(X0),X8) | ~v1_relat_1(X8) | ~r2_hidden(X0,X9) | sK5 != X0) )),
% 1.72/0.65    inference(superposition,[],[f194,f44])).
% 1.72/0.65  fof(f44,plain,(
% 1.72/0.65    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 1.72/0.65    inference(cnf_transformation,[],[f22])).
% 1.72/0.65  fof(f22,plain,(
% 1.72/0.65    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 1.72/0.65    inference(flattening,[],[f21])).
% 1.72/0.65  fof(f21,plain,(
% 1.72/0.65    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 1.72/0.65    inference(ennf_transformation,[],[f13])).
% 1.72/0.65  fof(f13,axiom,(
% 1.72/0.65    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 1.72/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).
% 1.72/0.65  fof(f194,plain,(
% 1.72/0.65    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sK5 != k4_tarski(k1_mcart_1(X0),X1) | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X4 | k1_xboole_0 = X5 | k1_xboole_0 = X6 | k1_xboole_0 = X7 | sK4 = k2_mcart_1(k1_mcart_1(X0)) | ~m1_subset_1(X1,sK3) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(X0)),sK2) | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,X4),X3),X2)) | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X7,sK1),X6),X5)) | ~r2_hidden(k1_mcart_1(k1_mcart_1(X0)),X8) | ~v1_relat_1(X8) | ~r2_hidden(k1_mcart_1(X0),X9) | ~v1_relat_1(X9)) )),
% 1.72/0.65    inference(superposition,[],[f191,f44])).
% 1.72/0.65  fof(f191,plain,(
% 1.72/0.65    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sK5 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(X0)),X7),X8) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X4 | k1_xboole_0 = X5 | k1_xboole_0 = X6 | sK4 = X7 | ~m1_subset_1(X8,sK3) | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X2),X3)) | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X6,sK1),X5),X4)) | ~r2_hidden(k1_mcart_1(k1_mcart_1(X0)),X9) | ~v1_relat_1(X9)) )),
% 1.72/0.65    inference(subsumption_resolution,[],[f188,f37])).
% 1.72/0.65  fof(f188,plain,(
% 1.72/0.65    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = sK0 | k1_xboole_0 = X4 | k1_xboole_0 = X5 | k1_xboole_0 = X6 | sK4 = X7 | ~m1_subset_1(X8,sK3) | ~m1_subset_1(X7,sK2) | sK5 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(X0)),X7),X8) | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X6,sK1),X5),X4)) | ~r2_hidden(k1_mcart_1(k1_mcart_1(X0)),X9) | ~v1_relat_1(X9)) )),
% 1.72/0.65    inference(resolution,[],[f187,f185])).
% 1.72/0.65  fof(f185,plain,(
% 1.72/0.65    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(X0))),sK0) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | sK4 = X4 | ~m1_subset_1(X5,sK3) | ~m1_subset_1(X4,sK2) | sK5 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(X0)),X4),X5) | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,sK1),X2),X3)) | ~r2_hidden(k1_mcart_1(k1_mcart_1(X0)),X6) | ~v1_relat_1(X6)) )),
% 1.72/0.65    inference(subsumption_resolution,[],[f184,f38])).
% 1.72/0.65  fof(f184,plain,(
% 1.72/0.65    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,sK1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = sK1 | k1_xboole_0 = X1 | sK4 = X4 | ~m1_subset_1(X5,sK3) | ~m1_subset_1(X4,sK2) | sK5 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(X0)),X4),X5) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(X0))),sK0) | ~r2_hidden(k1_mcart_1(k1_mcart_1(X0)),X6) | ~v1_relat_1(X6)) )),
% 1.72/0.65    inference(resolution,[],[f183,f135])).
% 1.72/0.65  fof(f135,plain,(
% 1.72/0.65    ( ! [X2,X0,X3,X1] : (~m1_subset_1(k2_mcart_1(X0),sK1) | sK4 = X1 | ~m1_subset_1(X2,sK3) | ~m1_subset_1(X1,sK2) | k4_tarski(k4_tarski(X0,X1),X2) != sK5 | ~m1_subset_1(k1_mcart_1(X0),sK0) | ~r2_hidden(X0,X3) | ~v1_relat_1(X3)) )),
% 1.72/0.65    inference(superposition,[],[f67,f44])).
% 1.72/0.65  fof(f67,plain,(
% 1.72/0.65    ( ! [X6,X8,X7,X9] : (sK5 != k4_tarski(k4_tarski(k4_tarski(X6,X7),X8),X9) | sK4 = X8 | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X6,sK0)) )),
% 1.72/0.65    inference(definition_unfolding,[],[f36,f65])).
% 1.72/0.65  fof(f65,plain,(
% 1.72/0.65    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 1.72/0.65    inference(definition_unfolding,[],[f50,f46])).
% 1.72/0.65  fof(f46,plain,(
% 1.72/0.65    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.72/0.65    inference(cnf_transformation,[],[f4])).
% 1.72/0.65  fof(f4,axiom,(
% 1.72/0.65    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.72/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.72/0.65  fof(f50,plain,(
% 1.72/0.65    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 1.72/0.65    inference(cnf_transformation,[],[f6])).
% 1.72/0.65  fof(f6,axiom,(
% 1.72/0.65    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 1.72/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).
% 1.72/0.65  fof(f36,plain,(
% 1.72/0.65    ( ! [X6,X8,X7,X9] : (sK4 = X8 | k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X6,sK0)) )),
% 1.72/0.65    inference(cnf_transformation,[],[f32])).
% 1.72/0.65  fof(f183,plain,(
% 1.72/0.65    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))),X1) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.72/0.65    inference(duplicate_literal_removal,[],[f182])).
% 1.72/0.65  fof(f182,plain,(
% 1.72/0.65    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))),X1) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.72/0.65    inference(superposition,[],[f79,f76])).
% 1.72/0.65  fof(f76,plain,(
% 1.72/0.65    ( ! [X4,X2,X0,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.72/0.65    inference(definition_unfolding,[],[f58,f66])).
% 1.72/0.65  fof(f58,plain,(
% 1.72/0.65    ( ! [X4,X2,X0,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.72/0.65    inference(cnf_transformation,[],[f26])).
% 1.72/0.65  fof(f79,plain,(
% 1.72/0.65    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))) )),
% 1.72/0.65    inference(definition_unfolding,[],[f62,f66])).
% 1.72/0.65  fof(f62,plain,(
% 1.72/0.65    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 1.72/0.65    inference(cnf_transformation,[],[f28])).
% 1.72/0.65  fof(f28,plain,(
% 1.72/0.65    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.72/0.65    inference(ennf_transformation,[],[f11])).
% 1.72/0.65  fof(f11,axiom,(
% 1.72/0.65    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1))),
% 1.72/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_mcart_1)).
% 1.72/0.65  fof(f187,plain,(
% 1.72/0.65    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))),X0) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.72/0.65    inference(duplicate_literal_removal,[],[f186])).
% 1.72/0.65  fof(f186,plain,(
% 1.72/0.65    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))),X0) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.72/0.65    inference(superposition,[],[f80,f77])).
% 1.72/0.65  fof(f77,plain,(
% 1.72/0.65    ( ! [X4,X2,X0,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.72/0.65    inference(definition_unfolding,[],[f57,f66])).
% 1.72/0.65  fof(f57,plain,(
% 1.72/0.65    ( ! [X4,X2,X0,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.72/0.65    inference(cnf_transformation,[],[f26])).
% 1.72/0.65  fof(f80,plain,(
% 1.72/0.65    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))) )),
% 1.72/0.65    inference(definition_unfolding,[],[f63,f66])).
% 1.72/0.65  fof(f63,plain,(
% 1.72/0.65    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 1.72/0.65    inference(cnf_transformation,[],[f29])).
% 1.72/0.65  fof(f29,plain,(
% 1.72/0.65    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.72/0.65    inference(ennf_transformation,[],[f10])).
% 1.72/0.65  fof(f10,axiom,(
% 1.72/0.65    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0))),
% 1.72/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_mcart_1)).
% 1.72/0.65  % SZS output end Proof for theBenchmark
% 1.72/0.65  % (24995)------------------------------
% 1.72/0.65  % (24995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.65  % (24995)Termination reason: Refutation
% 1.72/0.65  
% 1.72/0.65  % (24995)Memory used [KB]: 11129
% 1.72/0.65  % (24995)Time elapsed: 0.221 s
% 1.72/0.65  % (24995)------------------------------
% 1.72/0.65  % (24995)------------------------------
% 1.72/0.65  % (24991)Success in time 0.282 s
%------------------------------------------------------------------------------
