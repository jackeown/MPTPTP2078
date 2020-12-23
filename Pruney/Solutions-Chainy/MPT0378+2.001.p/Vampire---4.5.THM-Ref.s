%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:34 EST 2020

% Result     : Theorem 1.69s
% Output     : Refutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 259 expanded)
%              Number of leaves         :   23 ( 112 expanded)
%              Depth                    :   18
%              Number of atoms          :  465 (1791 expanded)
%              Number of equality atoms :   81 ( 282 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f351,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f54,f54,f54,f95,f54,f60,f346,f214])).

fof(f214,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ sP1(X5,X0,X2,X3,X4)
      | ~ m1_subset_1(X2,X1)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X4,X1)
      | k1_xboole_0 = X1
      | r2_hidden(X5,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f158,f148])).

fof(f148,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,k2_enumset1(X4,X3,X2,X1))
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(resolution,[],[f82,f99])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] : sP2(X0,X1,X2,X3,k2_enumset1(X0,X1,X2,X3)) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ~ sP2(X0,X1,X2,X3,X4) )
      & ( sP2(X0,X1,X2,X3,X4)
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> sP2(X0,X1,X2,X3,X4) ) ),
    inference(definition_folding,[],[f21,f25,f24])).

fof(f24,plain,(
    ! [X5,X3,X2,X1,X0] :
      ( sP1(X5,X3,X2,X1,X0)
    <=> ( X3 = X5
        | X2 = X5
        | X1 = X5
        | X0 = X5 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( sP2(X0,X1,X2,X3,X4)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> sP1(X5,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).

fof(f82,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ sP2(X0,X1,X2,X3,X4)
      | ~ sP1(X6,X3,X2,X1,X0)
      | r2_hidden(X6,X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP2(X0,X1,X2,X3,X4)
        | ( ( ~ sP1(sK12(X0,X1,X2,X3,X4),X3,X2,X1,X0)
            | ~ r2_hidden(sK12(X0,X1,X2,X3,X4),X4) )
          & ( sP1(sK12(X0,X1,X2,X3,X4),X3,X2,X1,X0)
            | r2_hidden(sK12(X0,X1,X2,X3,X4),X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ~ sP1(X6,X3,X2,X1,X0) )
            & ( sP1(X6,X3,X2,X1,X0)
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP2(X0,X1,X2,X3,X4) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f47,f48])).

fof(f48,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ~ sP1(X5,X3,X2,X1,X0)
            | ~ r2_hidden(X5,X4) )
          & ( sP1(X5,X3,X2,X1,X0)
            | r2_hidden(X5,X4) ) )
     => ( ( ~ sP1(sK12(X0,X1,X2,X3,X4),X3,X2,X1,X0)
          | ~ r2_hidden(sK12(X0,X1,X2,X3,X4),X4) )
        & ( sP1(sK12(X0,X1,X2,X3,X4),X3,X2,X1,X0)
          | r2_hidden(sK12(X0,X1,X2,X3,X4),X4) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP2(X0,X1,X2,X3,X4)
        | ? [X5] :
            ( ( ~ sP1(X5,X3,X2,X1,X0)
              | ~ r2_hidden(X5,X4) )
            & ( sP1(X5,X3,X2,X1,X0)
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ~ sP1(X6,X3,X2,X1,X0) )
            & ( sP1(X6,X3,X2,X1,X0)
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP2(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP2(X0,X1,X2,X3,X4)
        | ? [X5] :
            ( ( ~ sP1(X5,X3,X2,X1,X0)
              | ~ r2_hidden(X5,X4) )
            & ( sP1(X5,X3,X2,X1,X0)
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ~ sP1(X5,X3,X2,X1,X0) )
            & ( sP1(X5,X3,X2,X1,X0)
              | ~ r2_hidden(X5,X4) ) )
        | ~ sP2(X0,X1,X2,X3,X4) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f158,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X5,k2_enumset1(X4,X3,X2,X1))
      | ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X4,X0)
      | k1_xboole_0 = X0
      | r2_hidden(X5,X0) ) ),
    inference(resolution,[],[f69,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ! [X4] :
                  ( m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0))
                  | k1_xboole_0 = X0
                  | ~ m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ! [X4] :
                  ( m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0))
                  | k1_xboole_0 = X0
                  | ~ m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ! [X3] :
              ( m1_subset_1(X3,X0)
             => ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => ( k1_xboole_0 != X0
                   => m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_subset_1)).

fof(f346,plain,(
    ~ r2_hidden(sK4,sK3) ),
    inference(subsumption_resolution,[],[f345,f63])).

fof(f63,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK10(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f35,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK10(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
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

fof(f345,plain,
    ( ~ r2_hidden(sK4,sK3)
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f334,f113])).

fof(f113,plain,
    ( r2_hidden(sK5,sK3)
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f65,f55])).

fof(f55,plain,(
    m1_subset_1(sK5,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ m1_subset_1(k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK3))
    & k1_xboole_0 != sK3
    & m1_subset_1(sK9,sK3)
    & m1_subset_1(sK8,sK3)
    & m1_subset_1(sK7,sK3)
    & m1_subset_1(sK6,sK3)
    & m1_subset_1(sK5,sK3)
    & m1_subset_1(sK4,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f14,f32,f31,f30,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
                            & k1_xboole_0 != X0
                            & m1_subset_1(X6,X0) )
                        & m1_subset_1(X5,X0) )
                    & m1_subset_1(X4,X0) )
                & m1_subset_1(X3,X0) )
            & m1_subset_1(X2,X0) )
        & m1_subset_1(X1,X0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ m1_subset_1(k4_enumset1(sK4,X2,X3,X4,X5,X6),k1_zfmisc_1(sK3))
                          & k1_xboole_0 != sK3
                          & m1_subset_1(X6,sK3) )
                      & m1_subset_1(X5,sK3) )
                  & m1_subset_1(X4,sK3) )
              & m1_subset_1(X3,sK3) )
          & m1_subset_1(X2,sK3) )
      & m1_subset_1(sK4,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ m1_subset_1(k4_enumset1(sK4,X2,X3,X4,X5,X6),k1_zfmisc_1(sK3))
                        & k1_xboole_0 != sK3
                        & m1_subset_1(X6,sK3) )
                    & m1_subset_1(X5,sK3) )
                & m1_subset_1(X4,sK3) )
            & m1_subset_1(X3,sK3) )
        & m1_subset_1(X2,sK3) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ m1_subset_1(k4_enumset1(sK4,sK5,X3,X4,X5,X6),k1_zfmisc_1(sK3))
                      & k1_xboole_0 != sK3
                      & m1_subset_1(X6,sK3) )
                  & m1_subset_1(X5,sK3) )
              & m1_subset_1(X4,sK3) )
          & m1_subset_1(X3,sK3) )
      & m1_subset_1(sK5,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ m1_subset_1(k4_enumset1(sK4,sK5,X3,X4,X5,X6),k1_zfmisc_1(sK3))
                    & k1_xboole_0 != sK3
                    & m1_subset_1(X6,sK3) )
                & m1_subset_1(X5,sK3) )
            & m1_subset_1(X4,sK3) )
        & m1_subset_1(X3,sK3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ m1_subset_1(k4_enumset1(sK4,sK5,sK6,X4,X5,X6),k1_zfmisc_1(sK3))
                  & k1_xboole_0 != sK3
                  & m1_subset_1(X6,sK3) )
              & m1_subset_1(X5,sK3) )
          & m1_subset_1(X4,sK3) )
      & m1_subset_1(sK6,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ~ m1_subset_1(k4_enumset1(sK4,sK5,sK6,X4,X5,X6),k1_zfmisc_1(sK3))
                & k1_xboole_0 != sK3
                & m1_subset_1(X6,sK3) )
            & m1_subset_1(X5,sK3) )
        & m1_subset_1(X4,sK3) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ~ m1_subset_1(k4_enumset1(sK4,sK5,sK6,sK7,X5,X6),k1_zfmisc_1(sK3))
              & k1_xboole_0 != sK3
              & m1_subset_1(X6,sK3) )
          & m1_subset_1(X5,sK3) )
      & m1_subset_1(sK7,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ~ m1_subset_1(k4_enumset1(sK4,sK5,sK6,sK7,X5,X6),k1_zfmisc_1(sK3))
            & k1_xboole_0 != sK3
            & m1_subset_1(X6,sK3) )
        & m1_subset_1(X5,sK3) )
   => ( ? [X6] :
          ( ~ m1_subset_1(k4_enumset1(sK4,sK5,sK6,sK7,sK8,X6),k1_zfmisc_1(sK3))
          & k1_xboole_0 != sK3
          & m1_subset_1(X6,sK3) )
      & m1_subset_1(sK8,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X6] :
        ( ~ m1_subset_1(k4_enumset1(sK4,sK5,sK6,sK7,sK8,X6),k1_zfmisc_1(sK3))
        & k1_xboole_0 != sK3
        & m1_subset_1(X6,sK3) )
   => ( ~ m1_subset_1(k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK3))
      & k1_xboole_0 != sK3
      & m1_subset_1(sK9,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
                          & k1_xboole_0 != X0
                          & m1_subset_1(X6,X0) )
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
                          & k1_xboole_0 != X0
                          & m1_subset_1(X6,X0) )
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ! [X2] :
            ( m1_subset_1(X2,X0)
           => ! [X3] :
                ( m1_subset_1(X3,X0)
               => ! [X4] :
                    ( m1_subset_1(X4,X0)
                   => ! [X5] :
                        ( m1_subset_1(X5,X0)
                       => ! [X6] :
                            ( m1_subset_1(X6,X0)
                           => ( k1_xboole_0 != X0
                             => m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ! [X3] :
              ( m1_subset_1(X3,X0)
             => ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => ! [X5] :
                      ( m1_subset_1(X5,X0)
                     => ! [X6] :
                          ( m1_subset_1(X6,X0)
                         => ( k1_xboole_0 != X0
                           => m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_subset_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f334,plain,
    ( ~ r2_hidden(sK5,sK3)
    | ~ r2_hidden(sK4,sK3) ),
    inference(resolution,[],[f323,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f323,plain,(
    ~ r1_tarski(k2_tarski(sK4,sK5),sK3) ),
    inference(subsumption_resolution,[],[f322,f59])).

fof(f59,plain,(
    m1_subset_1(sK9,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f322,plain,
    ( ~ r1_tarski(k2_tarski(sK4,sK5),sK3)
    | ~ m1_subset_1(sK9,sK3) ),
    inference(subsumption_resolution,[],[f321,f60])).

fof(f321,plain,
    ( ~ r1_tarski(k2_tarski(sK4,sK5),sK3)
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK9,sK3) ),
    inference(subsumption_resolution,[],[f320,f56])).

fof(f56,plain,(
    m1_subset_1(sK6,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f320,plain,
    ( ~ r1_tarski(k2_tarski(sK4,sK5),sK3)
    | ~ m1_subset_1(sK6,sK3)
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK9,sK3) ),
    inference(subsumption_resolution,[],[f319,f57])).

fof(f57,plain,(
    m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f319,plain,
    ( ~ r1_tarski(k2_tarski(sK4,sK5),sK3)
    | ~ m1_subset_1(sK7,sK3)
    | ~ m1_subset_1(sK6,sK3)
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK9,sK3) ),
    inference(subsumption_resolution,[],[f317,f58])).

fof(f58,plain,(
    m1_subset_1(sK8,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f317,plain,
    ( ~ r1_tarski(k2_tarski(sK4,sK5),sK3)
    | ~ m1_subset_1(sK8,sK3)
    | ~ m1_subset_1(sK7,sK3)
    | ~ m1_subset_1(sK6,sK3)
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK9,sK3) ),
    inference(resolution,[],[f275,f209])).

fof(f209,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_tarski(k2_enumset1(X4,X3,X2,X0),X1)
      | ~ m1_subset_1(X2,X1)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X4,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f163,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f71,f94])).

fof(f94,plain,(
    ! [X0] : sP0(X0,k1_zfmisc_1(X0)) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f4,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( ~ sP0(X0,X1)
      | ~ r2_hidden(X3,X1)
      | r1_tarski(X3,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ~ r1_tarski(sK11(X0,X1),X0)
            | ~ r2_hidden(sK11(X0,X1),X1) )
          & ( r1_tarski(sK11(X0,X1),X0)
            | r2_hidden(sK11(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK11(X0,X1),X0)
          | ~ r2_hidden(sK11(X0,X1),X1) )
        & ( r1_tarski(sK11(X0,X1),X0)
          | r2_hidden(sK11(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f163,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( r2_hidden(k2_enumset1(X10,X9,X8,X7),k1_zfmisc_1(X6))
      | ~ m1_subset_1(X7,X6)
      | ~ m1_subset_1(X8,X6)
      | ~ m1_subset_1(X9,X6)
      | ~ m1_subset_1(X10,X6)
      | k1_xboole_0 = X6 ) ),
    inference(subsumption_resolution,[],[f159,f62])).

fof(f62,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f159,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( k1_xboole_0 = X6
      | ~ m1_subset_1(X7,X6)
      | ~ m1_subset_1(X8,X6)
      | ~ m1_subset_1(X9,X6)
      | ~ m1_subset_1(X10,X6)
      | r2_hidden(k2_enumset1(X10,X9,X8,X7),k1_zfmisc_1(X6))
      | v1_xboole_0(k1_zfmisc_1(X6)) ) ),
    inference(resolution,[],[f69,f65])).

% (25006)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (25010)Refutation not found, incomplete strategy% (25010)------------------------------
% (25010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25010)Termination reason: Refutation not found, incomplete strategy

% (25010)Memory used [KB]: 10746
% (25010)Time elapsed: 0.212 s
% (25010)------------------------------
% (25010)------------------------------
fof(f275,plain,
    ( ~ r1_tarski(k2_enumset1(sK6,sK7,sK8,sK9),sK3)
    | ~ r1_tarski(k2_tarski(sK4,sK5),sK3) ),
    inference(resolution,[],[f178,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f178,plain,(
    ~ r1_tarski(k2_xboole_0(k2_tarski(sK4,sK5),k2_enumset1(sK6,sK7,sK8,sK9)),sK3) ),
    inference(resolution,[],[f172,f93])).

fof(f93,plain,(
    ~ m1_subset_1(k2_xboole_0(k2_tarski(sK4,sK5),k2_enumset1(sK6,sK7,sK8,sK9)),k1_zfmisc_1(sK3)) ),
    inference(definition_unfolding,[],[f61,f92])).

fof(f92,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_enumset1)).

fof(f61,plain,(
    ~ m1_subset_1(k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f33])).

fof(f172,plain,(
    ! [X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X3))
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f122,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f66,f63])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f122,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f72,f94])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( ~ sP0(X0,X1)
      | ~ r1_tarski(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f60,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f33])).

fof(f95,plain,(
    ! [X4,X2,X3,X1] : sP1(X1,X1,X2,X3,X4) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP1(X0,X1,X2,X3,X4)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | ~ sP1(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X5,X3,X2,X1,X0] :
      ( ( sP1(X5,X3,X2,X1,X0)
        | ( X3 != X5
          & X2 != X5
          & X1 != X5
          & X0 != X5 ) )
      & ( X3 = X5
        | X2 = X5
        | X1 = X5
        | X0 = X5
        | ~ sP1(X5,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X5,X3,X2,X1,X0] :
      ( ( sP1(X5,X3,X2,X1,X0)
        | ( X3 != X5
          & X2 != X5
          & X1 != X5
          & X0 != X5 ) )
      & ( X3 = X5
        | X2 = X5
        | X1 = X5
        | X0 = X5
        | ~ sP1(X5,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f54,plain,(
    m1_subset_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:07:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (25016)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (25000)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (24995)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.56  % (24995)Refutation not found, incomplete strategy% (24995)------------------------------
% 0.21/0.56  % (24995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (24995)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (24995)Memory used [KB]: 10746
% 0.21/0.56  % (24995)Time elapsed: 0.118 s
% 0.21/0.56  % (24995)------------------------------
% 0.21/0.56  % (24995)------------------------------
% 1.46/0.57  % (25002)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.46/0.58  % (24997)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.46/0.58  % (25011)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.46/0.58  % (24996)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.46/0.58  % (24993)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.46/0.58  % (24998)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.69/0.59  % (25008)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.69/0.59  % (25022)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.69/0.60  % (25009)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.69/0.61  % (25004)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.69/0.61  % (25020)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.69/0.61  % (24994)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.69/0.61  % (25003)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.69/0.62  % (25012)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.69/0.62  % (25015)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.69/0.62  % (25001)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.69/0.62  % (25005)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.69/0.62  % (25015)Refutation not found, incomplete strategy% (25015)------------------------------
% 1.69/0.62  % (25015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.62  % (25015)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.62  
% 1.69/0.62  % (25015)Memory used [KB]: 10746
% 1.69/0.62  % (25015)Time elapsed: 0.196 s
% 1.69/0.62  % (25015)------------------------------
% 1.69/0.62  % (25015)------------------------------
% 1.69/0.62  % (25018)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.69/0.62  % (25007)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.69/0.63  % (25017)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.69/0.63  % (25019)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.69/0.63  % (24999)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.69/0.63  % (25014)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.69/0.63  % (25001)Refutation not found, incomplete strategy% (25001)------------------------------
% 1.69/0.63  % (25001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.63  % (25001)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.63  
% 1.69/0.63  % (25001)Memory used [KB]: 10746
% 1.69/0.63  % (25001)Time elapsed: 0.201 s
% 1.69/0.63  % (25001)------------------------------
% 1.69/0.63  % (25001)------------------------------
% 1.69/0.64  % (25010)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.69/0.64  % (25021)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.69/0.65  % (25013)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.69/0.65  % (25022)Refutation found. Thanks to Tanya!
% 1.69/0.65  % SZS status Theorem for theBenchmark
% 1.69/0.65  % SZS output start Proof for theBenchmark
% 1.69/0.65  fof(f351,plain,(
% 1.69/0.65    $false),
% 1.69/0.65    inference(unit_resulting_resolution,[],[f54,f54,f54,f95,f54,f60,f346,f214])).
% 1.69/0.65  fof(f214,plain,(
% 1.69/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (~sP1(X5,X0,X2,X3,X4) | ~m1_subset_1(X2,X1) | ~m1_subset_1(X3,X1) | ~m1_subset_1(X4,X1) | k1_xboole_0 = X1 | r2_hidden(X5,X1) | ~m1_subset_1(X0,X1)) )),
% 1.69/0.65    inference(resolution,[],[f158,f148])).
% 1.69/0.65  fof(f148,plain,(
% 1.69/0.65    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X0,k2_enumset1(X4,X3,X2,X1)) | ~sP1(X0,X1,X2,X3,X4)) )),
% 1.69/0.65    inference(resolution,[],[f82,f99])).
% 1.69/0.65  fof(f99,plain,(
% 1.69/0.65    ( ! [X2,X0,X3,X1] : (sP2(X0,X1,X2,X3,k2_enumset1(X0,X1,X2,X3))) )),
% 1.69/0.65    inference(equality_resolution,[],[f90])).
% 1.69/0.65  fof(f90,plain,(
% 1.69/0.65    ( ! [X4,X2,X0,X3,X1] : (sP2(X0,X1,X2,X3,X4) | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 1.69/0.65    inference(cnf_transformation,[],[f53])).
% 1.69/0.65  fof(f53,plain,(
% 1.69/0.65    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ~sP2(X0,X1,X2,X3,X4)) & (sP2(X0,X1,X2,X3,X4) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 1.69/0.65    inference(nnf_transformation,[],[f26])).
% 1.69/0.65  fof(f26,plain,(
% 1.69/0.65    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> sP2(X0,X1,X2,X3,X4))),
% 1.69/0.65    inference(definition_folding,[],[f21,f25,f24])).
% 1.69/0.65  fof(f24,plain,(
% 1.69/0.65    ! [X5,X3,X2,X1,X0] : (sP1(X5,X3,X2,X1,X0) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5))),
% 1.69/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.69/0.65  fof(f25,plain,(
% 1.69/0.65    ! [X0,X1,X2,X3,X4] : (sP2(X0,X1,X2,X3,X4) <=> ! [X5] : (r2_hidden(X5,X4) <=> sP1(X5,X3,X2,X1,X0)))),
% 1.69/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.69/0.65  fof(f21,plain,(
% 1.69/0.65    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 1.69/0.65    inference(ennf_transformation,[],[f6])).
% 1.69/0.65  fof(f6,axiom,(
% 1.69/0.65    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> ~(X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)))),
% 1.69/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).
% 1.69/0.65  fof(f82,plain,(
% 1.69/0.65    ( ! [X6,X4,X2,X0,X3,X1] : (~sP2(X0,X1,X2,X3,X4) | ~sP1(X6,X3,X2,X1,X0) | r2_hidden(X6,X4)) )),
% 1.69/0.65    inference(cnf_transformation,[],[f49])).
% 1.69/0.65  fof(f49,plain,(
% 1.69/0.65    ! [X0,X1,X2,X3,X4] : ((sP2(X0,X1,X2,X3,X4) | ((~sP1(sK12(X0,X1,X2,X3,X4),X3,X2,X1,X0) | ~r2_hidden(sK12(X0,X1,X2,X3,X4),X4)) & (sP1(sK12(X0,X1,X2,X3,X4),X3,X2,X1,X0) | r2_hidden(sK12(X0,X1,X2,X3,X4),X4)))) & (! [X6] : ((r2_hidden(X6,X4) | ~sP1(X6,X3,X2,X1,X0)) & (sP1(X6,X3,X2,X1,X0) | ~r2_hidden(X6,X4))) | ~sP2(X0,X1,X2,X3,X4)))),
% 1.69/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f47,f48])).
% 1.69/0.65  fof(f48,plain,(
% 1.69/0.65    ! [X4,X3,X2,X1,X0] : (? [X5] : ((~sP1(X5,X3,X2,X1,X0) | ~r2_hidden(X5,X4)) & (sP1(X5,X3,X2,X1,X0) | r2_hidden(X5,X4))) => ((~sP1(sK12(X0,X1,X2,X3,X4),X3,X2,X1,X0) | ~r2_hidden(sK12(X0,X1,X2,X3,X4),X4)) & (sP1(sK12(X0,X1,X2,X3,X4),X3,X2,X1,X0) | r2_hidden(sK12(X0,X1,X2,X3,X4),X4))))),
% 1.69/0.65    introduced(choice_axiom,[])).
% 1.69/0.65  fof(f47,plain,(
% 1.69/0.65    ! [X0,X1,X2,X3,X4] : ((sP2(X0,X1,X2,X3,X4) | ? [X5] : ((~sP1(X5,X3,X2,X1,X0) | ~r2_hidden(X5,X4)) & (sP1(X5,X3,X2,X1,X0) | r2_hidden(X5,X4)))) & (! [X6] : ((r2_hidden(X6,X4) | ~sP1(X6,X3,X2,X1,X0)) & (sP1(X6,X3,X2,X1,X0) | ~r2_hidden(X6,X4))) | ~sP2(X0,X1,X2,X3,X4)))),
% 1.69/0.65    inference(rectify,[],[f46])).
% 1.69/0.65  fof(f46,plain,(
% 1.69/0.65    ! [X0,X1,X2,X3,X4] : ((sP2(X0,X1,X2,X3,X4) | ? [X5] : ((~sP1(X5,X3,X2,X1,X0) | ~r2_hidden(X5,X4)) & (sP1(X5,X3,X2,X1,X0) | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | ~sP1(X5,X3,X2,X1,X0)) & (sP1(X5,X3,X2,X1,X0) | ~r2_hidden(X5,X4))) | ~sP2(X0,X1,X2,X3,X4)))),
% 1.69/0.65    inference(nnf_transformation,[],[f25])).
% 1.69/0.65  fof(f158,plain,(
% 1.69/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(X5,k2_enumset1(X4,X3,X2,X1)) | ~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X4,X0) | k1_xboole_0 = X0 | r2_hidden(X5,X0)) )),
% 1.69/0.65    inference(resolution,[],[f69,f70])).
% 1.69/0.65  fof(f70,plain,(
% 1.69/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.69/0.65    inference(cnf_transformation,[],[f18])).
% 1.69/0.65  fof(f18,plain,(
% 1.69/0.65    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.69/0.65    inference(ennf_transformation,[],[f9])).
% 1.69/0.65  fof(f9,axiom,(
% 1.69/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.69/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.69/0.65  fof(f69,plain,(
% 1.69/0.65    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 1.69/0.65    inference(cnf_transformation,[],[f17])).
% 1.69/0.65  fof(f17,plain,(
% 1.69/0.65    ! [X0,X1] : (! [X2] : (! [X3] : (! [X4] : (m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,X0))),
% 1.69/0.65    inference(flattening,[],[f16])).
% 1.69/0.65  fof(f16,plain,(
% 1.69/0.65    ! [X0,X1] : (! [X2] : (! [X3] : (! [X4] : ((m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,X0))),
% 1.69/0.65    inference(ennf_transformation,[],[f10])).
% 1.69/0.65  fof(f10,axiom,(
% 1.69/0.65    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => ! [X4] : (m1_subset_1(X4,X0) => (k1_xboole_0 != X0 => m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0)))))))),
% 1.69/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_subset_1)).
% 1.69/0.65  fof(f346,plain,(
% 1.69/0.65    ~r2_hidden(sK4,sK3)),
% 1.69/0.65    inference(subsumption_resolution,[],[f345,f63])).
% 1.69/0.65  fof(f63,plain,(
% 1.69/0.65    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.69/0.65    inference(cnf_transformation,[],[f37])).
% 1.69/0.65  fof(f37,plain,(
% 1.69/0.65    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK10(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.69/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f35,f36])).
% 1.69/0.65  fof(f36,plain,(
% 1.69/0.65    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK10(X0),X0))),
% 1.69/0.65    introduced(choice_axiom,[])).
% 1.69/0.65  fof(f35,plain,(
% 1.69/0.65    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.69/0.65    inference(rectify,[],[f34])).
% 1.69/0.65  fof(f34,plain,(
% 1.69/0.65    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.69/0.65    inference(nnf_transformation,[],[f1])).
% 1.69/0.65  fof(f1,axiom,(
% 1.69/0.65    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.69/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.69/0.65  fof(f345,plain,(
% 1.69/0.65    ~r2_hidden(sK4,sK3) | v1_xboole_0(sK3)),
% 1.69/0.65    inference(resolution,[],[f334,f113])).
% 1.69/0.65  fof(f113,plain,(
% 1.69/0.65    r2_hidden(sK5,sK3) | v1_xboole_0(sK3)),
% 1.69/0.65    inference(resolution,[],[f65,f55])).
% 1.69/0.65  fof(f55,plain,(
% 1.69/0.65    m1_subset_1(sK5,sK3)),
% 1.69/0.65    inference(cnf_transformation,[],[f33])).
% 1.69/0.65  fof(f33,plain,(
% 1.69/0.65    (((((~m1_subset_1(k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK3)) & k1_xboole_0 != sK3 & m1_subset_1(sK9,sK3)) & m1_subset_1(sK8,sK3)) & m1_subset_1(sK7,sK3)) & m1_subset_1(sK6,sK3)) & m1_subset_1(sK5,sK3)) & m1_subset_1(sK4,sK3)),
% 1.69/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f14,f32,f31,f30,f29,f28,f27])).
% 1.69/0.65  fof(f27,plain,(
% 1.69/0.65    ? [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(sK4,X2,X3,X4,X5,X6),k1_zfmisc_1(sK3)) & k1_xboole_0 != sK3 & m1_subset_1(X6,sK3)) & m1_subset_1(X5,sK3)) & m1_subset_1(X4,sK3)) & m1_subset_1(X3,sK3)) & m1_subset_1(X2,sK3)) & m1_subset_1(sK4,sK3))),
% 1.69/0.65    introduced(choice_axiom,[])).
% 1.69/0.65  fof(f28,plain,(
% 1.69/0.65    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(sK4,X2,X3,X4,X5,X6),k1_zfmisc_1(sK3)) & k1_xboole_0 != sK3 & m1_subset_1(X6,sK3)) & m1_subset_1(X5,sK3)) & m1_subset_1(X4,sK3)) & m1_subset_1(X3,sK3)) & m1_subset_1(X2,sK3)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(sK4,sK5,X3,X4,X5,X6),k1_zfmisc_1(sK3)) & k1_xboole_0 != sK3 & m1_subset_1(X6,sK3)) & m1_subset_1(X5,sK3)) & m1_subset_1(X4,sK3)) & m1_subset_1(X3,sK3)) & m1_subset_1(sK5,sK3))),
% 1.69/0.65    introduced(choice_axiom,[])).
% 1.69/0.65  fof(f29,plain,(
% 1.69/0.65    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(sK4,sK5,X3,X4,X5,X6),k1_zfmisc_1(sK3)) & k1_xboole_0 != sK3 & m1_subset_1(X6,sK3)) & m1_subset_1(X5,sK3)) & m1_subset_1(X4,sK3)) & m1_subset_1(X3,sK3)) => (? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(sK4,sK5,sK6,X4,X5,X6),k1_zfmisc_1(sK3)) & k1_xboole_0 != sK3 & m1_subset_1(X6,sK3)) & m1_subset_1(X5,sK3)) & m1_subset_1(X4,sK3)) & m1_subset_1(sK6,sK3))),
% 1.69/0.65    introduced(choice_axiom,[])).
% 1.69/0.65  fof(f30,plain,(
% 1.69/0.65    ? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(sK4,sK5,sK6,X4,X5,X6),k1_zfmisc_1(sK3)) & k1_xboole_0 != sK3 & m1_subset_1(X6,sK3)) & m1_subset_1(X5,sK3)) & m1_subset_1(X4,sK3)) => (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(sK4,sK5,sK6,sK7,X5,X6),k1_zfmisc_1(sK3)) & k1_xboole_0 != sK3 & m1_subset_1(X6,sK3)) & m1_subset_1(X5,sK3)) & m1_subset_1(sK7,sK3))),
% 1.69/0.65    introduced(choice_axiom,[])).
% 1.69/0.65  fof(f31,plain,(
% 1.69/0.65    ? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(sK4,sK5,sK6,sK7,X5,X6),k1_zfmisc_1(sK3)) & k1_xboole_0 != sK3 & m1_subset_1(X6,sK3)) & m1_subset_1(X5,sK3)) => (? [X6] : (~m1_subset_1(k4_enumset1(sK4,sK5,sK6,sK7,sK8,X6),k1_zfmisc_1(sK3)) & k1_xboole_0 != sK3 & m1_subset_1(X6,sK3)) & m1_subset_1(sK8,sK3))),
% 1.69/0.65    introduced(choice_axiom,[])).
% 1.69/0.65  fof(f32,plain,(
% 1.69/0.65    ? [X6] : (~m1_subset_1(k4_enumset1(sK4,sK5,sK6,sK7,sK8,X6),k1_zfmisc_1(sK3)) & k1_xboole_0 != sK3 & m1_subset_1(X6,sK3)) => (~m1_subset_1(k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK3)) & k1_xboole_0 != sK3 & m1_subset_1(sK9,sK3))),
% 1.69/0.65    introduced(choice_axiom,[])).
% 1.69/0.65  fof(f14,plain,(
% 1.69/0.65    ? [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 1.69/0.65    inference(flattening,[],[f13])).
% 1.69/0.65  fof(f13,plain,(
% 1.69/0.65    ? [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) & k1_xboole_0 != X0) & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 1.69/0.65    inference(ennf_transformation,[],[f12])).
% 1.69/0.65  fof(f12,negated_conjecture,(
% 1.69/0.65    ~! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X0) => (k1_xboole_0 != X0 => m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)))))))))),
% 1.69/0.65    inference(negated_conjecture,[],[f11])).
% 1.69/0.65  fof(f11,conjecture,(
% 1.69/0.65    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X0) => (k1_xboole_0 != X0 => m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)))))))))),
% 1.69/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_subset_1)).
% 1.69/0.65  fof(f65,plain,(
% 1.69/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.69/0.65    inference(cnf_transformation,[],[f38])).
% 1.69/0.65  fof(f38,plain,(
% 1.69/0.65    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.69/0.65    inference(nnf_transformation,[],[f15])).
% 1.69/0.65  fof(f15,plain,(
% 1.69/0.65    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.69/0.65    inference(ennf_transformation,[],[f7])).
% 1.69/0.65  fof(f7,axiom,(
% 1.69/0.65    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.69/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.69/0.65  fof(f334,plain,(
% 1.69/0.65    ~r2_hidden(sK5,sK3) | ~r2_hidden(sK4,sK3)),
% 1.69/0.65    inference(resolution,[],[f323,f80])).
% 1.69/0.65  fof(f80,plain,(
% 1.69/0.65    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.69/0.65    inference(cnf_transformation,[],[f45])).
% 1.69/0.65  fof(f45,plain,(
% 1.69/0.65    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.69/0.65    inference(flattening,[],[f44])).
% 1.69/0.65  fof(f44,plain,(
% 1.69/0.65    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.69/0.65    inference(nnf_transformation,[],[f5])).
% 1.69/0.65  fof(f5,axiom,(
% 1.69/0.65    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.69/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.69/0.65  fof(f323,plain,(
% 1.69/0.65    ~r1_tarski(k2_tarski(sK4,sK5),sK3)),
% 1.69/0.65    inference(subsumption_resolution,[],[f322,f59])).
% 1.69/0.65  fof(f59,plain,(
% 1.69/0.65    m1_subset_1(sK9,sK3)),
% 1.69/0.65    inference(cnf_transformation,[],[f33])).
% 1.69/0.65  fof(f322,plain,(
% 1.69/0.65    ~r1_tarski(k2_tarski(sK4,sK5),sK3) | ~m1_subset_1(sK9,sK3)),
% 1.69/0.65    inference(subsumption_resolution,[],[f321,f60])).
% 1.69/0.65  fof(f321,plain,(
% 1.69/0.65    ~r1_tarski(k2_tarski(sK4,sK5),sK3) | k1_xboole_0 = sK3 | ~m1_subset_1(sK9,sK3)),
% 1.69/0.65    inference(subsumption_resolution,[],[f320,f56])).
% 1.69/0.65  fof(f56,plain,(
% 1.69/0.65    m1_subset_1(sK6,sK3)),
% 1.69/0.65    inference(cnf_transformation,[],[f33])).
% 1.69/0.65  fof(f320,plain,(
% 1.69/0.65    ~r1_tarski(k2_tarski(sK4,sK5),sK3) | ~m1_subset_1(sK6,sK3) | k1_xboole_0 = sK3 | ~m1_subset_1(sK9,sK3)),
% 1.69/0.65    inference(subsumption_resolution,[],[f319,f57])).
% 1.69/0.65  fof(f57,plain,(
% 1.69/0.65    m1_subset_1(sK7,sK3)),
% 1.69/0.65    inference(cnf_transformation,[],[f33])).
% 1.69/0.65  fof(f319,plain,(
% 1.69/0.65    ~r1_tarski(k2_tarski(sK4,sK5),sK3) | ~m1_subset_1(sK7,sK3) | ~m1_subset_1(sK6,sK3) | k1_xboole_0 = sK3 | ~m1_subset_1(sK9,sK3)),
% 1.69/0.65    inference(subsumption_resolution,[],[f317,f58])).
% 1.69/0.65  fof(f58,plain,(
% 1.69/0.65    m1_subset_1(sK8,sK3)),
% 1.69/0.65    inference(cnf_transformation,[],[f33])).
% 1.69/0.65  fof(f317,plain,(
% 1.69/0.65    ~r1_tarski(k2_tarski(sK4,sK5),sK3) | ~m1_subset_1(sK8,sK3) | ~m1_subset_1(sK7,sK3) | ~m1_subset_1(sK6,sK3) | k1_xboole_0 = sK3 | ~m1_subset_1(sK9,sK3)),
% 1.69/0.65    inference(resolution,[],[f275,f209])).
% 1.69/0.65  fof(f209,plain,(
% 1.69/0.65    ( ! [X4,X2,X0,X3,X1] : (r1_tarski(k2_enumset1(X4,X3,X2,X0),X1) | ~m1_subset_1(X2,X1) | ~m1_subset_1(X3,X1) | ~m1_subset_1(X4,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X0,X1)) )),
% 1.69/0.65    inference(resolution,[],[f163,f121])).
% 1.69/0.65  fof(f121,plain,(
% 1.69/0.65    ( ! [X0,X1] : (~r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.69/0.65    inference(resolution,[],[f71,f94])).
% 1.69/0.65  fof(f94,plain,(
% 1.69/0.65    ( ! [X0] : (sP0(X0,k1_zfmisc_1(X0))) )),
% 1.69/0.65    inference(equality_resolution,[],[f75])).
% 1.69/0.65  fof(f75,plain,(
% 1.69/0.65    ( ! [X0,X1] : (sP0(X0,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.69/0.65    inference(cnf_transformation,[],[f43])).
% 1.69/0.65  fof(f43,plain,(
% 1.69/0.65    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k1_zfmisc_1(X0) != X1))),
% 1.69/0.65    inference(nnf_transformation,[],[f23])).
% 1.69/0.65  fof(f23,plain,(
% 1.69/0.65    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> sP0(X0,X1))),
% 1.69/0.65    inference(definition_folding,[],[f4,f22])).
% 1.69/0.65  fof(f22,plain,(
% 1.69/0.65    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.69/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.69/0.65  fof(f4,axiom,(
% 1.69/0.65    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.69/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.69/0.65  fof(f71,plain,(
% 1.69/0.65    ( ! [X0,X3,X1] : (~sP0(X0,X1) | ~r2_hidden(X3,X1) | r1_tarski(X3,X0)) )),
% 1.69/0.65    inference(cnf_transformation,[],[f42])).
% 1.69/0.65  fof(f42,plain,(
% 1.69/0.65    ! [X0,X1] : ((sP0(X0,X1) | ((~r1_tarski(sK11(X0,X1),X0) | ~r2_hidden(sK11(X0,X1),X1)) & (r1_tarski(sK11(X0,X1),X0) | r2_hidden(sK11(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 1.69/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f40,f41])).
% 1.69/0.65  fof(f41,plain,(
% 1.69/0.65    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK11(X0,X1),X0) | ~r2_hidden(sK11(X0,X1),X1)) & (r1_tarski(sK11(X0,X1),X0) | r2_hidden(sK11(X0,X1),X1))))),
% 1.69/0.65    introduced(choice_axiom,[])).
% 1.69/0.65  fof(f40,plain,(
% 1.69/0.65    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 1.69/0.65    inference(rectify,[],[f39])).
% 1.69/0.65  fof(f39,plain,(
% 1.69/0.65    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 1.69/0.65    inference(nnf_transformation,[],[f22])).
% 1.69/0.65  fof(f163,plain,(
% 1.69/0.65    ( ! [X6,X10,X8,X7,X9] : (r2_hidden(k2_enumset1(X10,X9,X8,X7),k1_zfmisc_1(X6)) | ~m1_subset_1(X7,X6) | ~m1_subset_1(X8,X6) | ~m1_subset_1(X9,X6) | ~m1_subset_1(X10,X6) | k1_xboole_0 = X6) )),
% 1.69/0.65    inference(subsumption_resolution,[],[f159,f62])).
% 1.69/0.65  fof(f62,plain,(
% 1.69/0.65    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.69/0.65    inference(cnf_transformation,[],[f8])).
% 1.69/0.65  fof(f8,axiom,(
% 1.69/0.65    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.69/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.69/0.65  fof(f159,plain,(
% 1.69/0.65    ( ! [X6,X10,X8,X7,X9] : (k1_xboole_0 = X6 | ~m1_subset_1(X7,X6) | ~m1_subset_1(X8,X6) | ~m1_subset_1(X9,X6) | ~m1_subset_1(X10,X6) | r2_hidden(k2_enumset1(X10,X9,X8,X7),k1_zfmisc_1(X6)) | v1_xboole_0(k1_zfmisc_1(X6))) )),
% 1.69/0.65    inference(resolution,[],[f69,f65])).
% 1.69/0.66  % (25006)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.20/0.66  % (25010)Refutation not found, incomplete strategy% (25010)------------------------------
% 2.20/0.66  % (25010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.66  % (25010)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.66  
% 2.20/0.66  % (25010)Memory used [KB]: 10746
% 2.20/0.66  % (25010)Time elapsed: 0.212 s
% 2.20/0.66  % (25010)------------------------------
% 2.20/0.66  % (25010)------------------------------
% 2.31/0.68  fof(f275,plain,(
% 2.31/0.68    ~r1_tarski(k2_enumset1(sK6,sK7,sK8,sK9),sK3) | ~r1_tarski(k2_tarski(sK4,sK5),sK3)),
% 2.31/0.68    inference(resolution,[],[f178,f77])).
% 2.31/0.68  fof(f77,plain,(
% 2.31/0.68    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.31/0.68    inference(cnf_transformation,[],[f20])).
% 2.31/0.68  fof(f20,plain,(
% 2.31/0.68    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.31/0.68    inference(flattening,[],[f19])).
% 2.31/0.68  fof(f19,plain,(
% 2.31/0.68    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.31/0.68    inference(ennf_transformation,[],[f2])).
% 2.31/0.68  fof(f2,axiom,(
% 2.31/0.68    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 2.31/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 2.31/0.68  fof(f178,plain,(
% 2.31/0.68    ~r1_tarski(k2_xboole_0(k2_tarski(sK4,sK5),k2_enumset1(sK6,sK7,sK8,sK9)),sK3)),
% 2.31/0.68    inference(resolution,[],[f172,f93])).
% 2.31/0.68  fof(f93,plain,(
% 2.31/0.68    ~m1_subset_1(k2_xboole_0(k2_tarski(sK4,sK5),k2_enumset1(sK6,sK7,sK8,sK9)),k1_zfmisc_1(sK3))),
% 2.31/0.68    inference(definition_unfolding,[],[f61,f92])).
% 2.31/0.68  fof(f92,plain,(
% 2.31/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))) )),
% 2.31/0.68    inference(cnf_transformation,[],[f3])).
% 2.31/0.68  fof(f3,axiom,(
% 2.31/0.68    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))),
% 2.31/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_enumset1)).
% 2.31/0.68  fof(f61,plain,(
% 2.31/0.68    ~m1_subset_1(k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK3))),
% 2.31/0.68    inference(cnf_transformation,[],[f33])).
% 2.31/0.68  fof(f172,plain,(
% 2.31/0.68    ( ! [X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(X3)) | ~r1_tarski(X2,X3)) )),
% 2.31/0.68    inference(resolution,[],[f122,f119])).
% 2.31/0.68  fof(f119,plain,(
% 2.31/0.68    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 2.31/0.68    inference(subsumption_resolution,[],[f66,f63])).
% 2.31/0.68  fof(f66,plain,(
% 2.31/0.68    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.31/0.68    inference(cnf_transformation,[],[f38])).
% 2.31/0.68  fof(f122,plain,(
% 2.31/0.68    ( ! [X0,X1] : (r2_hidden(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.31/0.68    inference(resolution,[],[f72,f94])).
% 2.31/0.68  fof(f72,plain,(
% 2.31/0.68    ( ! [X0,X3,X1] : (~sP0(X0,X1) | ~r1_tarski(X3,X0) | r2_hidden(X3,X1)) )),
% 2.31/0.68    inference(cnf_transformation,[],[f42])).
% 2.31/0.68  fof(f60,plain,(
% 2.31/0.68    k1_xboole_0 != sK3),
% 2.31/0.68    inference(cnf_transformation,[],[f33])).
% 2.31/0.68  fof(f95,plain,(
% 2.31/0.68    ( ! [X4,X2,X3,X1] : (sP1(X1,X1,X2,X3,X4)) )),
% 2.31/0.68    inference(equality_resolution,[],[f89])).
% 2.31/0.68  fof(f89,plain,(
% 2.31/0.68    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X1,X2,X3,X4) | X0 != X1) )),
% 2.31/0.68    inference(cnf_transformation,[],[f52])).
% 2.31/0.68  fof(f52,plain,(
% 2.31/0.68    ! [X0,X1,X2,X3,X4] : ((sP1(X0,X1,X2,X3,X4) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | ~sP1(X0,X1,X2,X3,X4)))),
% 2.31/0.68    inference(rectify,[],[f51])).
% 2.31/0.68  fof(f51,plain,(
% 2.31/0.68    ! [X5,X3,X2,X1,X0] : ((sP1(X5,X3,X2,X1,X0) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | ~sP1(X5,X3,X2,X1,X0)))),
% 2.31/0.68    inference(flattening,[],[f50])).
% 2.31/0.68  fof(f50,plain,(
% 2.31/0.68    ! [X5,X3,X2,X1,X0] : ((sP1(X5,X3,X2,X1,X0) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | ~sP1(X5,X3,X2,X1,X0)))),
% 2.31/0.68    inference(nnf_transformation,[],[f24])).
% 2.31/0.68  fof(f54,plain,(
% 2.31/0.68    m1_subset_1(sK4,sK3)),
% 2.31/0.68    inference(cnf_transformation,[],[f33])).
% 2.31/0.68  % SZS output end Proof for theBenchmark
% 2.31/0.68  % (25022)------------------------------
% 2.31/0.68  % (25022)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.31/0.68  % (25022)Termination reason: Refutation
% 2.31/0.68  
% 2.31/0.68  % (25022)Memory used [KB]: 2174
% 2.31/0.68  % (25022)Time elapsed: 0.230 s
% 2.31/0.68  % (25022)------------------------------
% 2.31/0.68  % (25022)------------------------------
% 2.31/0.68  % (24992)Success in time 0.306 s
%------------------------------------------------------------------------------
