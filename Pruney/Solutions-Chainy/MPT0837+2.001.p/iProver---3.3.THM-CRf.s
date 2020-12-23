%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:20 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 446 expanded)
%              Number of clauses        :   58 ( 117 expanded)
%              Number of leaves         :   20 ( 150 expanded)
%              Depth                    :   19
%              Number of atoms          :  396 (2665 expanded)
%              Number of equality atoms :   45 ( 152 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ! [X3] :
                  ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                <=> ? [X4] :
                      ( r2_hidden(k4_tarski(X4,X3),X2)
                      & m1_subset_1(X4,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ! [X3] :
                    ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                  <=> ? [X4] :
                        ( r2_hidden(k4_tarski(X4,X3),X2)
                        & m1_subset_1(X4,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f48])).

fof(f97,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                <~> ? [X4] :
                      ( r2_hidden(k4_tarski(X4,X3),X2)
                      & m1_subset_1(X4,X1) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f49])).

fof(f155,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
                  & ( ? [X4] :
                        ( r2_hidden(k4_tarski(X4,X3),X2)
                        & m1_subset_1(X4,X1) )
                    | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f97])).

fof(f156,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
                  & ( ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X3),X2)
                        & m1_subset_1(X5,X1) )
                    | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(rectify,[],[f155])).

fof(f161,plain,(
    ! [X2,X3,X1] :
      ( ? [X5] :
          ( r2_hidden(k4_tarski(X5,X3),X2)
          & m1_subset_1(X5,X1) )
     => ( r2_hidden(k4_tarski(sK28,X3),X2)
        & m1_subset_1(sK28,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                | ~ m1_subset_1(X4,X1) )
            | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
          & ( ? [X5] :
                ( r2_hidden(k4_tarski(X5,X3),X2)
                & m1_subset_1(X5,X1) )
            | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(k4_tarski(X4,sK27),X2)
              | ~ m1_subset_1(X4,X1) )
          | ~ r2_hidden(sK27,k2_relset_1(X1,X0,X2)) )
        & ( ? [X5] :
              ( r2_hidden(k4_tarski(X5,sK27),X2)
              & m1_subset_1(X5,X1) )
          | r2_hidden(sK27,k2_relset_1(X1,X0,X2)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f159,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ! [X4] :
                    ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                    | ~ m1_subset_1(X4,X1) )
                | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
              & ( ? [X5] :
                    ( r2_hidden(k4_tarski(X5,X3),X2)
                    & m1_subset_1(X5,X1) )
                | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
     => ( ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(k4_tarski(X4,X3),sK26)
                  | ~ m1_subset_1(X4,X1) )
              | ~ r2_hidden(X3,k2_relset_1(X1,X0,sK26)) )
            & ( ? [X5] :
                  ( r2_hidden(k4_tarski(X5,X3),sK26)
                  & m1_subset_1(X5,X1) )
              | r2_hidden(X3,k2_relset_1(X1,X0,sK26)) ) )
        & m1_subset_1(sK26,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f158,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
                  & ( ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X3),X2)
                        & m1_subset_1(X5,X1) )
                    | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                      | ~ m1_subset_1(X4,sK25) )
                  | ~ r2_hidden(X3,k2_relset_1(sK25,X0,X2)) )
                & ( ? [X5] :
                      ( r2_hidden(k4_tarski(X5,X3),X2)
                      & m1_subset_1(X5,sK25) )
                  | r2_hidden(X3,k2_relset_1(sK25,X0,X2)) ) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK25,X0))) )
        & ~ v1_xboole_0(sK25) ) ) ),
    introduced(choice_axiom,[])).

fof(f157,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ! [X4] :
                          ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                          | ~ m1_subset_1(X4,X1) )
                      | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
                    & ( ? [X5] :
                          ( r2_hidden(k4_tarski(X5,X3),X2)
                          & m1_subset_1(X5,X1) )
                      | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k2_relset_1(X1,sK24,X2)) )
                  & ( ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X3),X2)
                        & m1_subset_1(X5,X1) )
                    | r2_hidden(X3,k2_relset_1(X1,sK24,X2)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK24))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK24) ) ),
    introduced(choice_axiom,[])).

fof(f162,plain,
    ( ( ! [X4] :
          ( ~ r2_hidden(k4_tarski(X4,sK27),sK26)
          | ~ m1_subset_1(X4,sK25) )
      | ~ r2_hidden(sK27,k2_relset_1(sK25,sK24,sK26)) )
    & ( ( r2_hidden(k4_tarski(sK28,sK27),sK26)
        & m1_subset_1(sK28,sK25) )
      | r2_hidden(sK27,k2_relset_1(sK25,sK24,sK26)) )
    & m1_subset_1(sK26,k1_zfmisc_1(k2_zfmisc_1(sK25,sK24)))
    & ~ v1_xboole_0(sK25)
    & ~ v1_xboole_0(sK24) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK24,sK25,sK26,sK27,sK28])],[f156,f161,f160,f159,f158,f157])).

fof(f253,plain,(
    ! [X4] :
      ( ~ r2_hidden(k4_tarski(X4,sK27),sK26)
      | ~ m1_subset_1(X4,sK25)
      | ~ r2_hidden(sK27,k2_relset_1(sK25,sK24,sK26)) ) ),
    inference(cnf_transformation,[],[f162])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f127,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f128,plain,(
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
    inference(rectify,[],[f127])).

fof(f131,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK13(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f130,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK12(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f129,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK11(X0,X1)),X0)
          | ~ r2_hidden(sK11(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK11(X0,X1)),X0)
          | r2_hidden(sK11(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK11(X0,X1)),X0)
            | ~ r2_hidden(sK11(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK12(X0,X1),sK11(X0,X1)),X0)
            | r2_hidden(sK11(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK13(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12,sK13])],[f128,f131,f130,f129])).

fof(f208,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f132])).

fof(f258,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f208])).

fof(f250,plain,(
    m1_subset_1(sK26,k1_zfmisc_1(k2_zfmisc_1(sK25,sK24))) ),
    inference(cnf_transformation,[],[f162])).

fof(f43,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f237,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f252,plain,
    ( r2_hidden(k4_tarski(sK28,sK27),sK26)
    | r2_hidden(sK27,k2_relset_1(sK25,sK24,sK26)) ),
    inference(cnf_transformation,[],[f162])).

fof(f207,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK13(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f132])).

fof(f259,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK13(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f207])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f192,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f65])).

fof(f196,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f109,plain,(
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
    inference(nnf_transformation,[],[f53])).

fof(f179,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f109])).

fof(f28,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f211,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f116,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f194,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f116])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f191,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f195,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f116])).

fof(f251,plain,
    ( m1_subset_1(sK28,sK25)
    | r2_hidden(sK27,k2_relset_1(sK25,sK24,sK26)) ),
    inference(cnf_transformation,[],[f162])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f168,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f63])).

fof(f193,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f105,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f106,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f105])).

fof(f171,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_85,negated_conjecture,
    ( ~ m1_subset_1(X0,sK25)
    | ~ r2_hidden(k4_tarski(X0,sK27),sK26)
    | ~ r2_hidden(sK27,k2_relset_1(sK25,sK24,sK26)) ),
    inference(cnf_transformation,[],[f253])).

cnf(c_46,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f258])).

cnf(c_8360,plain,
    ( ~ r2_hidden(k4_tarski(sK28,sK27),sK26)
    | r2_hidden(sK27,k2_relat_1(sK26)) ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_88,negated_conjecture,
    ( m1_subset_1(sK26,k1_zfmisc_1(k2_zfmisc_1(sK25,sK24))) ),
    inference(cnf_transformation,[],[f250])).

cnf(c_6859,plain,
    ( m1_subset_1(sK26,k1_zfmisc_1(k2_zfmisc_1(sK25,sK24))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_88])).

cnf(c_74,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f237])).

cnf(c_6873,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_74])).

cnf(c_14916,plain,
    ( k2_relset_1(sK25,sK24,sK26) = k2_relat_1(sK26) ),
    inference(superposition,[status(thm)],[c_6859,c_6873])).

cnf(c_86,negated_conjecture,
    ( r2_hidden(k4_tarski(sK28,sK27),sK26)
    | r2_hidden(sK27,k2_relset_1(sK25,sK24,sK26)) ),
    inference(cnf_transformation,[],[f252])).

cnf(c_6861,plain,
    ( r2_hidden(k4_tarski(sK28,sK27),sK26) = iProver_top
    | r2_hidden(sK27,k2_relset_1(sK25,sK24,sK26)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_86])).

cnf(c_15307,plain,
    ( r2_hidden(k4_tarski(sK28,sK27),sK26) = iProver_top
    | r2_hidden(sK27,k2_relat_1(sK26)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14916,c_6861])).

cnf(c_15449,plain,
    ( r2_hidden(k4_tarski(sK28,sK27),sK26)
    | r2_hidden(sK27,k2_relat_1(sK26)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_15307])).

cnf(c_6862,plain,
    ( m1_subset_1(X0,sK25) != iProver_top
    | r2_hidden(k4_tarski(X0,sK27),sK26) != iProver_top
    | r2_hidden(sK27,k2_relset_1(sK25,sK24,sK26)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_85])).

cnf(c_15309,plain,
    ( m1_subset_1(X0,sK25) != iProver_top
    | r2_hidden(k4_tarski(X0,sK27),sK26) != iProver_top
    | r2_hidden(sK27,k2_relat_1(sK26)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14916,c_6862])).

cnf(c_15451,plain,
    ( ~ m1_subset_1(X0,sK25)
    | ~ r2_hidden(k4_tarski(X0,sK27),sK26)
    | ~ r2_hidden(sK27,k2_relat_1(sK26)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_15309])).

cnf(c_15493,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK27),sK26)
    | ~ m1_subset_1(X0,sK25) ),
    inference(global_propositional_subsumption,[status(thm)],[c_85,c_8360,c_15449,c_15451])).

cnf(c_15494,negated_conjecture,
    ( ~ m1_subset_1(X0,sK25)
    | ~ r2_hidden(k4_tarski(X0,sK27),sK26) ),
    inference(renaming,[status(thm)],[c_15493])).

cnf(c_47,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK13(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f259])).

cnf(c_15511,plain,
    ( ~ m1_subset_1(sK13(sK26,sK27),sK25)
    | ~ r2_hidden(sK27,k2_relat_1(sK26)) ),
    inference(resolution,[status(thm)],[c_15494,c_47])).

cnf(c_15617,plain,
    ( ~ m1_subset_1(sK13(sK26,sK27),sK25) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15511,c_8360,c_15449])).

cnf(c_29,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f192])).

cnf(c_15629,plain,
    ( ~ r2_hidden(sK13(sK26,sK27),sK25) ),
    inference(resolution,[status(thm)],[c_15617,c_29])).

cnf(c_33,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f196])).

cnf(c_15039,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(sK25,sK24))
    | ~ r2_hidden(X0,sK26) ),
    inference(resolution,[status(thm)],[c_33,c_88])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f179])).

cnf(c_15612,plain,
    ( ~ r2_hidden(X0,sK26)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_zfmisc_1(sK25,sK24)) ),
    inference(resolution,[status(thm)],[c_15039,c_15])).

cnf(c_48,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f211])).

cnf(c_10393,plain,
    ( v1_xboole_0(k2_relat_1(sK26))
    | ~ v1_xboole_0(sK26) ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f194])).

cnf(c_6910,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_11227,plain,
    ( r1_tarski(sK26,k2_zfmisc_1(sK25,sK24)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6859,c_6910])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f191])).

cnf(c_31,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f195])).

cnf(c_716,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_31])).

cnf(c_717,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_716])).

cnf(c_848,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_28,c_717])).

cnf(c_6853,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_848])).

cnf(c_11603,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK25,sK24)) != iProver_top
    | v1_xboole_0(sK26) = iProver_top ),
    inference(superposition,[status(thm)],[c_11227,c_6853])).

cnf(c_11616,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK25,sK24))
    | v1_xboole_0(sK26) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11603])).

cnf(c_87,negated_conjecture,
    ( m1_subset_1(sK28,sK25)
    | r2_hidden(sK27,k2_relset_1(sK25,sK24,sK26)) ),
    inference(cnf_transformation,[],[f251])).

cnf(c_6860,plain,
    ( m1_subset_1(sK28,sK25) = iProver_top
    | r2_hidden(sK27,k2_relset_1(sK25,sK24,sK26)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_87])).

cnf(c_15308,plain,
    ( m1_subset_1(sK28,sK25) = iProver_top
    | r2_hidden(sK27,k2_relat_1(sK26)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14916,c_6860])).

cnf(c_8361,plain,
    ( r2_hidden(k4_tarski(sK28,sK27),sK26) != iProver_top
    | r2_hidden(sK27,k2_relat_1(sK26)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8360])).

cnf(c_15705,plain,
    ( r2_hidden(sK27,k2_relat_1(sK26)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15308,c_8361,c_15307])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f168])).

cnf(c_6933,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_15711,plain,
    ( v1_xboole_0(k2_relat_1(sK26)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15705,c_6933])).

cnf(c_15732,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK26)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_15711])).

cnf(c_15749,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK25,sK24)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15612,c_10393,c_11616,c_15732])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f193])).

cnf(c_15613,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK25,sK24))
    | ~ r2_hidden(X0,sK26)
    | v1_xboole_0(k2_zfmisc_1(sK25,sK24)) ),
    inference(resolution,[status(thm)],[c_15039,c_30])).

cnf(c_15760,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK25,sK24))
    | ~ r2_hidden(X0,sK26) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_15749,c_15613])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f171])).

cnf(c_16178,plain,
    ( r2_hidden(X0,sK25)
    | ~ r2_hidden(k4_tarski(X0,X1),sK26) ),
    inference(resolution,[status(thm)],[c_15760,c_10])).

cnf(c_16616,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK26))
    | r2_hidden(sK13(sK26,X0),sK25) ),
    inference(resolution,[status(thm)],[c_16178,c_47])).

cnf(c_17745,plain,
    ( ~ r2_hidden(sK27,k2_relat_1(sK26)) ),
    inference(resolution,[status(thm)],[c_15629,c_16616])).

cnf(c_15707,plain,
    ( r2_hidden(sK27,k2_relat_1(sK26)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_15705])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17745,c_15707])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:07:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.65/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/0.97  
% 3.65/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.65/0.97  
% 3.65/0.97  ------  iProver source info
% 3.65/0.97  
% 3.65/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.65/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.65/0.97  git: non_committed_changes: false
% 3.65/0.97  git: last_make_outside_of_git: false
% 3.65/0.97  
% 3.65/0.97  ------ 
% 3.65/0.97  ------ Parsing...
% 3.65/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.65/0.97  
% 3.65/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.65/0.97  
% 3.65/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.65/0.97  
% 3.65/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/0.97  ------ Proving...
% 3.65/0.97  ------ Problem Properties 
% 3.65/0.97  
% 3.65/0.97  
% 3.65/0.97  clauses                                 88
% 3.65/0.97  conjectures                             6
% 3.65/0.97  EPR                                     15
% 3.65/0.97  Horn                                    72
% 3.65/0.97  unary                                   15
% 3.65/0.97  binary                                  31
% 3.65/0.97  lits                                    220
% 3.65/0.97  lits eq                                 34
% 3.65/0.97  fd_pure                                 0
% 3.65/0.97  fd_pseudo                               0
% 3.65/0.97  fd_cond                                 2
% 3.65/0.97  fd_pseudo_cond                          9
% 3.65/0.97  AC symbols                              0
% 3.65/0.97  
% 3.65/0.97  ------ Input Options Time Limit: Unbounded
% 3.65/0.97  
% 3.65/0.97  
% 3.65/0.97  ------ 
% 3.65/0.97  Current options:
% 3.65/0.97  ------ 
% 3.65/0.97  
% 3.65/0.97  
% 3.65/0.97  
% 3.65/0.97  
% 3.65/0.97  ------ Proving...
% 3.65/0.97  
% 3.65/0.97  
% 3.65/0.97  % SZS status Theorem for theBenchmark.p
% 3.65/0.97  
% 3.65/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.65/0.97  
% 3.65/0.97  fof(f48,conjecture,(
% 3.65/0.97    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))))),
% 3.65/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.97  
% 3.65/0.97  fof(f49,negated_conjecture,(
% 3.65/0.97    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))))),
% 3.65/0.97    inference(negated_conjecture,[],[f48])).
% 3.65/0.97  
% 3.65/0.97  fof(f97,plain,(
% 3.65/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <~> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.65/0.97    inference(ennf_transformation,[],[f49])).
% 3.65/0.97  
% 3.65/0.97  fof(f155,plain,(
% 3.65/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.65/0.97    inference(nnf_transformation,[],[f97])).
% 3.65/0.97  
% 3.65/0.97  fof(f156,plain,(
% 3.65/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.65/0.97    inference(rectify,[],[f155])).
% 3.65/0.97  
% 3.65/0.97  fof(f161,plain,(
% 3.65/0.97    ( ! [X2,X3,X1] : (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) => (r2_hidden(k4_tarski(sK28,X3),X2) & m1_subset_1(sK28,X1))) )),
% 3.65/0.97    introduced(choice_axiom,[])).
% 3.65/0.97  
% 3.65/0.97  fof(f160,plain,(
% 3.65/0.97    ( ! [X2,X0,X1] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) => ((! [X4] : (~r2_hidden(k4_tarski(X4,sK27),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(sK27,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,sK27),X2) & m1_subset_1(X5,X1)) | r2_hidden(sK27,k2_relset_1(X1,X0,X2))))) )),
% 3.65/0.97    introduced(choice_axiom,[])).
% 3.65/0.97  
% 3.65/0.97  fof(f159,plain,(
% 3.65/0.97    ( ! [X0,X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),sK26) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,sK26))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),sK26) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,sK26)))) & m1_subset_1(sK26,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))) )),
% 3.65/0.97    introduced(choice_axiom,[])).
% 3.65/0.97  
% 3.65/0.97  fof(f158,plain,(
% 3.65/0.97    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,sK25)) | ~r2_hidden(X3,k2_relset_1(sK25,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,sK25)) | r2_hidden(X3,k2_relset_1(sK25,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK25,X0)))) & ~v1_xboole_0(sK25))) )),
% 3.65/0.97    introduced(choice_axiom,[])).
% 3.65/0.97  
% 3.65/0.97  fof(f157,plain,(
% 3.65/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,sK24,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,sK24,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK24)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK24))),
% 3.65/0.97    introduced(choice_axiom,[])).
% 3.65/0.97  
% 3.65/0.97  fof(f162,plain,(
% 3.65/0.97    ((((! [X4] : (~r2_hidden(k4_tarski(X4,sK27),sK26) | ~m1_subset_1(X4,sK25)) | ~r2_hidden(sK27,k2_relset_1(sK25,sK24,sK26))) & ((r2_hidden(k4_tarski(sK28,sK27),sK26) & m1_subset_1(sK28,sK25)) | r2_hidden(sK27,k2_relset_1(sK25,sK24,sK26)))) & m1_subset_1(sK26,k1_zfmisc_1(k2_zfmisc_1(sK25,sK24)))) & ~v1_xboole_0(sK25)) & ~v1_xboole_0(sK24)),
% 3.65/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK24,sK25,sK26,sK27,sK28])],[f156,f161,f160,f159,f158,f157])).
% 3.65/0.97  
% 3.65/0.97  fof(f253,plain,(
% 3.65/0.97    ( ! [X4] : (~r2_hidden(k4_tarski(X4,sK27),sK26) | ~m1_subset_1(X4,sK25) | ~r2_hidden(sK27,k2_relset_1(sK25,sK24,sK26))) )),
% 3.65/0.97    inference(cnf_transformation,[],[f162])).
% 3.65/0.97  
% 3.65/0.97  fof(f27,axiom,(
% 3.65/0.97    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 3.65/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.97  
% 3.65/0.97  fof(f127,plain,(
% 3.65/0.97    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 3.65/0.97    inference(nnf_transformation,[],[f27])).
% 3.65/0.97  
% 3.65/0.97  fof(f128,plain,(
% 3.65/0.97    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.65/0.97    inference(rectify,[],[f127])).
% 3.65/0.97  
% 3.65/0.97  fof(f131,plain,(
% 3.65/0.97    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK13(X0,X5),X5),X0))),
% 3.65/0.97    introduced(choice_axiom,[])).
% 3.65/0.97  
% 3.65/0.97  fof(f130,plain,(
% 3.65/0.97    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK12(X0,X1),X2),X0))) )),
% 3.65/0.97    introduced(choice_axiom,[])).
% 3.65/0.97  
% 3.65/0.97  fof(f129,plain,(
% 3.65/0.97    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK11(X0,X1)),X0) | ~r2_hidden(sK11(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK11(X0,X1)),X0) | r2_hidden(sK11(X0,X1),X1))))),
% 3.65/0.97    introduced(choice_axiom,[])).
% 3.65/0.97  
% 3.65/0.97  fof(f132,plain,(
% 3.65/0.97    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK11(X0,X1)),X0) | ~r2_hidden(sK11(X0,X1),X1)) & (r2_hidden(k4_tarski(sK12(X0,X1),sK11(X0,X1)),X0) | r2_hidden(sK11(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK13(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.65/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12,sK13])],[f128,f131,f130,f129])).
% 3.65/0.97  
% 3.65/0.97  fof(f208,plain,(
% 3.65/0.97    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 3.65/0.97    inference(cnf_transformation,[],[f132])).
% 3.65/0.97  
% 3.65/0.97  fof(f258,plain,(
% 3.65/0.97    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 3.65/0.97    inference(equality_resolution,[],[f208])).
% 3.65/0.97  
% 3.65/0.97  fof(f250,plain,(
% 3.65/0.97    m1_subset_1(sK26,k1_zfmisc_1(k2_zfmisc_1(sK25,sK24)))),
% 3.65/0.97    inference(cnf_transformation,[],[f162])).
% 3.65/0.97  
% 3.65/0.97  fof(f43,axiom,(
% 3.65/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.65/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.97  
% 3.65/0.97  fof(f90,plain,(
% 3.65/0.97    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.65/0.97    inference(ennf_transformation,[],[f43])).
% 3.65/0.97  
% 3.65/0.97  fof(f237,plain,(
% 3.65/0.97    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.65/0.97    inference(cnf_transformation,[],[f90])).
% 3.65/0.97  
% 3.65/0.97  fof(f252,plain,(
% 3.65/0.97    r2_hidden(k4_tarski(sK28,sK27),sK26) | r2_hidden(sK27,k2_relset_1(sK25,sK24,sK26))),
% 3.65/0.97    inference(cnf_transformation,[],[f162])).
% 3.65/0.97  
% 3.65/0.97  fof(f207,plain,(
% 3.65/0.97    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK13(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 3.65/0.97    inference(cnf_transformation,[],[f132])).
% 3.65/0.97  
% 3.65/0.97  fof(f259,plain,(
% 3.65/0.97    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK13(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 3.65/0.97    inference(equality_resolution,[],[f207])).
% 3.65/0.97  
% 3.65/0.97  fof(f20,axiom,(
% 3.65/0.97    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.65/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.97  
% 3.65/0.97  fof(f62,plain,(
% 3.65/0.97    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.65/0.97    inference(ennf_transformation,[],[f20])).
% 3.65/0.97  
% 3.65/0.97  fof(f192,plain,(
% 3.65/0.97    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.65/0.97    inference(cnf_transformation,[],[f62])).
% 3.65/0.97  
% 3.65/0.97  fof(f23,axiom,(
% 3.65/0.97    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.65/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.97  
% 3.65/0.97  fof(f65,plain,(
% 3.65/0.97    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.65/0.97    inference(ennf_transformation,[],[f23])).
% 3.65/0.97  
% 3.65/0.97  fof(f66,plain,(
% 3.65/0.97    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.65/0.97    inference(flattening,[],[f65])).
% 3.65/0.97  
% 3.65/0.97  fof(f196,plain,(
% 3.65/0.97    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.65/0.97    inference(cnf_transformation,[],[f66])).
% 3.65/0.97  
% 3.65/0.97  fof(f10,axiom,(
% 3.65/0.97    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.65/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.97  
% 3.65/0.97  fof(f53,plain,(
% 3.65/0.97    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.65/0.97    inference(ennf_transformation,[],[f10])).
% 3.65/0.97  
% 3.65/0.97  fof(f109,plain,(
% 3.65/0.97    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.65/0.97    inference(nnf_transformation,[],[f53])).
% 3.65/0.97  
% 3.65/0.97  fof(f179,plain,(
% 3.65/0.97    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.65/0.97    inference(cnf_transformation,[],[f109])).
% 3.65/0.97  
% 3.65/0.97  fof(f28,axiom,(
% 3.65/0.97    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 3.65/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.97  
% 3.65/0.97  fof(f70,plain,(
% 3.65/0.97    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 3.65/0.97    inference(ennf_transformation,[],[f28])).
% 3.65/0.97  
% 3.65/0.97  fof(f211,plain,(
% 3.65/0.97    ( ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.65/0.97    inference(cnf_transformation,[],[f70])).
% 3.65/0.97  
% 3.65/0.97  fof(f22,axiom,(
% 3.65/0.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.65/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.97  
% 3.65/0.97  fof(f116,plain,(
% 3.65/0.97    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.65/0.97    inference(nnf_transformation,[],[f22])).
% 3.65/0.97  
% 3.65/0.97  fof(f194,plain,(
% 3.65/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.65/0.97    inference(cnf_transformation,[],[f116])).
% 3.65/0.97  
% 3.65/0.97  fof(f19,axiom,(
% 3.65/0.97    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.65/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.97  
% 3.65/0.97  fof(f61,plain,(
% 3.65/0.97    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.65/0.97    inference(ennf_transformation,[],[f19])).
% 3.65/0.97  
% 3.65/0.97  fof(f191,plain,(
% 3.65/0.97    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.65/0.97    inference(cnf_transformation,[],[f61])).
% 3.65/0.97  
% 3.65/0.97  fof(f195,plain,(
% 3.65/0.97    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.65/0.97    inference(cnf_transformation,[],[f116])).
% 3.65/0.97  
% 3.65/0.97  fof(f251,plain,(
% 3.65/0.97    m1_subset_1(sK28,sK25) | r2_hidden(sK27,k2_relset_1(sK25,sK24,sK26))),
% 3.65/0.97    inference(cnf_transformation,[],[f162])).
% 3.65/0.97  
% 3.65/0.97  fof(f5,axiom,(
% 3.65/0.97    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 3.65/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.97  
% 3.65/0.97  fof(f51,plain,(
% 3.65/0.97    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 3.65/0.97    inference(ennf_transformation,[],[f5])).
% 3.65/0.97  
% 3.65/0.97  fof(f168,plain,(
% 3.65/0.97    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 3.65/0.97    inference(cnf_transformation,[],[f51])).
% 3.65/0.97  
% 3.65/0.97  fof(f21,axiom,(
% 3.65/0.97    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.65/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.97  
% 3.65/0.97  fof(f63,plain,(
% 3.65/0.97    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.65/0.97    inference(ennf_transformation,[],[f21])).
% 3.65/0.97  
% 3.65/0.97  fof(f64,plain,(
% 3.65/0.97    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.65/0.97    inference(flattening,[],[f63])).
% 3.65/0.97  
% 3.65/0.97  fof(f193,plain,(
% 3.65/0.97    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.65/0.97    inference(cnf_transformation,[],[f64])).
% 3.65/0.97  
% 3.65/0.97  fof(f7,axiom,(
% 3.65/0.97    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 3.65/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.97  
% 3.65/0.97  fof(f105,plain,(
% 3.65/0.97    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.65/0.97    inference(nnf_transformation,[],[f7])).
% 3.65/0.97  
% 3.65/0.97  fof(f106,plain,(
% 3.65/0.97    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.65/0.97    inference(flattening,[],[f105])).
% 3.65/0.97  
% 3.65/0.97  fof(f171,plain,(
% 3.65/0.97    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.65/0.97    inference(cnf_transformation,[],[f106])).
% 3.65/0.97  
% 3.65/0.97  cnf(c_85,negated_conjecture,
% 3.65/0.97      ( ~ m1_subset_1(X0,sK25)
% 3.65/0.97      | ~ r2_hidden(k4_tarski(X0,sK27),sK26)
% 3.65/0.97      | ~ r2_hidden(sK27,k2_relset_1(sK25,sK24,sK26)) ),
% 3.65/0.97      inference(cnf_transformation,[],[f253]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_46,plain,
% 3.65/0.97      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 3.65/0.97      inference(cnf_transformation,[],[f258]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_8360,plain,
% 3.65/0.97      ( ~ r2_hidden(k4_tarski(sK28,sK27),sK26)
% 3.65/0.97      | r2_hidden(sK27,k2_relat_1(sK26)) ),
% 3.65/0.97      inference(instantiation,[status(thm)],[c_46]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_88,negated_conjecture,
% 3.65/0.97      ( m1_subset_1(sK26,k1_zfmisc_1(k2_zfmisc_1(sK25,sK24))) ),
% 3.65/0.97      inference(cnf_transformation,[],[f250]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_6859,plain,
% 3.65/0.97      ( m1_subset_1(sK26,k1_zfmisc_1(k2_zfmisc_1(sK25,sK24))) = iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_88]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_74,plain,
% 3.65/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/0.97      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.65/0.97      inference(cnf_transformation,[],[f237]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_6873,plain,
% 3.65/0.97      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.65/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_74]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_14916,plain,
% 3.65/0.97      ( k2_relset_1(sK25,sK24,sK26) = k2_relat_1(sK26) ),
% 3.65/0.97      inference(superposition,[status(thm)],[c_6859,c_6873]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_86,negated_conjecture,
% 3.65/0.97      ( r2_hidden(k4_tarski(sK28,sK27),sK26)
% 3.65/0.97      | r2_hidden(sK27,k2_relset_1(sK25,sK24,sK26)) ),
% 3.65/0.97      inference(cnf_transformation,[],[f252]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_6861,plain,
% 3.65/0.97      ( r2_hidden(k4_tarski(sK28,sK27),sK26) = iProver_top
% 3.65/0.97      | r2_hidden(sK27,k2_relset_1(sK25,sK24,sK26)) = iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_86]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_15307,plain,
% 3.65/0.97      ( r2_hidden(k4_tarski(sK28,sK27),sK26) = iProver_top
% 3.65/0.97      | r2_hidden(sK27,k2_relat_1(sK26)) = iProver_top ),
% 3.65/0.97      inference(demodulation,[status(thm)],[c_14916,c_6861]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_15449,plain,
% 3.65/0.97      ( r2_hidden(k4_tarski(sK28,sK27),sK26)
% 3.65/0.97      | r2_hidden(sK27,k2_relat_1(sK26)) ),
% 3.65/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_15307]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_6862,plain,
% 3.65/0.97      ( m1_subset_1(X0,sK25) != iProver_top
% 3.65/0.97      | r2_hidden(k4_tarski(X0,sK27),sK26) != iProver_top
% 3.65/0.97      | r2_hidden(sK27,k2_relset_1(sK25,sK24,sK26)) != iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_85]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_15309,plain,
% 3.65/0.97      ( m1_subset_1(X0,sK25) != iProver_top
% 3.65/0.97      | r2_hidden(k4_tarski(X0,sK27),sK26) != iProver_top
% 3.65/0.97      | r2_hidden(sK27,k2_relat_1(sK26)) != iProver_top ),
% 3.65/0.97      inference(demodulation,[status(thm)],[c_14916,c_6862]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_15451,plain,
% 3.65/0.97      ( ~ m1_subset_1(X0,sK25)
% 3.65/0.97      | ~ r2_hidden(k4_tarski(X0,sK27),sK26)
% 3.65/0.97      | ~ r2_hidden(sK27,k2_relat_1(sK26)) ),
% 3.65/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_15309]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_15493,plain,
% 3.65/0.97      ( ~ r2_hidden(k4_tarski(X0,sK27),sK26) | ~ m1_subset_1(X0,sK25) ),
% 3.65/0.97      inference(global_propositional_subsumption,
% 3.65/0.97                [status(thm)],
% 3.65/0.97                [c_85,c_8360,c_15449,c_15451]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_15494,negated_conjecture,
% 3.65/0.97      ( ~ m1_subset_1(X0,sK25) | ~ r2_hidden(k4_tarski(X0,sK27),sK26) ),
% 3.65/0.97      inference(renaming,[status(thm)],[c_15493]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_47,plain,
% 3.65/0.97      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.65/0.97      | r2_hidden(k4_tarski(sK13(X1,X0),X0),X1) ),
% 3.65/0.97      inference(cnf_transformation,[],[f259]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_15511,plain,
% 3.65/0.97      ( ~ m1_subset_1(sK13(sK26,sK27),sK25)
% 3.65/0.97      | ~ r2_hidden(sK27,k2_relat_1(sK26)) ),
% 3.65/0.97      inference(resolution,[status(thm)],[c_15494,c_47]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_15617,plain,
% 3.65/0.97      ( ~ m1_subset_1(sK13(sK26,sK27),sK25) ),
% 3.65/0.97      inference(global_propositional_subsumption,
% 3.65/0.97                [status(thm)],
% 3.65/0.97                [c_15511,c_8360,c_15449]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_29,plain,
% 3.65/0.97      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.65/0.97      inference(cnf_transformation,[],[f192]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_15629,plain,
% 3.65/0.97      ( ~ r2_hidden(sK13(sK26,sK27),sK25) ),
% 3.65/0.97      inference(resolution,[status(thm)],[c_15617,c_29]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_33,plain,
% 3.65/0.97      ( m1_subset_1(X0,X1)
% 3.65/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.65/0.97      | ~ r2_hidden(X0,X2) ),
% 3.65/0.97      inference(cnf_transformation,[],[f196]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_15039,plain,
% 3.65/0.97      ( m1_subset_1(X0,k2_zfmisc_1(sK25,sK24)) | ~ r2_hidden(X0,sK26) ),
% 3.65/0.97      inference(resolution,[status(thm)],[c_33,c_88]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_15,plain,
% 3.65/0.97      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 3.65/0.97      inference(cnf_transformation,[],[f179]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_15612,plain,
% 3.65/0.97      ( ~ r2_hidden(X0,sK26)
% 3.65/0.97      | v1_xboole_0(X0)
% 3.65/0.97      | ~ v1_xboole_0(k2_zfmisc_1(sK25,sK24)) ),
% 3.65/0.97      inference(resolution,[status(thm)],[c_15039,c_15]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_48,plain,
% 3.65/0.97      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_relat_1(X0)) ),
% 3.65/0.97      inference(cnf_transformation,[],[f211]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_10393,plain,
% 3.65/0.97      ( v1_xboole_0(k2_relat_1(sK26)) | ~ v1_xboole_0(sK26) ),
% 3.65/0.97      inference(instantiation,[status(thm)],[c_48]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_32,plain,
% 3.65/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.65/0.97      inference(cnf_transformation,[],[f194]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_6910,plain,
% 3.65/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.65/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_11227,plain,
% 3.65/0.97      ( r1_tarski(sK26,k2_zfmisc_1(sK25,sK24)) = iProver_top ),
% 3.65/0.97      inference(superposition,[status(thm)],[c_6859,c_6910]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_28,plain,
% 3.65/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.65/0.97      | ~ v1_xboole_0(X1)
% 3.65/0.97      | v1_xboole_0(X0) ),
% 3.65/0.97      inference(cnf_transformation,[],[f191]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_31,plain,
% 3.65/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.65/0.97      inference(cnf_transformation,[],[f195]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_716,plain,
% 3.65/0.97      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.65/0.97      inference(prop_impl,[status(thm)],[c_31]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_717,plain,
% 3.65/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.65/0.97      inference(renaming,[status(thm)],[c_716]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_848,plain,
% 3.65/0.97      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 3.65/0.97      inference(bin_hyper_res,[status(thm)],[c_28,c_717]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_6853,plain,
% 3.65/0.97      ( r1_tarski(X0,X1) != iProver_top
% 3.65/0.97      | v1_xboole_0(X1) != iProver_top
% 3.65/0.97      | v1_xboole_0(X0) = iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_848]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_11603,plain,
% 3.65/0.97      ( v1_xboole_0(k2_zfmisc_1(sK25,sK24)) != iProver_top
% 3.65/0.97      | v1_xboole_0(sK26) = iProver_top ),
% 3.65/0.97      inference(superposition,[status(thm)],[c_11227,c_6853]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_11616,plain,
% 3.65/0.97      ( ~ v1_xboole_0(k2_zfmisc_1(sK25,sK24)) | v1_xboole_0(sK26) ),
% 3.65/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_11603]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_87,negated_conjecture,
% 3.65/0.97      ( m1_subset_1(sK28,sK25)
% 3.65/0.97      | r2_hidden(sK27,k2_relset_1(sK25,sK24,sK26)) ),
% 3.65/0.97      inference(cnf_transformation,[],[f251]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_6860,plain,
% 3.65/0.97      ( m1_subset_1(sK28,sK25) = iProver_top
% 3.65/0.97      | r2_hidden(sK27,k2_relset_1(sK25,sK24,sK26)) = iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_87]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_15308,plain,
% 3.65/0.97      ( m1_subset_1(sK28,sK25) = iProver_top
% 3.65/0.97      | r2_hidden(sK27,k2_relat_1(sK26)) = iProver_top ),
% 3.65/0.97      inference(demodulation,[status(thm)],[c_14916,c_6860]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_8361,plain,
% 3.65/0.97      ( r2_hidden(k4_tarski(sK28,sK27),sK26) != iProver_top
% 3.65/0.97      | r2_hidden(sK27,k2_relat_1(sK26)) = iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_8360]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_15705,plain,
% 3.65/0.97      ( r2_hidden(sK27,k2_relat_1(sK26)) = iProver_top ),
% 3.65/0.97      inference(global_propositional_subsumption,
% 3.65/0.97                [status(thm)],
% 3.65/0.97                [c_15308,c_8361,c_15307]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_5,plain,
% 3.65/0.97      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.65/0.97      inference(cnf_transformation,[],[f168]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_6933,plain,
% 3.65/0.97      ( r2_hidden(X0,X1) != iProver_top
% 3.65/0.97      | v1_xboole_0(X1) != iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_15711,plain,
% 3.65/0.97      ( v1_xboole_0(k2_relat_1(sK26)) != iProver_top ),
% 3.65/0.97      inference(superposition,[status(thm)],[c_15705,c_6933]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_15732,plain,
% 3.65/0.97      ( ~ v1_xboole_0(k2_relat_1(sK26)) ),
% 3.65/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_15711]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_15749,plain,
% 3.65/0.97      ( ~ v1_xboole_0(k2_zfmisc_1(sK25,sK24)) ),
% 3.65/0.97      inference(global_propositional_subsumption,
% 3.65/0.97                [status(thm)],
% 3.65/0.97                [c_15612,c_10393,c_11616,c_15732]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_30,plain,
% 3.65/0.97      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.65/0.97      inference(cnf_transformation,[],[f193]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_15613,plain,
% 3.65/0.97      ( r2_hidden(X0,k2_zfmisc_1(sK25,sK24))
% 3.65/0.97      | ~ r2_hidden(X0,sK26)
% 3.65/0.97      | v1_xboole_0(k2_zfmisc_1(sK25,sK24)) ),
% 3.65/0.97      inference(resolution,[status(thm)],[c_15039,c_30]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_15760,plain,
% 3.65/0.97      ( r2_hidden(X0,k2_zfmisc_1(sK25,sK24)) | ~ r2_hidden(X0,sK26) ),
% 3.65/0.97      inference(backward_subsumption_resolution,
% 3.65/0.97                [status(thm)],
% 3.65/0.97                [c_15749,c_15613]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_10,plain,
% 3.65/0.97      ( r2_hidden(X0,X1)
% 3.65/0.97      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 3.65/0.97      inference(cnf_transformation,[],[f171]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_16178,plain,
% 3.65/0.97      ( r2_hidden(X0,sK25) | ~ r2_hidden(k4_tarski(X0,X1),sK26) ),
% 3.65/0.97      inference(resolution,[status(thm)],[c_15760,c_10]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_16616,plain,
% 3.65/0.97      ( ~ r2_hidden(X0,k2_relat_1(sK26))
% 3.65/0.97      | r2_hidden(sK13(sK26,X0),sK25) ),
% 3.65/0.97      inference(resolution,[status(thm)],[c_16178,c_47]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_17745,plain,
% 3.65/0.97      ( ~ r2_hidden(sK27,k2_relat_1(sK26)) ),
% 3.65/0.97      inference(resolution,[status(thm)],[c_15629,c_16616]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_15707,plain,
% 3.65/0.97      ( r2_hidden(sK27,k2_relat_1(sK26)) ),
% 3.65/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_15705]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(contradiction,plain,
% 3.65/0.97      ( $false ),
% 3.65/0.97      inference(minisat,[status(thm)],[c_17745,c_15707]) ).
% 3.65/0.97  
% 3.65/0.97  
% 3.65/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.65/0.97  
% 3.65/0.97  ------                               Statistics
% 3.65/0.97  
% 3.65/0.97  ------ Selected
% 3.65/0.97  
% 3.65/0.97  total_time:                             0.374
% 3.65/0.97  
%------------------------------------------------------------------------------
