%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:56 EST 2020

% Result     : Theorem 11.25s
% Output     : CNFRefutation 11.25s
% Verified   : 
% Statistics : Number of formulae       :  185 (1088 expanded)
%              Number of clauses        :   86 ( 225 expanded)
%              Number of leaves         :   32 ( 276 expanded)
%              Depth                    :   24
%              Number of atoms          :  517 (3354 expanded)
%              Number of equality atoms :  195 (1351 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f26])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f56])).

fof(f94,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f9,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f48])).

fof(f52,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK3(X0,X5),X0)
        & r2_hidden(X5,sK3(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(X2,sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK1(X0,X1),X3) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK1(X0,X1),X4) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK1(X0,X1),X3) )
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( ( r2_hidden(sK2(X0,X1),X0)
              & r2_hidden(sK1(X0,X1),sK2(X0,X1)) )
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK3(X0,X5),X0)
                & r2_hidden(X5,sK3(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f49,f52,f51,f50])).

fof(f70,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f115,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f70])).

fof(f71,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f114,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f71])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f42,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f43,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f59,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK7,sK5),sK6)
      & k1_xboole_0 != sK6
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6)))
      & v1_funct_2(sK7,k1_tarski(sK5),sK6)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ~ r2_hidden(k1_funct_1(sK7,sK5),sK6)
    & k1_xboole_0 != sK6
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6)))
    & v1_funct_2(sK7,k1_tarski(sK5),sK6)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f43,f59])).

fof(f103,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6))) ),
    inference(cnf_transformation,[],[f60])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f106,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f67,f68])).

fof(f107,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f66,f106])).

fof(f108,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f65,f107])).

fof(f112,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK6))) ),
    inference(definition_unfolding,[],[f103,f108])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f40])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f102,plain,(
    v1_funct_2(sK7,k1_tarski(sK5),sK6) ),
    inference(cnf_transformation,[],[f60])).

fof(f113,plain,(
    v1_funct_2(sK7,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK6) ),
    inference(definition_unfolding,[],[f102,f108])).

fof(f104,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f60])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X1),X2)) ) ),
    inference(definition_unfolding,[],[f92,f108])).

fof(f101,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f60])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f15,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f46])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f105,plain,(
    ~ r2_hidden(k1_funct_1(sK7,sK5),sK6) ),
    inference(cnf_transformation,[],[f60])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f109,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(definition_unfolding,[],[f75,f108])).

fof(f16,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_29,plain,
    ( r2_hidden(sK4(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1252,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK4(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_11,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(sK3(X1,X0),X1) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1268,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1269,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3654,plain,
    ( r2_hidden(X0,sK3(X1,X2)) != iProver_top
    | r2_hidden(X2,k3_tarski(X1)) != iProver_top
    | r2_hidden(X0,k3_tarski(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1268,c_1269])).

cnf(c_15371,plain,
    ( sK3(X0,X1) = k1_xboole_0
    | r2_hidden(X1,k3_tarski(X0)) != iProver_top
    | r2_hidden(sK4(sK3(X0,X1)),k3_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1252,c_3654])).

cnf(c_40419,plain,
    ( sK3(k1_zfmisc_1(X0),X1) = k1_xboole_0
    | r2_hidden(X1,k3_tarski(k1_zfmisc_1(X0))) != iProver_top
    | r2_hidden(sK4(sK3(k1_zfmisc_1(X0),X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_15371])).

cnf(c_40485,plain,
    ( sK3(k1_zfmisc_1(X0),X1) = k1_xboole_0
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(sK4(sK3(k1_zfmisc_1(X0),X1)),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_40419,c_11])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK6))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1244,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_35,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1246,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_1988,plain,
    ( k1_relset_1(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK6,sK7) = k3_enumset1(sK5,sK5,sK5,sK5,sK5)
    | sK6 = k1_xboole_0
    | v1_funct_2(sK7,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1244,c_1246])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK7,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK6) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_37,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1676,plain,
    ( ~ v1_funct_2(X0,X1,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK6)))
    | k1_relset_1(X1,sK6,X0) = X1
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_1798,plain,
    ( ~ v1_funct_2(sK7,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK6)))
    | k1_relset_1(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK6,sK7) = k3_enumset1(sK5,sK5,sK5,sK5,sK5)
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_1676])).

cnf(c_5017,plain,
    ( k1_relset_1(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK6,sK7) = k3_enumset1(sK5,sK5,sK5,sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1988,c_39,c_38,c_37,c_1798])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1257,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2735,plain,
    ( k1_relset_1(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK6,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1244,c_1257])).

cnf(c_5019,plain,
    ( k3_enumset1(sK5,sK5,sK5,sK5,sK5) = k1_relat_1(sK7) ),
    inference(light_normalisation,[status(thm)],[c_5017,c_2735])).

cnf(c_5023,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK6))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5019,c_1244])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1265,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5324,plain,
    ( r2_hidden(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK6))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK6))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5023,c_1265])).

cnf(c_12,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1266,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7222,plain,
    ( r2_hidden(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK6))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5324,c_1266])).

cnf(c_7224,plain,
    ( r2_hidden(X0,k3_tarski(k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK6)))) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_7222,c_1269])).

cnf(c_7232,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK7),sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7224,c_11])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X1),X2))
    | k1_mcart_1(X0) = X1 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1253,plain,
    ( k1_mcart_1(X0) = X1
    | r2_hidden(X0,k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5038,plain,
    ( k1_mcart_1(X0) = sK5
    | r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK7),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5019,c_1253])).

cnf(c_7491,plain,
    ( k1_mcart_1(X0) = sK5
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_7232,c_5038])).

cnf(c_40527,plain,
    ( sK3(k1_zfmisc_1(sK7),X0) = k1_xboole_0
    | k1_mcart_1(sK4(sK3(k1_zfmisc_1(sK7),X0))) = sK5
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_40485,c_7491])).

cnf(c_41256,plain,
    ( sK3(k1_zfmisc_1(sK7),sK4(sK7)) = k1_xboole_0
    | k1_mcart_1(sK4(sK3(k1_zfmisc_1(sK7),sK4(sK7)))) = sK5
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1252,c_40527])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_23,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1592,plain,
    ( v5_relat_1(sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK6))) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_18,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1726,plain,
    ( ~ v5_relat_1(sK7,sK6)
    | r1_tarski(k2_relat_1(sK7),sK6)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1751,plain,
    ( r2_hidden(sK4(sK7),sK7)
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_423,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1792,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_423])).

cnf(c_424,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2136,plain,
    ( X0 != X1
    | sK7 != X1
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_424])).

cnf(c_3754,plain,
    ( X0 != sK7
    | sK7 = X0
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2136])).

cnf(c_3755,plain,
    ( sK7 != sK7
    | sK7 = k1_xboole_0
    | k1_xboole_0 != sK7 ),
    inference(instantiation,[status(thm)],[c_3754])).

cnf(c_7619,plain,
    ( k1_mcart_1(sK4(sK7)) = sK5
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1252,c_7491])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1255,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7490,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(k1_mcart_1(X0),k1_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7232,c_1255])).

cnf(c_8218,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(sK4(sK7),sK7) != iProver_top
    | r2_hidden(sK5,k1_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7619,c_7490])).

cnf(c_8246,plain,
    ( ~ r2_hidden(sK4(sK7),sK7)
    | r2_hidden(sK5,k1_relat_1(sK7))
    | sK7 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8218])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_14,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_257,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_258,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_257])).

cnf(c_332,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_16,c_258])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1646,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK6)) ),
    inference(resolution,[status(thm)],[c_15,c_38])).

cnf(c_12478,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK6))
    | v1_relat_1(sK7) ),
    inference(resolution,[status(thm)],[c_332,c_1646])).

cnf(c_19,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_12500,plain,
    ( v1_relat_1(sK7) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12478,c_19])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1259,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1273,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4133,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),X2) = iProver_top
    | r1_tarski(k2_relat_1(X1),X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1259,c_1273])).

cnf(c_36,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK7,sK5),sK6) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1245,plain,
    ( r2_hidden(k1_funct_1(sK7,sK5),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_39878,plain,
    ( r2_hidden(sK5,k1_relat_1(sK7)) != iProver_top
    | r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4133,c_1245])).

cnf(c_40229,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK7))
    | ~ r1_tarski(k2_relat_1(sK7),sK6)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_39878])).

cnf(c_42899,plain,
    ( sK7 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_41256,c_40,c_38,c_1592,c_1726,c_1751,c_1792,c_3755,c_8246,c_12500,c_40229])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_10,plain,
    ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1610,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_10])).

cnf(c_5036,plain,
    ( k1_relat_1(sK7) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5019,c_1610])).

cnf(c_42959,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_42899,c_5036])).

cnf(c_21,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_42978,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_42959,c_21])).

cnf(c_42979,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_42978])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:01:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.25/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.25/1.99  
% 11.25/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.25/1.99  
% 11.25/1.99  ------  iProver source info
% 11.25/1.99  
% 11.25/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.25/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.25/1.99  git: non_committed_changes: false
% 11.25/1.99  git: last_make_outside_of_git: false
% 11.25/1.99  
% 11.25/1.99  ------ 
% 11.25/1.99  
% 11.25/1.99  ------ Input Options
% 11.25/1.99  
% 11.25/1.99  --out_options                           all
% 11.25/1.99  --tptp_safe_out                         true
% 11.25/1.99  --problem_path                          ""
% 11.25/1.99  --include_path                          ""
% 11.25/1.99  --clausifier                            res/vclausify_rel
% 11.25/1.99  --clausifier_options                    --mode clausify
% 11.25/1.99  --stdin                                 false
% 11.25/1.99  --stats_out                             sel
% 11.25/1.99  
% 11.25/1.99  ------ General Options
% 11.25/1.99  
% 11.25/1.99  --fof                                   false
% 11.25/1.99  --time_out_real                         604.99
% 11.25/1.99  --time_out_virtual                      -1.
% 11.25/1.99  --symbol_type_check                     false
% 11.25/1.99  --clausify_out                          false
% 11.25/1.99  --sig_cnt_out                           false
% 11.25/1.99  --trig_cnt_out                          false
% 11.25/1.99  --trig_cnt_out_tolerance                1.
% 11.25/1.99  --trig_cnt_out_sk_spl                   false
% 11.25/1.99  --abstr_cl_out                          false
% 11.25/1.99  
% 11.25/1.99  ------ Global Options
% 11.25/1.99  
% 11.25/1.99  --schedule                              none
% 11.25/1.99  --add_important_lit                     false
% 11.25/1.99  --prop_solver_per_cl                    1000
% 11.25/1.99  --min_unsat_core                        false
% 11.25/1.99  --soft_assumptions                      false
% 11.25/1.99  --soft_lemma_size                       3
% 11.25/1.99  --prop_impl_unit_size                   0
% 11.25/1.99  --prop_impl_unit                        []
% 11.25/1.99  --share_sel_clauses                     true
% 11.25/1.99  --reset_solvers                         false
% 11.25/1.99  --bc_imp_inh                            [conj_cone]
% 11.25/1.99  --conj_cone_tolerance                   3.
% 11.25/1.99  --extra_neg_conj                        none
% 11.25/1.99  --large_theory_mode                     true
% 11.25/1.99  --prolific_symb_bound                   200
% 11.25/1.99  --lt_threshold                          2000
% 11.25/1.99  --clause_weak_htbl                      true
% 11.25/1.99  --gc_record_bc_elim                     false
% 11.25/1.99  
% 11.25/1.99  ------ Preprocessing Options
% 11.25/1.99  
% 11.25/1.99  --preprocessing_flag                    true
% 11.25/1.99  --time_out_prep_mult                    0.1
% 11.25/1.99  --splitting_mode                        input
% 11.25/1.99  --splitting_grd                         true
% 11.25/1.99  --splitting_cvd                         false
% 11.25/1.99  --splitting_cvd_svl                     false
% 11.25/1.99  --splitting_nvd                         32
% 11.25/1.99  --sub_typing                            true
% 11.25/1.99  --prep_gs_sim                           false
% 11.25/1.99  --prep_unflatten                        true
% 11.25/1.99  --prep_res_sim                          true
% 11.25/1.99  --prep_upred                            true
% 11.25/1.99  --prep_sem_filter                       exhaustive
% 11.25/1.99  --prep_sem_filter_out                   false
% 11.25/1.99  --pred_elim                             false
% 11.25/1.99  --res_sim_input                         true
% 11.25/1.99  --eq_ax_congr_red                       true
% 11.25/1.99  --pure_diseq_elim                       true
% 11.25/1.99  --brand_transform                       false
% 11.25/1.99  --non_eq_to_eq                          false
% 11.25/1.99  --prep_def_merge                        true
% 11.25/1.99  --prep_def_merge_prop_impl              false
% 11.25/1.99  --prep_def_merge_mbd                    true
% 11.25/1.99  --prep_def_merge_tr_red                 false
% 11.25/1.99  --prep_def_merge_tr_cl                  false
% 11.25/1.99  --smt_preprocessing                     true
% 11.25/1.99  --smt_ac_axioms                         fast
% 11.25/1.99  --preprocessed_out                      false
% 11.25/1.99  --preprocessed_stats                    false
% 11.25/1.99  
% 11.25/1.99  ------ Abstraction refinement Options
% 11.25/1.99  
% 11.25/1.99  --abstr_ref                             []
% 11.25/1.99  --abstr_ref_prep                        false
% 11.25/1.99  --abstr_ref_until_sat                   false
% 11.25/1.99  --abstr_ref_sig_restrict                funpre
% 11.25/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.25/1.99  --abstr_ref_under                       []
% 11.25/1.99  
% 11.25/1.99  ------ SAT Options
% 11.25/1.99  
% 11.25/1.99  --sat_mode                              false
% 11.25/1.99  --sat_fm_restart_options                ""
% 11.25/1.99  --sat_gr_def                            false
% 11.25/1.99  --sat_epr_types                         true
% 11.25/1.99  --sat_non_cyclic_types                  false
% 11.25/1.99  --sat_finite_models                     false
% 11.25/1.99  --sat_fm_lemmas                         false
% 11.25/1.99  --sat_fm_prep                           false
% 11.25/1.99  --sat_fm_uc_incr                        true
% 11.25/1.99  --sat_out_model                         small
% 11.25/1.99  --sat_out_clauses                       false
% 11.25/1.99  
% 11.25/1.99  ------ QBF Options
% 11.25/1.99  
% 11.25/1.99  --qbf_mode                              false
% 11.25/1.99  --qbf_elim_univ                         false
% 11.25/1.99  --qbf_dom_inst                          none
% 11.25/1.99  --qbf_dom_pre_inst                      false
% 11.25/1.99  --qbf_sk_in                             false
% 11.25/1.99  --qbf_pred_elim                         true
% 11.25/1.99  --qbf_split                             512
% 11.25/1.99  
% 11.25/1.99  ------ BMC1 Options
% 11.25/1.99  
% 11.25/1.99  --bmc1_incremental                      false
% 11.25/1.99  --bmc1_axioms                           reachable_all
% 11.25/1.99  --bmc1_min_bound                        0
% 11.25/1.99  --bmc1_max_bound                        -1
% 11.25/1.99  --bmc1_max_bound_default                -1
% 11.25/1.99  --bmc1_symbol_reachability              true
% 11.25/1.99  --bmc1_property_lemmas                  false
% 11.25/1.99  --bmc1_k_induction                      false
% 11.25/1.99  --bmc1_non_equiv_states                 false
% 11.25/1.99  --bmc1_deadlock                         false
% 11.25/1.99  --bmc1_ucm                              false
% 11.25/1.99  --bmc1_add_unsat_core                   none
% 11.25/1.99  --bmc1_unsat_core_children              false
% 11.25/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.25/1.99  --bmc1_out_stat                         full
% 11.25/1.99  --bmc1_ground_init                      false
% 11.25/1.99  --bmc1_pre_inst_next_state              false
% 11.25/1.99  --bmc1_pre_inst_state                   false
% 11.25/1.99  --bmc1_pre_inst_reach_state             false
% 11.25/1.99  --bmc1_out_unsat_core                   false
% 11.25/1.99  --bmc1_aig_witness_out                  false
% 11.25/1.99  --bmc1_verbose                          false
% 11.25/1.99  --bmc1_dump_clauses_tptp                false
% 11.25/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.25/1.99  --bmc1_dump_file                        -
% 11.25/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.25/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.25/1.99  --bmc1_ucm_extend_mode                  1
% 11.25/1.99  --bmc1_ucm_init_mode                    2
% 11.25/1.99  --bmc1_ucm_cone_mode                    none
% 11.25/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.25/1.99  --bmc1_ucm_relax_model                  4
% 11.25/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.25/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.25/1.99  --bmc1_ucm_layered_model                none
% 11.25/1.99  --bmc1_ucm_max_lemma_size               10
% 11.25/1.99  
% 11.25/1.99  ------ AIG Options
% 11.25/1.99  
% 11.25/1.99  --aig_mode                              false
% 11.25/1.99  
% 11.25/1.99  ------ Instantiation Options
% 11.25/1.99  
% 11.25/1.99  --instantiation_flag                    true
% 11.25/1.99  --inst_sos_flag                         false
% 11.25/1.99  --inst_sos_phase                        true
% 11.25/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.25/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.25/1.99  --inst_lit_sel_side                     num_symb
% 11.25/1.99  --inst_solver_per_active                1400
% 11.25/1.99  --inst_solver_calls_frac                1.
% 11.25/1.99  --inst_passive_queue_type               priority_queues
% 11.25/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.25/1.99  --inst_passive_queues_freq              [25;2]
% 11.25/1.99  --inst_dismatching                      true
% 11.25/1.99  --inst_eager_unprocessed_to_passive     true
% 11.25/1.99  --inst_prop_sim_given                   true
% 11.25/1.99  --inst_prop_sim_new                     false
% 11.25/1.99  --inst_subs_new                         false
% 11.25/1.99  --inst_eq_res_simp                      false
% 11.25/1.99  --inst_subs_given                       false
% 11.25/1.99  --inst_orphan_elimination               true
% 11.25/1.99  --inst_learning_loop_flag               true
% 11.25/1.99  --inst_learning_start                   3000
% 11.25/1.99  --inst_learning_factor                  2
% 11.25/1.99  --inst_start_prop_sim_after_learn       3
% 11.25/1.99  --inst_sel_renew                        solver
% 11.25/1.99  --inst_lit_activity_flag                true
% 11.25/1.99  --inst_restr_to_given                   false
% 11.25/1.99  --inst_activity_threshold               500
% 11.25/1.99  --inst_out_proof                        true
% 11.25/1.99  
% 11.25/1.99  ------ Resolution Options
% 11.25/1.99  
% 11.25/1.99  --resolution_flag                       true
% 11.25/1.99  --res_lit_sel                           adaptive
% 11.25/1.99  --res_lit_sel_side                      none
% 11.25/1.99  --res_ordering                          kbo
% 11.25/1.99  --res_to_prop_solver                    active
% 11.25/1.99  --res_prop_simpl_new                    false
% 11.25/1.99  --res_prop_simpl_given                  true
% 11.25/1.99  --res_passive_queue_type                priority_queues
% 11.25/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.25/1.99  --res_passive_queues_freq               [15;5]
% 11.25/1.99  --res_forward_subs                      full
% 11.25/1.99  --res_backward_subs                     full
% 11.25/1.99  --res_forward_subs_resolution           true
% 11.25/1.99  --res_backward_subs_resolution          true
% 11.25/1.99  --res_orphan_elimination                true
% 11.25/1.99  --res_time_limit                        2.
% 11.25/1.99  --res_out_proof                         true
% 11.25/1.99  
% 11.25/1.99  ------ Superposition Options
% 11.25/1.99  
% 11.25/1.99  --superposition_flag                    true
% 11.25/1.99  --sup_passive_queue_type                priority_queues
% 11.25/1.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.25/1.99  --sup_passive_queues_freq               [1;4]
% 11.25/1.99  --demod_completeness_check              fast
% 11.25/1.99  --demod_use_ground                      true
% 11.25/1.99  --sup_to_prop_solver                    passive
% 11.25/1.99  --sup_prop_simpl_new                    true
% 11.25/1.99  --sup_prop_simpl_given                  true
% 11.25/1.99  --sup_fun_splitting                     false
% 11.25/1.99  --sup_smt_interval                      50000
% 11.25/1.99  
% 11.25/1.99  ------ Superposition Simplification Setup
% 11.25/1.99  
% 11.25/1.99  --sup_indices_passive                   []
% 11.25/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.25/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.25/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.25/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.25/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.25/1.99  --sup_full_bw                           [BwDemod]
% 11.25/1.99  --sup_immed_triv                        [TrivRules]
% 11.25/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.25/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.25/1.99  --sup_immed_bw_main                     []
% 11.25/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.25/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.25/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.25/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.25/1.99  
% 11.25/1.99  ------ Combination Options
% 11.25/1.99  
% 11.25/1.99  --comb_res_mult                         3
% 11.25/1.99  --comb_sup_mult                         2
% 11.25/1.99  --comb_inst_mult                        10
% 11.25/1.99  
% 11.25/1.99  ------ Debug Options
% 11.25/1.99  
% 11.25/1.99  --dbg_backtrace                         false
% 11.25/1.99  --dbg_dump_prop_clauses                 false
% 11.25/1.99  --dbg_dump_prop_clauses_file            -
% 11.25/1.99  --dbg_out_stat                          false
% 11.25/1.99  ------ Parsing...
% 11.25/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.25/1.99  
% 11.25/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 11.25/1.99  
% 11.25/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.25/1.99  
% 11.25/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.25/1.99  ------ Proving...
% 11.25/1.99  ------ Problem Properties 
% 11.25/1.99  
% 11.25/1.99  
% 11.25/1.99  clauses                                 41
% 11.25/1.99  conjectures                             5
% 11.25/1.99  EPR                                     5
% 11.25/1.99  Horn                                    32
% 11.25/1.99  unary                                   12
% 11.25/1.99  binary                                  13
% 11.25/1.99  lits                                    91
% 11.25/1.99  lits eq                                 21
% 11.25/1.99  fd_pure                                 0
% 11.25/1.99  fd_pseudo                               0
% 11.25/1.99  fd_cond                                 4
% 11.25/1.99  fd_pseudo_cond                          4
% 11.25/1.99  AC symbols                              0
% 11.25/1.99  
% 11.25/1.99  ------ Input Options Time Limit: Unbounded
% 11.25/1.99  
% 11.25/1.99  
% 11.25/1.99  ------ 
% 11.25/1.99  Current options:
% 11.25/1.99  ------ 
% 11.25/1.99  
% 11.25/1.99  ------ Input Options
% 11.25/1.99  
% 11.25/1.99  --out_options                           all
% 11.25/1.99  --tptp_safe_out                         true
% 11.25/1.99  --problem_path                          ""
% 11.25/1.99  --include_path                          ""
% 11.25/1.99  --clausifier                            res/vclausify_rel
% 11.25/1.99  --clausifier_options                    --mode clausify
% 11.25/1.99  --stdin                                 false
% 11.25/1.99  --stats_out                             sel
% 11.25/1.99  
% 11.25/1.99  ------ General Options
% 11.25/1.99  
% 11.25/1.99  --fof                                   false
% 11.25/1.99  --time_out_real                         604.99
% 11.25/1.99  --time_out_virtual                      -1.
% 11.25/1.99  --symbol_type_check                     false
% 11.25/1.99  --clausify_out                          false
% 11.25/1.99  --sig_cnt_out                           false
% 11.25/1.99  --trig_cnt_out                          false
% 11.25/1.99  --trig_cnt_out_tolerance                1.
% 11.25/1.99  --trig_cnt_out_sk_spl                   false
% 11.25/1.99  --abstr_cl_out                          false
% 11.25/1.99  
% 11.25/1.99  ------ Global Options
% 11.25/1.99  
% 11.25/1.99  --schedule                              none
% 11.25/1.99  --add_important_lit                     false
% 11.25/1.99  --prop_solver_per_cl                    1000
% 11.25/1.99  --min_unsat_core                        false
% 11.25/1.99  --soft_assumptions                      false
% 11.25/1.99  --soft_lemma_size                       3
% 11.25/1.99  --prop_impl_unit_size                   0
% 11.25/1.99  --prop_impl_unit                        []
% 11.25/1.99  --share_sel_clauses                     true
% 11.25/1.99  --reset_solvers                         false
% 11.25/1.99  --bc_imp_inh                            [conj_cone]
% 11.25/1.99  --conj_cone_tolerance                   3.
% 11.25/1.99  --extra_neg_conj                        none
% 11.25/1.99  --large_theory_mode                     true
% 11.25/1.99  --prolific_symb_bound                   200
% 11.25/1.99  --lt_threshold                          2000
% 11.25/1.99  --clause_weak_htbl                      true
% 11.25/1.99  --gc_record_bc_elim                     false
% 11.25/1.99  
% 11.25/1.99  ------ Preprocessing Options
% 11.25/1.99  
% 11.25/1.99  --preprocessing_flag                    true
% 11.25/1.99  --time_out_prep_mult                    0.1
% 11.25/1.99  --splitting_mode                        input
% 11.25/1.99  --splitting_grd                         true
% 11.25/1.99  --splitting_cvd                         false
% 11.25/1.99  --splitting_cvd_svl                     false
% 11.25/1.99  --splitting_nvd                         32
% 11.25/1.99  --sub_typing                            true
% 11.25/1.99  --prep_gs_sim                           false
% 11.25/1.99  --prep_unflatten                        true
% 11.25/1.99  --prep_res_sim                          true
% 11.25/1.99  --prep_upred                            true
% 11.25/1.99  --prep_sem_filter                       exhaustive
% 11.25/1.99  --prep_sem_filter_out                   false
% 11.25/1.99  --pred_elim                             false
% 11.25/1.99  --res_sim_input                         true
% 11.25/1.99  --eq_ax_congr_red                       true
% 11.25/1.99  --pure_diseq_elim                       true
% 11.25/1.99  --brand_transform                       false
% 11.25/1.99  --non_eq_to_eq                          false
% 11.25/1.99  --prep_def_merge                        true
% 11.25/1.99  --prep_def_merge_prop_impl              false
% 11.25/1.99  --prep_def_merge_mbd                    true
% 11.25/1.99  --prep_def_merge_tr_red                 false
% 11.25/1.99  --prep_def_merge_tr_cl                  false
% 11.25/1.99  --smt_preprocessing                     true
% 11.25/1.99  --smt_ac_axioms                         fast
% 11.25/1.99  --preprocessed_out                      false
% 11.25/1.99  --preprocessed_stats                    false
% 11.25/1.99  
% 11.25/1.99  ------ Abstraction refinement Options
% 11.25/1.99  
% 11.25/1.99  --abstr_ref                             []
% 11.25/1.99  --abstr_ref_prep                        false
% 11.25/1.99  --abstr_ref_until_sat                   false
% 11.25/1.99  --abstr_ref_sig_restrict                funpre
% 11.25/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.25/1.99  --abstr_ref_under                       []
% 11.25/1.99  
% 11.25/1.99  ------ SAT Options
% 11.25/1.99  
% 11.25/1.99  --sat_mode                              false
% 11.25/1.99  --sat_fm_restart_options                ""
% 11.25/1.99  --sat_gr_def                            false
% 11.25/1.99  --sat_epr_types                         true
% 11.25/1.99  --sat_non_cyclic_types                  false
% 11.25/1.99  --sat_finite_models                     false
% 11.25/1.99  --sat_fm_lemmas                         false
% 11.25/1.99  --sat_fm_prep                           false
% 11.25/1.99  --sat_fm_uc_incr                        true
% 11.25/1.99  --sat_out_model                         small
% 11.25/1.99  --sat_out_clauses                       false
% 11.25/1.99  
% 11.25/1.99  ------ QBF Options
% 11.25/1.99  
% 11.25/1.99  --qbf_mode                              false
% 11.25/1.99  --qbf_elim_univ                         false
% 11.25/1.99  --qbf_dom_inst                          none
% 11.25/1.99  --qbf_dom_pre_inst                      false
% 11.25/1.99  --qbf_sk_in                             false
% 11.25/1.99  --qbf_pred_elim                         true
% 11.25/1.99  --qbf_split                             512
% 11.25/1.99  
% 11.25/1.99  ------ BMC1 Options
% 11.25/1.99  
% 11.25/1.99  --bmc1_incremental                      false
% 11.25/1.99  --bmc1_axioms                           reachable_all
% 11.25/1.99  --bmc1_min_bound                        0
% 11.25/1.99  --bmc1_max_bound                        -1
% 11.25/1.99  --bmc1_max_bound_default                -1
% 11.25/1.99  --bmc1_symbol_reachability              true
% 11.25/1.99  --bmc1_property_lemmas                  false
% 11.25/1.99  --bmc1_k_induction                      false
% 11.25/1.99  --bmc1_non_equiv_states                 false
% 11.25/1.99  --bmc1_deadlock                         false
% 11.25/1.99  --bmc1_ucm                              false
% 11.25/1.99  --bmc1_add_unsat_core                   none
% 11.25/1.99  --bmc1_unsat_core_children              false
% 11.25/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.25/1.99  --bmc1_out_stat                         full
% 11.25/1.99  --bmc1_ground_init                      false
% 11.25/1.99  --bmc1_pre_inst_next_state              false
% 11.25/1.99  --bmc1_pre_inst_state                   false
% 11.25/1.99  --bmc1_pre_inst_reach_state             false
% 11.25/1.99  --bmc1_out_unsat_core                   false
% 11.25/1.99  --bmc1_aig_witness_out                  false
% 11.25/1.99  --bmc1_verbose                          false
% 11.25/1.99  --bmc1_dump_clauses_tptp                false
% 11.25/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.25/1.99  --bmc1_dump_file                        -
% 11.25/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.25/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.25/1.99  --bmc1_ucm_extend_mode                  1
% 11.25/1.99  --bmc1_ucm_init_mode                    2
% 11.25/1.99  --bmc1_ucm_cone_mode                    none
% 11.25/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.25/1.99  --bmc1_ucm_relax_model                  4
% 11.25/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.25/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.25/1.99  --bmc1_ucm_layered_model                none
% 11.25/1.99  --bmc1_ucm_max_lemma_size               10
% 11.25/1.99  
% 11.25/1.99  ------ AIG Options
% 11.25/1.99  
% 11.25/1.99  --aig_mode                              false
% 11.25/1.99  
% 11.25/1.99  ------ Instantiation Options
% 11.25/1.99  
% 11.25/1.99  --instantiation_flag                    true
% 11.25/1.99  --inst_sos_flag                         false
% 11.25/1.99  --inst_sos_phase                        true
% 11.25/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.25/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.25/1.99  --inst_lit_sel_side                     num_symb
% 11.25/1.99  --inst_solver_per_active                1400
% 11.25/1.99  --inst_solver_calls_frac                1.
% 11.25/1.99  --inst_passive_queue_type               priority_queues
% 11.25/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.25/1.99  --inst_passive_queues_freq              [25;2]
% 11.25/1.99  --inst_dismatching                      true
% 11.25/1.99  --inst_eager_unprocessed_to_passive     true
% 11.25/1.99  --inst_prop_sim_given                   true
% 11.25/1.99  --inst_prop_sim_new                     false
% 11.25/1.99  --inst_subs_new                         false
% 11.25/1.99  --inst_eq_res_simp                      false
% 11.25/1.99  --inst_subs_given                       false
% 11.25/1.99  --inst_orphan_elimination               true
% 11.25/1.99  --inst_learning_loop_flag               true
% 11.25/1.99  --inst_learning_start                   3000
% 11.25/1.99  --inst_learning_factor                  2
% 11.25/1.99  --inst_start_prop_sim_after_learn       3
% 11.25/1.99  --inst_sel_renew                        solver
% 11.25/1.99  --inst_lit_activity_flag                true
% 11.25/1.99  --inst_restr_to_given                   false
% 11.25/1.99  --inst_activity_threshold               500
% 11.25/1.99  --inst_out_proof                        true
% 11.25/1.99  
% 11.25/1.99  ------ Resolution Options
% 11.25/1.99  
% 11.25/1.99  --resolution_flag                       true
% 11.25/1.99  --res_lit_sel                           adaptive
% 11.25/1.99  --res_lit_sel_side                      none
% 11.25/1.99  --res_ordering                          kbo
% 11.25/1.99  --res_to_prop_solver                    active
% 11.25/1.99  --res_prop_simpl_new                    false
% 11.25/1.99  --res_prop_simpl_given                  true
% 11.25/1.99  --res_passive_queue_type                priority_queues
% 11.25/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.25/1.99  --res_passive_queues_freq               [15;5]
% 11.25/1.99  --res_forward_subs                      full
% 11.25/1.99  --res_backward_subs                     full
% 11.25/1.99  --res_forward_subs_resolution           true
% 11.25/1.99  --res_backward_subs_resolution          true
% 11.25/1.99  --res_orphan_elimination                true
% 11.25/1.99  --res_time_limit                        2.
% 11.25/1.99  --res_out_proof                         true
% 11.25/1.99  
% 11.25/1.99  ------ Superposition Options
% 11.25/1.99  
% 11.25/1.99  --superposition_flag                    true
% 11.25/1.99  --sup_passive_queue_type                priority_queues
% 11.25/1.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.25/1.99  --sup_passive_queues_freq               [1;4]
% 11.25/1.99  --demod_completeness_check              fast
% 11.25/1.99  --demod_use_ground                      true
% 11.25/1.99  --sup_to_prop_solver                    passive
% 11.25/1.99  --sup_prop_simpl_new                    true
% 11.25/1.99  --sup_prop_simpl_given                  true
% 11.25/1.99  --sup_fun_splitting                     false
% 11.25/1.99  --sup_smt_interval                      50000
% 11.25/1.99  
% 11.25/1.99  ------ Superposition Simplification Setup
% 11.25/1.99  
% 11.25/1.99  --sup_indices_passive                   []
% 11.25/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.25/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.25/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.25/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.25/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.25/1.99  --sup_full_bw                           [BwDemod]
% 11.25/1.99  --sup_immed_triv                        [TrivRules]
% 11.25/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.25/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.25/1.99  --sup_immed_bw_main                     []
% 11.25/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.25/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.25/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.25/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.25/1.99  
% 11.25/1.99  ------ Combination Options
% 11.25/1.99  
% 11.25/1.99  --comb_res_mult                         3
% 11.25/1.99  --comb_sup_mult                         2
% 11.25/1.99  --comb_inst_mult                        10
% 11.25/1.99  
% 11.25/1.99  ------ Debug Options
% 11.25/1.99  
% 11.25/1.99  --dbg_backtrace                         false
% 11.25/1.99  --dbg_dump_prop_clauses                 false
% 11.25/1.99  --dbg_dump_prop_clauses_file            -
% 11.25/1.99  --dbg_out_stat                          false
% 11.25/1.99  
% 11.25/1.99  
% 11.25/1.99  
% 11.25/1.99  
% 11.25/1.99  ------ Proving...
% 11.25/1.99  
% 11.25/1.99  
% 11.25/1.99  % SZS status Theorem for theBenchmark.p
% 11.25/1.99  
% 11.25/1.99   Resolution empty clause
% 11.25/1.99  
% 11.25/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.25/1.99  
% 11.25/1.99  fof(f22,axiom,(
% 11.25/1.99    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f26,plain,(
% 11.25/1.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 11.25/1.99    inference(pure_predicate_removal,[],[f22])).
% 11.25/1.99  
% 11.25/1.99  fof(f39,plain,(
% 11.25/1.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 11.25/1.99    inference(ennf_transformation,[],[f26])).
% 11.25/1.99  
% 11.25/1.99  fof(f56,plain,(
% 11.25/1.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 11.25/1.99    introduced(choice_axiom,[])).
% 11.25/1.99  
% 11.25/1.99  fof(f57,plain,(
% 11.25/1.99    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 11.25/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f56])).
% 11.25/1.99  
% 11.25/1.99  fof(f94,plain,(
% 11.25/1.99    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 11.25/1.99    inference(cnf_transformation,[],[f57])).
% 11.25/1.99  
% 11.25/1.99  fof(f9,axiom,(
% 11.25/1.99    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f76,plain,(
% 11.25/1.99    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 11.25/1.99    inference(cnf_transformation,[],[f9])).
% 11.25/1.99  
% 11.25/1.99  fof(f7,axiom,(
% 11.25/1.99    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f48,plain,(
% 11.25/1.99    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 11.25/1.99    inference(nnf_transformation,[],[f7])).
% 11.25/1.99  
% 11.25/1.99  fof(f49,plain,(
% 11.25/1.99    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 11.25/1.99    inference(rectify,[],[f48])).
% 11.25/1.99  
% 11.25/1.99  fof(f52,plain,(
% 11.25/1.99    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))))),
% 11.25/1.99    introduced(choice_axiom,[])).
% 11.25/1.99  
% 11.25/1.99  fof(f51,plain,(
% 11.25/1.99    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK2(X0,X1),X0) & r2_hidden(X2,sK2(X0,X1))))) )),
% 11.25/1.99    introduced(choice_axiom,[])).
% 11.25/1.99  
% 11.25/1.99  fof(f50,plain,(
% 11.25/1.99    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK1(X0,X1),X4)) | r2_hidden(sK1(X0,X1),X1))))),
% 11.25/1.99    introduced(choice_axiom,[])).
% 11.25/1.99  
% 11.25/1.99  fof(f53,plain,(
% 11.25/1.99    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & ((r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),sK2(X0,X1))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 11.25/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f49,f52,f51,f50])).
% 11.25/1.99  
% 11.25/1.99  fof(f70,plain,(
% 11.25/1.99    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 11.25/1.99    inference(cnf_transformation,[],[f53])).
% 11.25/1.99  
% 11.25/1.99  fof(f115,plain,(
% 11.25/1.99    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 11.25/1.99    inference(equality_resolution,[],[f70])).
% 11.25/1.99  
% 11.25/1.99  fof(f71,plain,(
% 11.25/1.99    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 11.25/1.99    inference(cnf_transformation,[],[f53])).
% 11.25/1.99  
% 11.25/1.99  fof(f114,plain,(
% 11.25/1.99    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 11.25/1.99    inference(equality_resolution,[],[f71])).
% 11.25/1.99  
% 11.25/1.99  fof(f24,conjecture,(
% 11.25/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f25,negated_conjecture,(
% 11.25/1.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 11.25/1.99    inference(negated_conjecture,[],[f24])).
% 11.25/1.99  
% 11.25/1.99  fof(f42,plain,(
% 11.25/1.99    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 11.25/1.99    inference(ennf_transformation,[],[f25])).
% 11.25/1.99  
% 11.25/1.99  fof(f43,plain,(
% 11.25/1.99    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 11.25/1.99    inference(flattening,[],[f42])).
% 11.25/1.99  
% 11.25/1.99  fof(f59,plain,(
% 11.25/1.99    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK7,sK5),sK6) & k1_xboole_0 != sK6 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6))) & v1_funct_2(sK7,k1_tarski(sK5),sK6) & v1_funct_1(sK7))),
% 11.25/1.99    introduced(choice_axiom,[])).
% 11.25/1.99  
% 11.25/1.99  fof(f60,plain,(
% 11.25/1.99    ~r2_hidden(k1_funct_1(sK7,sK5),sK6) & k1_xboole_0 != sK6 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6))) & v1_funct_2(sK7,k1_tarski(sK5),sK6) & v1_funct_1(sK7)),
% 11.25/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f43,f59])).
% 11.25/1.99  
% 11.25/1.99  fof(f103,plain,(
% 11.25/1.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6)))),
% 11.25/1.99    inference(cnf_transformation,[],[f60])).
% 11.25/1.99  
% 11.25/1.99  fof(f3,axiom,(
% 11.25/1.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f65,plain,(
% 11.25/1.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.25/1.99    inference(cnf_transformation,[],[f3])).
% 11.25/1.99  
% 11.25/1.99  fof(f4,axiom,(
% 11.25/1.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f66,plain,(
% 11.25/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.25/1.99    inference(cnf_transformation,[],[f4])).
% 11.25/1.99  
% 11.25/1.99  fof(f5,axiom,(
% 11.25/1.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f67,plain,(
% 11.25/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.25/1.99    inference(cnf_transformation,[],[f5])).
% 11.25/1.99  
% 11.25/1.99  fof(f6,axiom,(
% 11.25/1.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f68,plain,(
% 11.25/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.25/1.99    inference(cnf_transformation,[],[f6])).
% 11.25/1.99  
% 11.25/1.99  fof(f106,plain,(
% 11.25/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 11.25/1.99    inference(definition_unfolding,[],[f67,f68])).
% 11.25/1.99  
% 11.25/1.99  fof(f107,plain,(
% 11.25/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 11.25/1.99    inference(definition_unfolding,[],[f66,f106])).
% 11.25/1.99  
% 11.25/1.99  fof(f108,plain,(
% 11.25/1.99    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 11.25/1.99    inference(definition_unfolding,[],[f65,f107])).
% 11.25/1.99  
% 11.25/1.99  fof(f112,plain,(
% 11.25/1.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK6)))),
% 11.25/1.99    inference(definition_unfolding,[],[f103,f108])).
% 11.25/1.99  
% 11.25/1.99  fof(f23,axiom,(
% 11.25/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f40,plain,(
% 11.25/1.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.25/1.99    inference(ennf_transformation,[],[f23])).
% 11.25/1.99  
% 11.25/1.99  fof(f41,plain,(
% 11.25/1.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.25/1.99    inference(flattening,[],[f40])).
% 11.25/1.99  
% 11.25/1.99  fof(f58,plain,(
% 11.25/1.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.25/1.99    inference(nnf_transformation,[],[f41])).
% 11.25/1.99  
% 11.25/1.99  fof(f95,plain,(
% 11.25/1.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.25/1.99    inference(cnf_transformation,[],[f58])).
% 11.25/1.99  
% 11.25/1.99  fof(f102,plain,(
% 11.25/1.99    v1_funct_2(sK7,k1_tarski(sK5),sK6)),
% 11.25/1.99    inference(cnf_transformation,[],[f60])).
% 11.25/1.99  
% 11.25/1.99  fof(f113,plain,(
% 11.25/1.99    v1_funct_2(sK7,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK6)),
% 11.25/1.99    inference(definition_unfolding,[],[f102,f108])).
% 11.25/1.99  
% 11.25/1.99  fof(f104,plain,(
% 11.25/1.99    k1_xboole_0 != sK6),
% 11.25/1.99    inference(cnf_transformation,[],[f60])).
% 11.25/1.99  
% 11.25/1.99  fof(f19,axiom,(
% 11.25/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f36,plain,(
% 11.25/1.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.25/1.99    inference(ennf_transformation,[],[f19])).
% 11.25/1.99  
% 11.25/1.99  fof(f89,plain,(
% 11.25/1.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.25/1.99    inference(cnf_transformation,[],[f36])).
% 11.25/1.99  
% 11.25/1.99  fof(f11,axiom,(
% 11.25/1.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f29,plain,(
% 11.25/1.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 11.25/1.99    inference(ennf_transformation,[],[f11])).
% 11.25/1.99  
% 11.25/1.99  fof(f30,plain,(
% 11.25/1.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 11.25/1.99    inference(flattening,[],[f29])).
% 11.25/1.99  
% 11.25/1.99  fof(f78,plain,(
% 11.25/1.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 11.25/1.99    inference(cnf_transformation,[],[f30])).
% 11.25/1.99  
% 11.25/1.99  fof(f10,axiom,(
% 11.25/1.99    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f77,plain,(
% 11.25/1.99    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 11.25/1.99    inference(cnf_transformation,[],[f10])).
% 11.25/1.99  
% 11.25/1.99  fof(f21,axiom,(
% 11.25/1.99    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f38,plain,(
% 11.25/1.99    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 11.25/1.99    inference(ennf_transformation,[],[f21])).
% 11.25/1.99  
% 11.25/1.99  fof(f92,plain,(
% 11.25/1.99    ( ! [X2,X0,X1] : (k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))) )),
% 11.25/1.99    inference(cnf_transformation,[],[f38])).
% 11.25/1.99  
% 11.25/1.99  fof(f111,plain,(
% 11.25/1.99    ( ! [X2,X0,X1] : (k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X1),X2))) )),
% 11.25/1.99    inference(definition_unfolding,[],[f92,f108])).
% 11.25/1.99  
% 11.25/1.99  fof(f101,plain,(
% 11.25/1.99    v1_funct_1(sK7)),
% 11.25/1.99    inference(cnf_transformation,[],[f60])).
% 11.25/1.99  
% 11.25/1.99  fof(f18,axiom,(
% 11.25/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f27,plain,(
% 11.25/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 11.25/1.99    inference(pure_predicate_removal,[],[f18])).
% 11.25/1.99  
% 11.25/1.99  fof(f35,plain,(
% 11.25/1.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.25/1.99    inference(ennf_transformation,[],[f27])).
% 11.25/1.99  
% 11.25/1.99  fof(f88,plain,(
% 11.25/1.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.25/1.99    inference(cnf_transformation,[],[f35])).
% 11.25/1.99  
% 11.25/1.99  fof(f14,axiom,(
% 11.25/1.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f32,plain,(
% 11.25/1.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.25/1.99    inference(ennf_transformation,[],[f14])).
% 11.25/1.99  
% 11.25/1.99  fof(f55,plain,(
% 11.25/1.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.25/1.99    inference(nnf_transformation,[],[f32])).
% 11.25/1.99  
% 11.25/1.99  fof(f82,plain,(
% 11.25/1.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.25/1.99    inference(cnf_transformation,[],[f55])).
% 11.25/1.99  
% 11.25/1.99  fof(f20,axiom,(
% 11.25/1.99    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f37,plain,(
% 11.25/1.99    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 11.25/1.99    inference(ennf_transformation,[],[f20])).
% 11.25/1.99  
% 11.25/1.99  fof(f90,plain,(
% 11.25/1.99    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 11.25/1.99    inference(cnf_transformation,[],[f37])).
% 11.25/1.99  
% 11.25/1.99  fof(f13,axiom,(
% 11.25/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f31,plain,(
% 11.25/1.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 11.25/1.99    inference(ennf_transformation,[],[f13])).
% 11.25/1.99  
% 11.25/1.99  fof(f81,plain,(
% 11.25/1.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 11.25/1.99    inference(cnf_transformation,[],[f31])).
% 11.25/1.99  
% 11.25/1.99  fof(f12,axiom,(
% 11.25/1.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f54,plain,(
% 11.25/1.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.25/1.99    inference(nnf_transformation,[],[f12])).
% 11.25/1.99  
% 11.25/1.99  fof(f80,plain,(
% 11.25/1.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.25/1.99    inference(cnf_transformation,[],[f54])).
% 11.25/1.99  
% 11.25/1.99  fof(f79,plain,(
% 11.25/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.25/1.99    inference(cnf_transformation,[],[f54])).
% 11.25/1.99  
% 11.25/1.99  fof(f15,axiom,(
% 11.25/1.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f84,plain,(
% 11.25/1.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 11.25/1.99    inference(cnf_transformation,[],[f15])).
% 11.25/1.99  
% 11.25/1.99  fof(f17,axiom,(
% 11.25/1.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f33,plain,(
% 11.25/1.99    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.25/1.99    inference(ennf_transformation,[],[f17])).
% 11.25/1.99  
% 11.25/1.99  fof(f34,plain,(
% 11.25/1.99    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.25/1.99    inference(flattening,[],[f33])).
% 11.25/1.99  
% 11.25/1.99  fof(f87,plain,(
% 11.25/1.99    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.25/1.99    inference(cnf_transformation,[],[f34])).
% 11.25/1.99  
% 11.25/1.99  fof(f1,axiom,(
% 11.25/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f28,plain,(
% 11.25/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.25/1.99    inference(ennf_transformation,[],[f1])).
% 11.25/1.99  
% 11.25/1.99  fof(f44,plain,(
% 11.25/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.25/1.99    inference(nnf_transformation,[],[f28])).
% 11.25/1.99  
% 11.25/1.99  fof(f45,plain,(
% 11.25/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.25/1.99    inference(rectify,[],[f44])).
% 11.25/1.99  
% 11.25/1.99  fof(f46,plain,(
% 11.25/1.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.25/1.99    introduced(choice_axiom,[])).
% 11.25/1.99  
% 11.25/1.99  fof(f47,plain,(
% 11.25/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.25/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f46])).
% 11.25/1.99  
% 11.25/1.99  fof(f61,plain,(
% 11.25/1.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 11.25/1.99    inference(cnf_transformation,[],[f47])).
% 11.25/1.99  
% 11.25/1.99  fof(f105,plain,(
% 11.25/1.99    ~r2_hidden(k1_funct_1(sK7,sK5),sK6)),
% 11.25/1.99    inference(cnf_transformation,[],[f60])).
% 11.25/1.99  
% 11.25/1.99  fof(f2,axiom,(
% 11.25/1.99    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f64,plain,(
% 11.25/1.99    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.25/1.99    inference(cnf_transformation,[],[f2])).
% 11.25/1.99  
% 11.25/1.99  fof(f8,axiom,(
% 11.25/1.99    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f75,plain,(
% 11.25/1.99    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 11.25/1.99    inference(cnf_transformation,[],[f8])).
% 11.25/1.99  
% 11.25/1.99  fof(f109,plain,(
% 11.25/1.99    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) )),
% 11.25/1.99    inference(definition_unfolding,[],[f75,f108])).
% 11.25/1.99  
% 11.25/1.99  fof(f16,axiom,(
% 11.25/1.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f85,plain,(
% 11.25/1.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 11.25/1.99    inference(cnf_transformation,[],[f16])).
% 11.25/1.99  
% 11.25/1.99  cnf(c_29,plain,
% 11.25/1.99      ( r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0 ),
% 11.25/1.99      inference(cnf_transformation,[],[f94]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_1252,plain,
% 11.25/1.99      ( k1_xboole_0 = X0 | r2_hidden(sK4(X0),X0) = iProver_top ),
% 11.25/1.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_11,plain,
% 11.25/1.99      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 11.25/1.99      inference(cnf_transformation,[],[f76]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_8,plain,
% 11.25/1.99      ( ~ r2_hidden(X0,k3_tarski(X1)) | r2_hidden(sK3(X1,X0),X1) ),
% 11.25/1.99      inference(cnf_transformation,[],[f115]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_1268,plain,
% 11.25/1.99      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 11.25/1.99      | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
% 11.25/1.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_7,plain,
% 11.25/1.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,k3_tarski(X1)) ),
% 11.25/1.99      inference(cnf_transformation,[],[f114]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_1269,plain,
% 11.25/1.99      ( r2_hidden(X0,X1) != iProver_top
% 11.25/1.99      | r2_hidden(X2,X0) != iProver_top
% 11.25/1.99      | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
% 11.25/1.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_3654,plain,
% 11.25/1.99      ( r2_hidden(X0,sK3(X1,X2)) != iProver_top
% 11.25/1.99      | r2_hidden(X2,k3_tarski(X1)) != iProver_top
% 11.25/1.99      | r2_hidden(X0,k3_tarski(X1)) = iProver_top ),
% 11.25/1.99      inference(superposition,[status(thm)],[c_1268,c_1269]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_15371,plain,
% 11.25/1.99      ( sK3(X0,X1) = k1_xboole_0
% 11.25/1.99      | r2_hidden(X1,k3_tarski(X0)) != iProver_top
% 11.25/1.99      | r2_hidden(sK4(sK3(X0,X1)),k3_tarski(X0)) = iProver_top ),
% 11.25/1.99      inference(superposition,[status(thm)],[c_1252,c_3654]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_40419,plain,
% 11.25/1.99      ( sK3(k1_zfmisc_1(X0),X1) = k1_xboole_0
% 11.25/1.99      | r2_hidden(X1,k3_tarski(k1_zfmisc_1(X0))) != iProver_top
% 11.25/1.99      | r2_hidden(sK4(sK3(k1_zfmisc_1(X0),X1)),X0) = iProver_top ),
% 11.25/1.99      inference(superposition,[status(thm)],[c_11,c_15371]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_40485,plain,
% 11.25/1.99      ( sK3(k1_zfmisc_1(X0),X1) = k1_xboole_0
% 11.25/1.99      | r2_hidden(X1,X0) != iProver_top
% 11.25/1.99      | r2_hidden(sK4(sK3(k1_zfmisc_1(X0),X1)),X0) = iProver_top ),
% 11.25/1.99      inference(light_normalisation,[status(thm)],[c_40419,c_11]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_38,negated_conjecture,
% 11.25/1.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK6))) ),
% 11.25/1.99      inference(cnf_transformation,[],[f112]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_1244,plain,
% 11.25/1.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK6))) = iProver_top ),
% 11.25/1.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_35,plain,
% 11.25/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.25/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.25/1.99      | k1_relset_1(X1,X2,X0) = X1
% 11.25/1.99      | k1_xboole_0 = X2 ),
% 11.25/1.99      inference(cnf_transformation,[],[f95]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_1246,plain,
% 11.25/1.99      ( k1_relset_1(X0,X1,X2) = X0
% 11.25/1.99      | k1_xboole_0 = X1
% 11.25/1.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.25/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.25/1.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_1988,plain,
% 11.25/1.99      ( k1_relset_1(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK6,sK7) = k3_enumset1(sK5,sK5,sK5,sK5,sK5)
% 11.25/1.99      | sK6 = k1_xboole_0
% 11.25/1.99      | v1_funct_2(sK7,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK6) != iProver_top ),
% 11.25/1.99      inference(superposition,[status(thm)],[c_1244,c_1246]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_39,negated_conjecture,
% 11.25/1.99      ( v1_funct_2(sK7,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK6) ),
% 11.25/1.99      inference(cnf_transformation,[],[f113]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_37,negated_conjecture,
% 11.25/1.99      ( k1_xboole_0 != sK6 ),
% 11.25/1.99      inference(cnf_transformation,[],[f104]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_1676,plain,
% 11.25/1.99      ( ~ v1_funct_2(X0,X1,sK6)
% 11.25/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK6)))
% 11.25/1.99      | k1_relset_1(X1,sK6,X0) = X1
% 11.25/1.99      | k1_xboole_0 = sK6 ),
% 11.25/1.99      inference(instantiation,[status(thm)],[c_35]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_1798,plain,
% 11.25/1.99      ( ~ v1_funct_2(sK7,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK6)
% 11.25/1.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK6)))
% 11.25/1.99      | k1_relset_1(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK6,sK7) = k3_enumset1(sK5,sK5,sK5,sK5,sK5)
% 11.25/1.99      | k1_xboole_0 = sK6 ),
% 11.25/1.99      inference(instantiation,[status(thm)],[c_1676]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_5017,plain,
% 11.25/1.99      ( k1_relset_1(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK6,sK7) = k3_enumset1(sK5,sK5,sK5,sK5,sK5) ),
% 11.25/1.99      inference(global_propositional_subsumption,
% 11.25/1.99                [status(thm)],
% 11.25/1.99                [c_1988,c_39,c_38,c_37,c_1798]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_24,plain,
% 11.25/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.25/1.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 11.25/1.99      inference(cnf_transformation,[],[f89]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_1257,plain,
% 11.25/1.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 11.25/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.25/1.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_2735,plain,
% 11.25/1.99      ( k1_relset_1(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK6,sK7) = k1_relat_1(sK7) ),
% 11.25/1.99      inference(superposition,[status(thm)],[c_1244,c_1257]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_5019,plain,
% 11.25/1.99      ( k3_enumset1(sK5,sK5,sK5,sK5,sK5) = k1_relat_1(sK7) ),
% 11.25/1.99      inference(light_normalisation,[status(thm)],[c_5017,c_2735]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_5023,plain,
% 11.25/1.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK6))) = iProver_top ),
% 11.25/1.99      inference(demodulation,[status(thm)],[c_5019,c_1244]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_13,plain,
% 11.25/1.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.25/1.99      inference(cnf_transformation,[],[f78]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_1265,plain,
% 11.25/1.99      ( m1_subset_1(X0,X1) != iProver_top
% 11.25/1.99      | r2_hidden(X0,X1) = iProver_top
% 11.25/1.99      | v1_xboole_0(X1) = iProver_top ),
% 11.25/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_5324,plain,
% 11.25/1.99      ( r2_hidden(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK6))) = iProver_top
% 11.25/1.99      | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK6))) = iProver_top ),
% 11.25/1.99      inference(superposition,[status(thm)],[c_5023,c_1265]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_12,plain,
% 11.25/1.99      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 11.25/1.99      inference(cnf_transformation,[],[f77]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_1266,plain,
% 11.25/1.99      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 11.25/1.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_7222,plain,
% 11.25/1.99      ( r2_hidden(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK6))) = iProver_top ),
% 11.25/1.99      inference(forward_subsumption_resolution,[status(thm)],[c_5324,c_1266]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_7224,plain,
% 11.25/1.99      ( r2_hidden(X0,k3_tarski(k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK6)))) = iProver_top
% 11.25/1.99      | r2_hidden(X0,sK7) != iProver_top ),
% 11.25/1.99      inference(superposition,[status(thm)],[c_7222,c_1269]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_7232,plain,
% 11.25/1.99      ( r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK7),sK6)) = iProver_top
% 11.25/1.99      | r2_hidden(X0,sK7) != iProver_top ),
% 11.25/1.99      inference(demodulation,[status(thm)],[c_7224,c_11]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_28,plain,
% 11.25/1.99      ( ~ r2_hidden(X0,k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X1),X2))
% 11.25/1.99      | k1_mcart_1(X0) = X1 ),
% 11.25/1.99      inference(cnf_transformation,[],[f111]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_1253,plain,
% 11.25/1.99      ( k1_mcart_1(X0) = X1
% 11.25/1.99      | r2_hidden(X0,k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X1),X2)) != iProver_top ),
% 11.25/1.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_5038,plain,
% 11.25/1.99      ( k1_mcart_1(X0) = sK5
% 11.25/1.99      | r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK7),X1)) != iProver_top ),
% 11.25/1.99      inference(superposition,[status(thm)],[c_5019,c_1253]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_7491,plain,
% 11.25/1.99      ( k1_mcart_1(X0) = sK5 | r2_hidden(X0,sK7) != iProver_top ),
% 11.25/1.99      inference(superposition,[status(thm)],[c_7232,c_5038]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_40527,plain,
% 11.25/1.99      ( sK3(k1_zfmisc_1(sK7),X0) = k1_xboole_0
% 11.25/1.99      | k1_mcart_1(sK4(sK3(k1_zfmisc_1(sK7),X0))) = sK5
% 11.25/1.99      | r2_hidden(X0,sK7) != iProver_top ),
% 11.25/1.99      inference(superposition,[status(thm)],[c_40485,c_7491]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_41256,plain,
% 11.25/1.99      ( sK3(k1_zfmisc_1(sK7),sK4(sK7)) = k1_xboole_0
% 11.25/1.99      | k1_mcart_1(sK4(sK3(k1_zfmisc_1(sK7),sK4(sK7)))) = sK5
% 11.25/1.99      | sK7 = k1_xboole_0 ),
% 11.25/1.99      inference(superposition,[status(thm)],[c_1252,c_40527]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_40,negated_conjecture,
% 11.25/1.99      ( v1_funct_1(sK7) ),
% 11.25/1.99      inference(cnf_transformation,[],[f101]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_23,plain,
% 11.25/1.99      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 11.25/1.99      inference(cnf_transformation,[],[f88]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_1592,plain,
% 11.25/1.99      ( v5_relat_1(sK7,sK6)
% 11.25/1.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK6))) ),
% 11.25/1.99      inference(instantiation,[status(thm)],[c_23]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_18,plain,
% 11.25/1.99      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 11.25/1.99      inference(cnf_transformation,[],[f82]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_1726,plain,
% 11.25/1.99      ( ~ v5_relat_1(sK7,sK6)
% 11.25/1.99      | r1_tarski(k2_relat_1(sK7),sK6)
% 11.25/1.99      | ~ v1_relat_1(sK7) ),
% 11.25/1.99      inference(instantiation,[status(thm)],[c_18]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_1751,plain,
% 11.25/1.99      ( r2_hidden(sK4(sK7),sK7) | k1_xboole_0 = sK7 ),
% 11.25/1.99      inference(instantiation,[status(thm)],[c_29]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_423,plain,( X0 = X0 ),theory(equality) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_1792,plain,
% 11.25/1.99      ( sK7 = sK7 ),
% 11.25/1.99      inference(instantiation,[status(thm)],[c_423]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_424,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_2136,plain,
% 11.25/1.99      ( X0 != X1 | sK7 != X1 | sK7 = X0 ),
% 11.25/1.99      inference(instantiation,[status(thm)],[c_424]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_3754,plain,
% 11.25/1.99      ( X0 != sK7 | sK7 = X0 | sK7 != sK7 ),
% 11.25/1.99      inference(instantiation,[status(thm)],[c_2136]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_3755,plain,
% 11.25/1.99      ( sK7 != sK7 | sK7 = k1_xboole_0 | k1_xboole_0 != sK7 ),
% 11.25/1.99      inference(instantiation,[status(thm)],[c_3754]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_7619,plain,
% 11.25/1.99      ( k1_mcart_1(sK4(sK7)) = sK5 | sK7 = k1_xboole_0 ),
% 11.25/1.99      inference(superposition,[status(thm)],[c_1252,c_7491]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_26,plain,
% 11.25/1.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1) ),
% 11.25/1.99      inference(cnf_transformation,[],[f90]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_1255,plain,
% 11.25/1.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 11.25/1.99      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 11.25/1.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_7490,plain,
% 11.25/1.99      ( r2_hidden(X0,sK7) != iProver_top
% 11.25/1.99      | r2_hidden(k1_mcart_1(X0),k1_relat_1(sK7)) = iProver_top ),
% 11.25/1.99      inference(superposition,[status(thm)],[c_7232,c_1255]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_8218,plain,
% 11.25/1.99      ( sK7 = k1_xboole_0
% 11.25/1.99      | r2_hidden(sK4(sK7),sK7) != iProver_top
% 11.25/1.99      | r2_hidden(sK5,k1_relat_1(sK7)) = iProver_top ),
% 11.25/1.99      inference(superposition,[status(thm)],[c_7619,c_7490]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_8246,plain,
% 11.25/1.99      ( ~ r2_hidden(sK4(sK7),sK7)
% 11.25/1.99      | r2_hidden(sK5,k1_relat_1(sK7))
% 11.25/1.99      | sK7 = k1_xboole_0 ),
% 11.25/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_8218]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_16,plain,
% 11.25/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 11.25/1.99      inference(cnf_transformation,[],[f81]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_14,plain,
% 11.25/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.25/1.99      inference(cnf_transformation,[],[f80]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_257,plain,
% 11.25/1.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.25/1.99      inference(prop_impl,[status(thm)],[c_14]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_258,plain,
% 11.25/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.25/1.99      inference(renaming,[status(thm)],[c_257]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_332,plain,
% 11.25/1.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 11.25/1.99      inference(bin_hyper_res,[status(thm)],[c_16,c_258]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_15,plain,
% 11.25/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.25/1.99      inference(cnf_transformation,[],[f79]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_1646,plain,
% 11.25/1.99      ( r1_tarski(sK7,k2_zfmisc_1(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK6)) ),
% 11.25/1.99      inference(resolution,[status(thm)],[c_15,c_38]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_12478,plain,
% 11.25/1.99      ( ~ v1_relat_1(k2_zfmisc_1(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK6))
% 11.25/1.99      | v1_relat_1(sK7) ),
% 11.25/1.99      inference(resolution,[status(thm)],[c_332,c_1646]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_19,plain,
% 11.25/1.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 11.25/1.99      inference(cnf_transformation,[],[f84]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_12500,plain,
% 11.25/1.99      ( v1_relat_1(sK7) ),
% 11.25/1.99      inference(forward_subsumption_resolution,[status(thm)],[c_12478,c_19]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_22,plain,
% 11.25/1.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 11.25/1.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 11.25/1.99      | ~ v1_funct_1(X1)
% 11.25/1.99      | ~ v1_relat_1(X1) ),
% 11.25/1.99      inference(cnf_transformation,[],[f87]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_1259,plain,
% 11.25/1.99      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 11.25/1.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 11.25/1.99      | v1_funct_1(X1) != iProver_top
% 11.25/1.99      | v1_relat_1(X1) != iProver_top ),
% 11.25/1.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_2,plain,
% 11.25/1.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 11.25/1.99      inference(cnf_transformation,[],[f61]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_1273,plain,
% 11.25/1.99      ( r2_hidden(X0,X1) != iProver_top
% 11.25/1.99      | r2_hidden(X0,X2) = iProver_top
% 11.25/1.99      | r1_tarski(X1,X2) != iProver_top ),
% 11.25/1.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_4133,plain,
% 11.25/1.99      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 11.25/1.99      | r2_hidden(k1_funct_1(X1,X0),X2) = iProver_top
% 11.25/1.99      | r1_tarski(k2_relat_1(X1),X2) != iProver_top
% 11.25/1.99      | v1_funct_1(X1) != iProver_top
% 11.25/1.99      | v1_relat_1(X1) != iProver_top ),
% 11.25/1.99      inference(superposition,[status(thm)],[c_1259,c_1273]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_36,negated_conjecture,
% 11.25/1.99      ( ~ r2_hidden(k1_funct_1(sK7,sK5),sK6) ),
% 11.25/1.99      inference(cnf_transformation,[],[f105]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_1245,plain,
% 11.25/1.99      ( r2_hidden(k1_funct_1(sK7,sK5),sK6) != iProver_top ),
% 11.25/1.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_39878,plain,
% 11.25/1.99      ( r2_hidden(sK5,k1_relat_1(sK7)) != iProver_top
% 11.25/1.99      | r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
% 11.25/1.99      | v1_funct_1(sK7) != iProver_top
% 11.25/1.99      | v1_relat_1(sK7) != iProver_top ),
% 11.25/1.99      inference(superposition,[status(thm)],[c_4133,c_1245]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_40229,plain,
% 11.25/1.99      ( ~ r2_hidden(sK5,k1_relat_1(sK7))
% 11.25/1.99      | ~ r1_tarski(k2_relat_1(sK7),sK6)
% 11.25/1.99      | ~ v1_funct_1(sK7)
% 11.25/1.99      | ~ v1_relat_1(sK7) ),
% 11.25/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_39878]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_42899,plain,
% 11.25/1.99      ( sK7 = k1_xboole_0 ),
% 11.25/1.99      inference(global_propositional_subsumption,
% 11.25/1.99                [status(thm)],
% 11.25/1.99                [c_41256,c_40,c_38,c_1592,c_1726,c_1751,c_1792,c_3755,c_8246,
% 11.25/1.99                 c_12500,c_40229]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_3,plain,
% 11.25/1.99      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.25/1.99      inference(cnf_transformation,[],[f64]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_10,plain,
% 11.25/1.99      ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) != k1_xboole_0 ),
% 11.25/1.99      inference(cnf_transformation,[],[f109]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_1610,plain,
% 11.25/1.99      ( k3_enumset1(X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 11.25/1.99      inference(superposition,[status(thm)],[c_3,c_10]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_5036,plain,
% 11.25/1.99      ( k1_relat_1(sK7) != k1_xboole_0 ),
% 11.25/1.99      inference(superposition,[status(thm)],[c_5019,c_1610]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_42959,plain,
% 11.25/1.99      ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 11.25/1.99      inference(demodulation,[status(thm)],[c_42899,c_5036]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_21,plain,
% 11.25/1.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 11.25/1.99      inference(cnf_transformation,[],[f85]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_42978,plain,
% 11.25/1.99      ( k1_xboole_0 != k1_xboole_0 ),
% 11.25/1.99      inference(light_normalisation,[status(thm)],[c_42959,c_21]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_42979,plain,
% 11.25/1.99      ( $false ),
% 11.25/1.99      inference(equality_resolution_simp,[status(thm)],[c_42978]) ).
% 11.25/1.99  
% 11.25/1.99  
% 11.25/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.25/1.99  
% 11.25/1.99  ------                               Statistics
% 11.25/1.99  
% 11.25/1.99  ------ Selected
% 11.25/1.99  
% 11.25/1.99  total_time:                             1.101
% 11.25/1.99  
%------------------------------------------------------------------------------
