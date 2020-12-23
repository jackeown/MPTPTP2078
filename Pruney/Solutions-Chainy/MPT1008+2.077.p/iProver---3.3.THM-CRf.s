%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:20 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 746 expanded)
%              Number of clauses        :   68 ( 188 expanded)
%              Number of leaves         :   20 ( 182 expanded)
%              Depth                    :   24
%              Number of atoms          :  462 (2502 expanded)
%              Number of equality atoms :  266 (1260 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK1(X0,X1) != X1
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( sK1(X0,X1) != X1
        & r2_hidden(sK1(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f30])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_enumset1(X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f50,f74])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f33])).

fof(f37,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) = X2
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK2(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK2(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK2(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1)
                  & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK4(X0,X5)) = X5
                    & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f34,f37,f36,f35])).

fof(f54,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f91,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k1_tarski(k1_funct_1(sK7,sK5)) != k2_relset_1(k1_tarski(sK5),sK6,sK7)
      & k1_xboole_0 != sK6
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6)))
      & v1_funct_2(sK7,k1_tarski(sK5),sK6)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( k1_tarski(k1_funct_1(sK7,sK5)) != k2_relset_1(k1_tarski(sK5),sK6,sK7)
    & k1_xboole_0 != sK6
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6)))
    & v1_funct_2(sK7,k1_tarski(sK5),sK6)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f25,f40])).

fof(f69,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f71,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6))) ),
    inference(cnf_transformation,[],[f41])).

fof(f83,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6))) ),
    inference(definition_unfolding,[],[f71,f74])).

fof(f70,plain,(
    v1_funct_2(sK7,k1_tarski(sK5),sK6) ),
    inference(cnf_transformation,[],[f41])).

fof(f84,plain,(
    v1_funct_2(sK7,k1_enumset1(sK5,sK5,sK5),sK6) ),
    inference(definition_unfolding,[],[f70,f74])).

fof(f12,axiom,(
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

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f72,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f43,f74])).

fof(f87,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_enumset1(X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f78])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f79,plain,(
    ! [X0] : ~ v1_xboole_0(k1_enumset1(X0,X0,X0)) ),
    inference(definition_unfolding,[],[f49,f74])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f73,plain,(
    k1_tarski(k1_funct_1(sK7,sK5)) != k2_relset_1(k1_tarski(sK5),sK6,sK7) ),
    inference(cnf_transformation,[],[f41])).

fof(f82,plain,(
    k1_enumset1(k1_funct_1(sK7,sK5),k1_funct_1(sK7,sK5),k1_funct_1(sK7,sK5)) != k2_relset_1(k1_enumset1(sK5,sK5,sK5),sK6,sK7) ),
    inference(definition_unfolding,[],[f73,f74,f74])).

fof(f55,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f90,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f51,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f80,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_enumset1(X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f51,f74])).

cnf(c_7,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | k1_enumset1(X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1312,plain,
    ( k1_enumset1(X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_519,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_29])).

cnf(c_520,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | r2_hidden(sK4(sK7,X0),k1_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_519])).

cnf(c_1306,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(sK4(sK7,X0),k1_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_520])).

cnf(c_521,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(sK4(sK7,X0),k1_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_520])).

cnf(c_1047,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1463,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) = k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) ),
    inference(instantiation,[status(thm)],[c_1047])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_371,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_372,plain,
    ( v1_relat_1(sK7)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_1466,plain,
    ( v1_relat_1(sK7)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) ),
    inference(instantiation,[status(thm)],[c_372])).

cnf(c_1467,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6))
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1466])).

cnf(c_2080,plain,
    ( r2_hidden(sK4(sK7,X0),k1_relat_1(sK7)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1306,c_521,c_1463,c_1467])).

cnf(c_2081,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(sK4(sK7,X0),k1_relat_1(sK7)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2080])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK7,k1_enumset1(sK5,sK5,sK5),sK6) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_317,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK7 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_27])).

cnf(c_318,plain,
    ( ~ v1_funct_2(sK7,X0,X1)
    | k1_relset_1(X0,X1,sK7) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_769,plain,
    ( k1_relset_1(X0,X1,sK7) = X0
    | k1_enumset1(sK5,sK5,sK5) != X0
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK6 != X1
    | sK7 != sK7
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_318])).

cnf(c_770,plain,
    ( k1_relset_1(k1_enumset1(sK5,sK5,sK5),sK6,sK7) = k1_enumset1(sK5,sK5,sK5)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6))
    | k1_xboole_0 = sK6 ),
    inference(unflattening,[status(thm)],[c_769])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_771,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6))
    | k1_relset_1(k1_enumset1(sK5,sK5,sK5),sK6,sK7) = k1_enumset1(sK5,sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_770,c_26])).

cnf(c_772,plain,
    ( k1_relset_1(k1_enumset1(sK5,sK5,sK5),sK6,sK7) = k1_enumset1(sK5,sK5,sK5)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) ),
    inference(renaming,[status(thm)],[c_771])).

cnf(c_823,plain,
    ( k1_relset_1(k1_enumset1(sK5,sK5,sK5),sK6,sK7) = k1_enumset1(sK5,sK5,sK5) ),
    inference(equality_resolution_simp,[status(thm)],[c_772])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_362,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_27])).

cnf(c_363,plain,
    ( k1_relset_1(X0,X1,sK7) = k1_relat_1(sK7)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_1474,plain,
    ( k1_relset_1(k1_enumset1(sK5,sK5,sK5),sK6,sK7) = k1_relat_1(sK7) ),
    inference(equality_resolution,[status(thm)],[c_363])).

cnf(c_1721,plain,
    ( k1_enumset1(sK5,sK5,sK5) = k1_relat_1(sK7) ),
    inference(light_normalisation,[status(thm)],[c_823,c_1474])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1313,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1743,plain,
    ( sK5 = X0
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1721,c_1313])).

cnf(c_3222,plain,
    ( sK4(sK7,X0) = sK5
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2081,c_1743])).

cnf(c_3347,plain,
    ( k1_enumset1(X0,X0,X0) = k2_relat_1(sK7)
    | sK4(sK7,sK1(k2_relat_1(sK7),X0)) = sK5
    | k2_relat_1(sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1312,c_3222])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1544,plain,
    ( ~ v1_relat_1(sK7)
    | k2_relat_1(sK7) != k1_xboole_0
    | k1_relat_1(sK7) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(k1_enumset1(X0,X0,X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_311,plain,
    ( k1_enumset1(X0,X0,X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_5])).

cnf(c_1742,plain,
    ( k1_relat_1(sK7) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1721,c_311])).

cnf(c_7996,plain,
    ( sK4(sK7,sK1(k2_relat_1(sK7),X0)) = sK5
    | k1_enumset1(X0,X0,X0) = k2_relat_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3347,c_1463,c_1466,c_1544,c_1742])).

cnf(c_7997,plain,
    ( k1_enumset1(X0,X0,X0) = k2_relat_1(sK7)
    | sK4(sK7,sK1(k2_relat_1(sK7),X0)) = sK5 ),
    inference(renaming,[status(thm)],[c_7996])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_353,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_354,plain,
    ( k2_relset_1(X0,X1,sK7) = k2_relat_1(sK7)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_1471,plain,
    ( k2_relset_1(k1_enumset1(sK5,sK5,sK5),sK6,sK7) = k2_relat_1(sK7) ),
    inference(equality_resolution,[status(thm)],[c_354])).

cnf(c_25,negated_conjecture,
    ( k1_enumset1(k1_funct_1(sK7,sK5),k1_funct_1(sK7,sK5),k1_funct_1(sK7,sK5)) != k2_relset_1(k1_enumset1(sK5,sK5,sK5),sK6,sK7) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1520,plain,
    ( k1_enumset1(k1_funct_1(sK7,sK5),k1_funct_1(sK7,sK5),k1_funct_1(sK7,sK5)) != k2_relat_1(sK7) ),
    inference(demodulation,[status(thm)],[c_1471,c_25])).

cnf(c_8023,plain,
    ( sK4(sK7,sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK5))) = sK5 ),
    inference(superposition,[status(thm)],[c_7997,c_1520])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK4(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_534,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK4(X1,X0)) = X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_29])).

cnf(c_535,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | k1_funct_1(sK7,sK4(sK7,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_1305,plain,
    ( k1_funct_1(sK7,sK4(sK7,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_535])).

cnf(c_536,plain,
    ( k1_funct_1(sK7,sK4(sK7,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_535])).

cnf(c_1966,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | k1_funct_1(sK7,sK4(sK7,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1305,c_536,c_1463,c_1467])).

cnf(c_1967,plain,
    ( k1_funct_1(sK7,sK4(sK7,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1966])).

cnf(c_2287,plain,
    ( k1_enumset1(X0,X0,X0) = k2_relat_1(sK7)
    | k1_funct_1(sK7,sK4(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0)
    | k2_relat_1(sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1312,c_1967])).

cnf(c_7534,plain,
    ( k1_funct_1(sK7,sK4(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0)
    | k1_enumset1(X0,X0,X0) = k2_relat_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2287,c_1463,c_1466,c_1544,c_1742])).

cnf(c_7535,plain,
    ( k1_enumset1(X0,X0,X0) = k2_relat_1(sK7)
    | k1_funct_1(sK7,sK4(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0) ),
    inference(renaming,[status(thm)],[c_7534])).

cnf(c_7560,plain,
    ( k1_funct_1(sK7,sK4(sK7,sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK5)))) = sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK5)) ),
    inference(superposition,[status(thm)],[c_7535,c_1520])).

cnf(c_8122,plain,
    ( sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK5)) = k1_funct_1(sK7,sK5) ),
    inference(demodulation,[status(thm)],[c_8023,c_7560])).

cnf(c_6,plain,
    ( k1_enumset1(X0,X0,X0) = X1
    | sK1(X1,X0) != X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_8273,plain,
    ( k1_enumset1(k1_funct_1(sK7,sK5),k1_funct_1(sK7,sK5),k1_funct_1(sK7,sK5)) = k2_relat_1(sK7)
    | k2_relat_1(sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8122,c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8273,c_1742,c_1544,c_1520,c_1466,c_1463])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.30  % Computer   : n005.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % WCLimit    : 600
% 0.11/0.30  % DateTime   : Tue Dec  1 19:35:02 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.31  % Running in FOF mode
% 3.33/0.96  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/0.96  
% 3.33/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.33/0.96  
% 3.33/0.96  ------  iProver source info
% 3.33/0.96  
% 3.33/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.33/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.33/0.96  git: non_committed_changes: false
% 3.33/0.96  git: last_make_outside_of_git: false
% 3.33/0.96  
% 3.33/0.96  ------ 
% 3.33/0.96  
% 3.33/0.96  ------ Input Options
% 3.33/0.96  
% 3.33/0.96  --out_options                           all
% 3.33/0.96  --tptp_safe_out                         true
% 3.33/0.96  --problem_path                          ""
% 3.33/0.96  --include_path                          ""
% 3.33/0.96  --clausifier                            res/vclausify_rel
% 3.33/0.96  --clausifier_options                    --mode clausify
% 3.33/0.96  --stdin                                 false
% 3.33/0.96  --stats_out                             all
% 3.33/0.96  
% 3.33/0.96  ------ General Options
% 3.33/0.96  
% 3.33/0.96  --fof                                   false
% 3.33/0.96  --time_out_real                         305.
% 3.33/0.96  --time_out_virtual                      -1.
% 3.33/0.96  --symbol_type_check                     false
% 3.33/0.96  --clausify_out                          false
% 3.33/0.96  --sig_cnt_out                           false
% 3.33/0.96  --trig_cnt_out                          false
% 3.33/0.96  --trig_cnt_out_tolerance                1.
% 3.33/0.96  --trig_cnt_out_sk_spl                   false
% 3.33/0.96  --abstr_cl_out                          false
% 3.33/0.96  
% 3.33/0.96  ------ Global Options
% 3.33/0.96  
% 3.33/0.96  --schedule                              default
% 3.33/0.96  --add_important_lit                     false
% 3.33/0.96  --prop_solver_per_cl                    1000
% 3.33/0.96  --min_unsat_core                        false
% 3.33/0.96  --soft_assumptions                      false
% 3.33/0.96  --soft_lemma_size                       3
% 3.33/0.96  --prop_impl_unit_size                   0
% 3.33/0.96  --prop_impl_unit                        []
% 3.33/0.96  --share_sel_clauses                     true
% 3.33/0.96  --reset_solvers                         false
% 3.33/0.96  --bc_imp_inh                            [conj_cone]
% 3.33/0.96  --conj_cone_tolerance                   3.
% 3.33/0.96  --extra_neg_conj                        none
% 3.33/0.96  --large_theory_mode                     true
% 3.33/0.96  --prolific_symb_bound                   200
% 3.33/0.96  --lt_threshold                          2000
% 3.33/0.96  --clause_weak_htbl                      true
% 3.33/0.96  --gc_record_bc_elim                     false
% 3.33/0.96  
% 3.33/0.96  ------ Preprocessing Options
% 3.33/0.96  
% 3.33/0.96  --preprocessing_flag                    true
% 3.33/0.96  --time_out_prep_mult                    0.1
% 3.33/0.96  --splitting_mode                        input
% 3.33/0.96  --splitting_grd                         true
% 3.33/0.96  --splitting_cvd                         false
% 3.33/0.96  --splitting_cvd_svl                     false
% 3.33/0.96  --splitting_nvd                         32
% 3.33/0.96  --sub_typing                            true
% 3.33/0.96  --prep_gs_sim                           true
% 3.33/0.96  --prep_unflatten                        true
% 3.33/0.96  --prep_res_sim                          true
% 3.33/0.96  --prep_upred                            true
% 3.33/0.96  --prep_sem_filter                       exhaustive
% 3.33/0.96  --prep_sem_filter_out                   false
% 3.33/0.96  --pred_elim                             true
% 3.33/0.96  --res_sim_input                         true
% 3.33/0.96  --eq_ax_congr_red                       true
% 3.33/0.96  --pure_diseq_elim                       true
% 3.33/0.96  --brand_transform                       false
% 3.33/0.96  --non_eq_to_eq                          false
% 3.33/0.96  --prep_def_merge                        true
% 3.33/0.96  --prep_def_merge_prop_impl              false
% 3.33/0.96  --prep_def_merge_mbd                    true
% 3.33/0.96  --prep_def_merge_tr_red                 false
% 3.33/0.96  --prep_def_merge_tr_cl                  false
% 3.33/0.96  --smt_preprocessing                     true
% 3.33/0.96  --smt_ac_axioms                         fast
% 3.33/0.96  --preprocessed_out                      false
% 3.33/0.96  --preprocessed_stats                    false
% 3.33/0.96  
% 3.33/0.96  ------ Abstraction refinement Options
% 3.33/0.96  
% 3.33/0.96  --abstr_ref                             []
% 3.33/0.96  --abstr_ref_prep                        false
% 3.33/0.96  --abstr_ref_until_sat                   false
% 3.33/0.96  --abstr_ref_sig_restrict                funpre
% 3.33/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.33/0.96  --abstr_ref_under                       []
% 3.33/0.96  
% 3.33/0.96  ------ SAT Options
% 3.33/0.96  
% 3.33/0.96  --sat_mode                              false
% 3.33/0.96  --sat_fm_restart_options                ""
% 3.33/0.96  --sat_gr_def                            false
% 3.33/0.96  --sat_epr_types                         true
% 3.33/0.96  --sat_non_cyclic_types                  false
% 3.33/0.96  --sat_finite_models                     false
% 3.33/0.96  --sat_fm_lemmas                         false
% 3.33/0.96  --sat_fm_prep                           false
% 3.33/0.96  --sat_fm_uc_incr                        true
% 3.33/0.96  --sat_out_model                         small
% 3.33/0.96  --sat_out_clauses                       false
% 3.33/0.96  
% 3.33/0.96  ------ QBF Options
% 3.33/0.96  
% 3.33/0.96  --qbf_mode                              false
% 3.33/0.96  --qbf_elim_univ                         false
% 3.33/0.96  --qbf_dom_inst                          none
% 3.33/0.96  --qbf_dom_pre_inst                      false
% 3.33/0.96  --qbf_sk_in                             false
% 3.33/0.96  --qbf_pred_elim                         true
% 3.33/0.96  --qbf_split                             512
% 3.33/0.96  
% 3.33/0.96  ------ BMC1 Options
% 3.33/0.96  
% 3.33/0.96  --bmc1_incremental                      false
% 3.33/0.96  --bmc1_axioms                           reachable_all
% 3.33/0.96  --bmc1_min_bound                        0
% 3.33/0.96  --bmc1_max_bound                        -1
% 3.33/0.96  --bmc1_max_bound_default                -1
% 3.33/0.96  --bmc1_symbol_reachability              true
% 3.33/0.96  --bmc1_property_lemmas                  false
% 3.33/0.96  --bmc1_k_induction                      false
% 3.33/0.96  --bmc1_non_equiv_states                 false
% 3.33/0.96  --bmc1_deadlock                         false
% 3.33/0.96  --bmc1_ucm                              false
% 3.33/0.96  --bmc1_add_unsat_core                   none
% 3.33/0.96  --bmc1_unsat_core_children              false
% 3.33/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.33/0.96  --bmc1_out_stat                         full
% 3.33/0.96  --bmc1_ground_init                      false
% 3.33/0.96  --bmc1_pre_inst_next_state              false
% 3.33/0.96  --bmc1_pre_inst_state                   false
% 3.33/0.96  --bmc1_pre_inst_reach_state             false
% 3.33/0.96  --bmc1_out_unsat_core                   false
% 3.33/0.96  --bmc1_aig_witness_out                  false
% 3.33/0.96  --bmc1_verbose                          false
% 3.33/0.96  --bmc1_dump_clauses_tptp                false
% 3.33/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.33/0.96  --bmc1_dump_file                        -
% 3.33/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.33/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.33/0.96  --bmc1_ucm_extend_mode                  1
% 3.33/0.96  --bmc1_ucm_init_mode                    2
% 3.33/0.96  --bmc1_ucm_cone_mode                    none
% 3.33/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.33/0.96  --bmc1_ucm_relax_model                  4
% 3.33/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.33/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.33/0.96  --bmc1_ucm_layered_model                none
% 3.33/0.96  --bmc1_ucm_max_lemma_size               10
% 3.33/0.96  
% 3.33/0.96  ------ AIG Options
% 3.33/0.96  
% 3.33/0.96  --aig_mode                              false
% 3.33/0.96  
% 3.33/0.96  ------ Instantiation Options
% 3.33/0.96  
% 3.33/0.96  --instantiation_flag                    true
% 3.33/0.96  --inst_sos_flag                         false
% 3.33/0.96  --inst_sos_phase                        true
% 3.33/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.33/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.33/0.96  --inst_lit_sel_side                     num_symb
% 3.33/0.96  --inst_solver_per_active                1400
% 3.33/0.96  --inst_solver_calls_frac                1.
% 3.33/0.96  --inst_passive_queue_type               priority_queues
% 3.33/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.33/0.96  --inst_passive_queues_freq              [25;2]
% 3.33/0.96  --inst_dismatching                      true
% 3.33/0.96  --inst_eager_unprocessed_to_passive     true
% 3.33/0.96  --inst_prop_sim_given                   true
% 3.33/0.96  --inst_prop_sim_new                     false
% 3.33/0.96  --inst_subs_new                         false
% 3.33/0.96  --inst_eq_res_simp                      false
% 3.33/0.96  --inst_subs_given                       false
% 3.33/0.96  --inst_orphan_elimination               true
% 3.33/0.96  --inst_learning_loop_flag               true
% 3.33/0.96  --inst_learning_start                   3000
% 3.33/0.96  --inst_learning_factor                  2
% 3.33/0.96  --inst_start_prop_sim_after_learn       3
% 3.33/0.96  --inst_sel_renew                        solver
% 3.33/0.96  --inst_lit_activity_flag                true
% 3.33/0.96  --inst_restr_to_given                   false
% 3.33/0.96  --inst_activity_threshold               500
% 3.33/0.96  --inst_out_proof                        true
% 3.33/0.96  
% 3.33/0.96  ------ Resolution Options
% 3.33/0.96  
% 3.33/0.96  --resolution_flag                       true
% 3.33/0.96  --res_lit_sel                           adaptive
% 3.33/0.96  --res_lit_sel_side                      none
% 3.33/0.96  --res_ordering                          kbo
% 3.33/0.96  --res_to_prop_solver                    active
% 3.33/0.96  --res_prop_simpl_new                    false
% 3.33/0.96  --res_prop_simpl_given                  true
% 3.33/0.96  --res_passive_queue_type                priority_queues
% 3.33/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.33/0.96  --res_passive_queues_freq               [15;5]
% 3.33/0.96  --res_forward_subs                      full
% 3.33/0.96  --res_backward_subs                     full
% 3.33/0.96  --res_forward_subs_resolution           true
% 3.33/0.96  --res_backward_subs_resolution          true
% 3.33/0.96  --res_orphan_elimination                true
% 3.33/0.96  --res_time_limit                        2.
% 3.33/0.96  --res_out_proof                         true
% 3.33/0.96  
% 3.33/0.96  ------ Superposition Options
% 3.33/0.96  
% 3.33/0.96  --superposition_flag                    true
% 3.33/0.96  --sup_passive_queue_type                priority_queues
% 3.33/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.33/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.33/0.96  --demod_completeness_check              fast
% 3.33/0.96  --demod_use_ground                      true
% 3.33/0.96  --sup_to_prop_solver                    passive
% 3.33/0.96  --sup_prop_simpl_new                    true
% 3.33/0.96  --sup_prop_simpl_given                  true
% 3.33/0.96  --sup_fun_splitting                     false
% 3.33/0.96  --sup_smt_interval                      50000
% 3.33/0.96  
% 3.33/0.96  ------ Superposition Simplification Setup
% 3.33/0.96  
% 3.33/0.96  --sup_indices_passive                   []
% 3.33/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.33/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/0.96  --sup_full_bw                           [BwDemod]
% 3.33/0.96  --sup_immed_triv                        [TrivRules]
% 3.33/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.33/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/0.96  --sup_immed_bw_main                     []
% 3.33/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.33/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/0.96  
% 3.33/0.96  ------ Combination Options
% 3.33/0.96  
% 3.33/0.96  --comb_res_mult                         3
% 3.33/0.96  --comb_sup_mult                         2
% 3.33/0.96  --comb_inst_mult                        10
% 3.33/0.96  
% 3.33/0.96  ------ Debug Options
% 3.33/0.96  
% 3.33/0.96  --dbg_backtrace                         false
% 3.33/0.96  --dbg_dump_prop_clauses                 false
% 3.33/0.96  --dbg_dump_prop_clauses_file            -
% 3.33/0.96  --dbg_out_stat                          false
% 3.33/0.96  ------ Parsing...
% 3.33/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.33/0.96  
% 3.33/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.33/0.96  
% 3.33/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.33/0.96  
% 3.33/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.33/0.96  ------ Proving...
% 3.33/0.96  ------ Problem Properties 
% 3.33/0.96  
% 3.33/0.96  
% 3.33/0.96  clauses                                 22
% 3.33/0.96  conjectures                             2
% 3.33/0.96  EPR                                     1
% 3.33/0.96  Horn                                    16
% 3.33/0.96  unary                                   5
% 3.33/0.96  binary                                  4
% 3.33/0.96  lits                                    57
% 3.33/0.96  lits eq                                 33
% 3.33/0.96  fd_pure                                 0
% 3.33/0.96  fd_pseudo                               0
% 3.33/0.96  fd_cond                                 3
% 3.33/0.96  fd_pseudo_cond                          4
% 3.33/0.96  AC symbols                              0
% 3.33/0.96  
% 3.33/0.96  ------ Schedule dynamic 5 is on 
% 3.33/0.96  
% 3.33/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.33/0.96  
% 3.33/0.96  
% 3.33/0.96  ------ 
% 3.33/0.96  Current options:
% 3.33/0.96  ------ 
% 3.33/0.96  
% 3.33/0.96  ------ Input Options
% 3.33/0.96  
% 3.33/0.96  --out_options                           all
% 3.33/0.96  --tptp_safe_out                         true
% 3.33/0.96  --problem_path                          ""
% 3.33/0.96  --include_path                          ""
% 3.33/0.96  --clausifier                            res/vclausify_rel
% 3.33/0.96  --clausifier_options                    --mode clausify
% 3.33/0.96  --stdin                                 false
% 3.33/0.96  --stats_out                             all
% 3.33/0.96  
% 3.33/0.96  ------ General Options
% 3.33/0.96  
% 3.33/0.96  --fof                                   false
% 3.33/0.96  --time_out_real                         305.
% 3.33/0.96  --time_out_virtual                      -1.
% 3.33/0.96  --symbol_type_check                     false
% 3.33/0.96  --clausify_out                          false
% 3.33/0.96  --sig_cnt_out                           false
% 3.33/0.96  --trig_cnt_out                          false
% 3.33/0.96  --trig_cnt_out_tolerance                1.
% 3.33/0.96  --trig_cnt_out_sk_spl                   false
% 3.33/0.96  --abstr_cl_out                          false
% 3.33/0.96  
% 3.33/0.96  ------ Global Options
% 3.33/0.96  
% 3.33/0.96  --schedule                              default
% 3.33/0.96  --add_important_lit                     false
% 3.33/0.96  --prop_solver_per_cl                    1000
% 3.33/0.96  --min_unsat_core                        false
% 3.33/0.96  --soft_assumptions                      false
% 3.33/0.96  --soft_lemma_size                       3
% 3.33/0.96  --prop_impl_unit_size                   0
% 3.33/0.96  --prop_impl_unit                        []
% 3.33/0.96  --share_sel_clauses                     true
% 3.33/0.96  --reset_solvers                         false
% 3.33/0.96  --bc_imp_inh                            [conj_cone]
% 3.33/0.96  --conj_cone_tolerance                   3.
% 3.33/0.96  --extra_neg_conj                        none
% 3.33/0.96  --large_theory_mode                     true
% 3.33/0.96  --prolific_symb_bound                   200
% 3.33/0.96  --lt_threshold                          2000
% 3.33/0.96  --clause_weak_htbl                      true
% 3.33/0.96  --gc_record_bc_elim                     false
% 3.33/0.96  
% 3.33/0.96  ------ Preprocessing Options
% 3.33/0.96  
% 3.33/0.96  --preprocessing_flag                    true
% 3.33/0.96  --time_out_prep_mult                    0.1
% 3.33/0.96  --splitting_mode                        input
% 3.33/0.96  --splitting_grd                         true
% 3.33/0.96  --splitting_cvd                         false
% 3.33/0.96  --splitting_cvd_svl                     false
% 3.33/0.96  --splitting_nvd                         32
% 3.33/0.96  --sub_typing                            true
% 3.33/0.96  --prep_gs_sim                           true
% 3.33/0.96  --prep_unflatten                        true
% 3.33/0.96  --prep_res_sim                          true
% 3.33/0.96  --prep_upred                            true
% 3.33/0.96  --prep_sem_filter                       exhaustive
% 3.33/0.96  --prep_sem_filter_out                   false
% 3.33/0.96  --pred_elim                             true
% 3.33/0.96  --res_sim_input                         true
% 3.33/0.96  --eq_ax_congr_red                       true
% 3.33/0.96  --pure_diseq_elim                       true
% 3.33/0.96  --brand_transform                       false
% 3.33/0.96  --non_eq_to_eq                          false
% 3.33/0.96  --prep_def_merge                        true
% 3.33/0.96  --prep_def_merge_prop_impl              false
% 3.33/0.96  --prep_def_merge_mbd                    true
% 3.33/0.96  --prep_def_merge_tr_red                 false
% 3.33/0.96  --prep_def_merge_tr_cl                  false
% 3.33/0.96  --smt_preprocessing                     true
% 3.33/0.96  --smt_ac_axioms                         fast
% 3.33/0.96  --preprocessed_out                      false
% 3.33/0.96  --preprocessed_stats                    false
% 3.33/0.96  
% 3.33/0.96  ------ Abstraction refinement Options
% 3.33/0.96  
% 3.33/0.96  --abstr_ref                             []
% 3.33/0.96  --abstr_ref_prep                        false
% 3.33/0.96  --abstr_ref_until_sat                   false
% 3.33/0.96  --abstr_ref_sig_restrict                funpre
% 3.33/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.33/0.96  --abstr_ref_under                       []
% 3.33/0.96  
% 3.33/0.96  ------ SAT Options
% 3.33/0.96  
% 3.33/0.96  --sat_mode                              false
% 3.33/0.96  --sat_fm_restart_options                ""
% 3.33/0.96  --sat_gr_def                            false
% 3.33/0.96  --sat_epr_types                         true
% 3.33/0.96  --sat_non_cyclic_types                  false
% 3.33/0.96  --sat_finite_models                     false
% 3.33/0.96  --sat_fm_lemmas                         false
% 3.33/0.96  --sat_fm_prep                           false
% 3.33/0.96  --sat_fm_uc_incr                        true
% 3.33/0.96  --sat_out_model                         small
% 3.33/0.96  --sat_out_clauses                       false
% 3.33/0.96  
% 3.33/0.96  ------ QBF Options
% 3.33/0.96  
% 3.33/0.96  --qbf_mode                              false
% 3.33/0.96  --qbf_elim_univ                         false
% 3.33/0.96  --qbf_dom_inst                          none
% 3.33/0.96  --qbf_dom_pre_inst                      false
% 3.33/0.96  --qbf_sk_in                             false
% 3.33/0.96  --qbf_pred_elim                         true
% 3.33/0.96  --qbf_split                             512
% 3.33/0.96  
% 3.33/0.96  ------ BMC1 Options
% 3.33/0.96  
% 3.33/0.96  --bmc1_incremental                      false
% 3.33/0.96  --bmc1_axioms                           reachable_all
% 3.33/0.96  --bmc1_min_bound                        0
% 3.33/0.96  --bmc1_max_bound                        -1
% 3.33/0.96  --bmc1_max_bound_default                -1
% 3.33/0.96  --bmc1_symbol_reachability              true
% 3.33/0.96  --bmc1_property_lemmas                  false
% 3.33/0.96  --bmc1_k_induction                      false
% 3.33/0.96  --bmc1_non_equiv_states                 false
% 3.33/0.96  --bmc1_deadlock                         false
% 3.33/0.96  --bmc1_ucm                              false
% 3.33/0.96  --bmc1_add_unsat_core                   none
% 3.33/0.96  --bmc1_unsat_core_children              false
% 3.33/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.33/0.96  --bmc1_out_stat                         full
% 3.33/0.96  --bmc1_ground_init                      false
% 3.33/0.96  --bmc1_pre_inst_next_state              false
% 3.33/0.96  --bmc1_pre_inst_state                   false
% 3.33/0.96  --bmc1_pre_inst_reach_state             false
% 3.33/0.96  --bmc1_out_unsat_core                   false
% 3.33/0.96  --bmc1_aig_witness_out                  false
% 3.33/0.96  --bmc1_verbose                          false
% 3.33/0.96  --bmc1_dump_clauses_tptp                false
% 3.33/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.33/0.96  --bmc1_dump_file                        -
% 3.33/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.33/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.33/0.96  --bmc1_ucm_extend_mode                  1
% 3.33/0.96  --bmc1_ucm_init_mode                    2
% 3.33/0.96  --bmc1_ucm_cone_mode                    none
% 3.33/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.33/0.96  --bmc1_ucm_relax_model                  4
% 3.33/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.33/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.33/0.96  --bmc1_ucm_layered_model                none
% 3.33/0.96  --bmc1_ucm_max_lemma_size               10
% 3.33/0.96  
% 3.33/0.96  ------ AIG Options
% 3.33/0.96  
% 3.33/0.96  --aig_mode                              false
% 3.33/0.96  
% 3.33/0.96  ------ Instantiation Options
% 3.33/0.96  
% 3.33/0.96  --instantiation_flag                    true
% 3.33/0.96  --inst_sos_flag                         false
% 3.33/0.96  --inst_sos_phase                        true
% 3.33/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.33/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.33/0.96  --inst_lit_sel_side                     none
% 3.33/0.96  --inst_solver_per_active                1400
% 3.33/0.96  --inst_solver_calls_frac                1.
% 3.33/0.96  --inst_passive_queue_type               priority_queues
% 3.33/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.33/0.96  --inst_passive_queues_freq              [25;2]
% 3.33/0.96  --inst_dismatching                      true
% 3.33/0.96  --inst_eager_unprocessed_to_passive     true
% 3.33/0.96  --inst_prop_sim_given                   true
% 3.33/0.96  --inst_prop_sim_new                     false
% 3.33/0.96  --inst_subs_new                         false
% 3.33/0.96  --inst_eq_res_simp                      false
% 3.33/0.96  --inst_subs_given                       false
% 3.33/0.96  --inst_orphan_elimination               true
% 3.33/0.96  --inst_learning_loop_flag               true
% 3.33/0.96  --inst_learning_start                   3000
% 3.33/0.96  --inst_learning_factor                  2
% 3.33/0.96  --inst_start_prop_sim_after_learn       3
% 3.33/0.96  --inst_sel_renew                        solver
% 3.33/0.96  --inst_lit_activity_flag                true
% 3.33/0.96  --inst_restr_to_given                   false
% 3.33/0.96  --inst_activity_threshold               500
% 3.33/0.96  --inst_out_proof                        true
% 3.33/0.96  
% 3.33/0.96  ------ Resolution Options
% 3.33/0.96  
% 3.33/0.96  --resolution_flag                       false
% 3.33/0.96  --res_lit_sel                           adaptive
% 3.33/0.96  --res_lit_sel_side                      none
% 3.33/0.96  --res_ordering                          kbo
% 3.33/0.96  --res_to_prop_solver                    active
% 3.33/0.96  --res_prop_simpl_new                    false
% 3.33/0.96  --res_prop_simpl_given                  true
% 3.33/0.96  --res_passive_queue_type                priority_queues
% 3.33/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.33/0.96  --res_passive_queues_freq               [15;5]
% 3.33/0.96  --res_forward_subs                      full
% 3.33/0.96  --res_backward_subs                     full
% 3.33/0.96  --res_forward_subs_resolution           true
% 3.33/0.96  --res_backward_subs_resolution          true
% 3.33/0.96  --res_orphan_elimination                true
% 3.33/0.96  --res_time_limit                        2.
% 3.33/0.96  --res_out_proof                         true
% 3.33/0.96  
% 3.33/0.96  ------ Superposition Options
% 3.33/0.96  
% 3.33/0.96  --superposition_flag                    true
% 3.33/0.96  --sup_passive_queue_type                priority_queues
% 3.33/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.33/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.33/0.96  --demod_completeness_check              fast
% 3.33/0.96  --demod_use_ground                      true
% 3.33/0.96  --sup_to_prop_solver                    passive
% 3.33/0.96  --sup_prop_simpl_new                    true
% 3.33/0.96  --sup_prop_simpl_given                  true
% 3.33/0.96  --sup_fun_splitting                     false
% 3.33/0.96  --sup_smt_interval                      50000
% 3.33/0.96  
% 3.33/0.96  ------ Superposition Simplification Setup
% 3.33/0.96  
% 3.33/0.96  --sup_indices_passive                   []
% 3.33/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.33/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/0.96  --sup_full_bw                           [BwDemod]
% 3.33/0.96  --sup_immed_triv                        [TrivRules]
% 3.33/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.33/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/0.96  --sup_immed_bw_main                     []
% 3.33/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.33/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/0.96  
% 3.33/0.96  ------ Combination Options
% 3.33/0.96  
% 3.33/0.96  --comb_res_mult                         3
% 3.33/0.96  --comb_sup_mult                         2
% 3.33/0.96  --comb_inst_mult                        10
% 3.33/0.96  
% 3.33/0.96  ------ Debug Options
% 3.33/0.96  
% 3.33/0.96  --dbg_backtrace                         false
% 3.33/0.96  --dbg_dump_prop_clauses                 false
% 3.33/0.96  --dbg_dump_prop_clauses_file            -
% 3.33/0.96  --dbg_out_stat                          false
% 3.33/0.96  
% 3.33/0.96  
% 3.33/0.96  
% 3.33/0.96  
% 3.33/0.96  ------ Proving...
% 3.33/0.96  
% 3.33/0.96  
% 3.33/0.96  % SZS status Theorem for theBenchmark.p
% 3.33/0.96  
% 3.33/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 3.33/0.96  
% 3.33/0.96  fof(f6,axiom,(
% 3.33/0.96    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 3.33/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/0.96  
% 3.33/0.96  fof(f15,plain,(
% 3.33/0.96    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 3.33/0.96    inference(ennf_transformation,[],[f6])).
% 3.33/0.96  
% 3.33/0.96  fof(f30,plain,(
% 3.33/0.96    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK1(X0,X1) != X1 & r2_hidden(sK1(X0,X1),X0)))),
% 3.33/0.96    introduced(choice_axiom,[])).
% 3.33/0.96  
% 3.33/0.96  fof(f31,plain,(
% 3.33/0.96    ! [X0,X1] : ((sK1(X0,X1) != X1 & r2_hidden(sK1(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 3.33/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f30])).
% 3.33/0.96  
% 3.33/0.96  fof(f50,plain,(
% 3.33/0.96    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 3.33/0.96    inference(cnf_transformation,[],[f31])).
% 3.33/0.96  
% 3.33/0.96  fof(f3,axiom,(
% 3.33/0.96    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.33/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/0.96  
% 3.33/0.96  fof(f47,plain,(
% 3.33/0.96    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.33/0.96    inference(cnf_transformation,[],[f3])).
% 3.33/0.96  
% 3.33/0.96  fof(f4,axiom,(
% 3.33/0.96    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.33/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/0.96  
% 3.33/0.96  fof(f48,plain,(
% 3.33/0.96    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.33/0.96    inference(cnf_transformation,[],[f4])).
% 3.33/0.96  
% 3.33/0.96  fof(f74,plain,(
% 3.33/0.96    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 3.33/0.96    inference(definition_unfolding,[],[f47,f48])).
% 3.33/0.96  
% 3.33/0.96  fof(f81,plain,(
% 3.33/0.96    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | k1_enumset1(X1,X1,X1) = X0) )),
% 3.33/0.96    inference(definition_unfolding,[],[f50,f74])).
% 3.33/0.96  
% 3.33/0.96  fof(f8,axiom,(
% 3.33/0.96    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.33/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/0.96  
% 3.33/0.96  fof(f17,plain,(
% 3.33/0.96    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.33/0.96    inference(ennf_transformation,[],[f8])).
% 3.33/0.96  
% 3.33/0.96  fof(f18,plain,(
% 3.33/0.96    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.33/0.96    inference(flattening,[],[f17])).
% 3.33/0.96  
% 3.33/0.96  fof(f33,plain,(
% 3.33/0.96    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.33/0.96    inference(nnf_transformation,[],[f18])).
% 3.33/0.96  
% 3.33/0.96  fof(f34,plain,(
% 3.33/0.96    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.33/0.96    inference(rectify,[],[f33])).
% 3.33/0.96  
% 3.33/0.96  fof(f37,plain,(
% 3.33/0.96    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))))),
% 3.33/0.96    introduced(choice_axiom,[])).
% 3.33/0.96  
% 3.33/0.96  fof(f36,plain,(
% 3.33/0.96    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1)) = X2 & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))) )),
% 3.33/0.96    introduced(choice_axiom,[])).
% 3.33/0.96  
% 3.33/0.96  fof(f35,plain,(
% 3.33/0.96    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1))))),
% 3.33/0.96    introduced(choice_axiom,[])).
% 3.33/0.96  
% 3.33/0.96  fof(f38,plain,(
% 3.33/0.96    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & ((k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.33/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f34,f37,f36,f35])).
% 3.33/0.96  
% 3.33/0.96  fof(f54,plain,(
% 3.33/0.96    ( ! [X0,X5,X1] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.33/0.96    inference(cnf_transformation,[],[f38])).
% 3.33/0.96  
% 3.33/0.96  fof(f91,plain,(
% 3.33/0.96    ( ! [X0,X5] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.33/0.96    inference(equality_resolution,[],[f54])).
% 3.33/0.96  
% 3.33/0.96  fof(f13,conjecture,(
% 3.33/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 3.33/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/0.96  
% 3.33/0.96  fof(f14,negated_conjecture,(
% 3.33/0.96    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 3.33/0.96    inference(negated_conjecture,[],[f13])).
% 3.33/0.96  
% 3.33/0.96  fof(f24,plain,(
% 3.33/0.96    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 3.33/0.96    inference(ennf_transformation,[],[f14])).
% 3.33/0.96  
% 3.33/0.96  fof(f25,plain,(
% 3.33/0.96    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 3.33/0.96    inference(flattening,[],[f24])).
% 3.33/0.96  
% 3.33/0.96  fof(f40,plain,(
% 3.33/0.96    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK7,sK5)) != k2_relset_1(k1_tarski(sK5),sK6,sK7) & k1_xboole_0 != sK6 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6))) & v1_funct_2(sK7,k1_tarski(sK5),sK6) & v1_funct_1(sK7))),
% 3.33/0.96    introduced(choice_axiom,[])).
% 3.33/0.96  
% 3.33/0.96  fof(f41,plain,(
% 3.33/0.96    k1_tarski(k1_funct_1(sK7,sK5)) != k2_relset_1(k1_tarski(sK5),sK6,sK7) & k1_xboole_0 != sK6 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6))) & v1_funct_2(sK7,k1_tarski(sK5),sK6) & v1_funct_1(sK7)),
% 3.33/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f25,f40])).
% 3.33/0.96  
% 3.33/0.96  fof(f69,plain,(
% 3.33/0.96    v1_funct_1(sK7)),
% 3.33/0.96    inference(cnf_transformation,[],[f41])).
% 3.33/0.96  
% 3.33/0.96  fof(f9,axiom,(
% 3.33/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.33/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/0.96  
% 3.33/0.96  fof(f19,plain,(
% 3.33/0.96    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/0.96    inference(ennf_transformation,[],[f9])).
% 3.33/0.96  
% 3.33/0.96  fof(f60,plain,(
% 3.33/0.96    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/0.96    inference(cnf_transformation,[],[f19])).
% 3.33/0.96  
% 3.33/0.96  fof(f71,plain,(
% 3.33/0.96    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6)))),
% 3.33/0.96    inference(cnf_transformation,[],[f41])).
% 3.33/0.96  
% 3.33/0.96  fof(f83,plain,(
% 3.33/0.96    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)))),
% 3.33/0.96    inference(definition_unfolding,[],[f71,f74])).
% 3.33/0.96  
% 3.33/0.96  fof(f70,plain,(
% 3.33/0.96    v1_funct_2(sK7,k1_tarski(sK5),sK6)),
% 3.33/0.96    inference(cnf_transformation,[],[f41])).
% 3.33/0.96  
% 3.33/0.96  fof(f84,plain,(
% 3.33/0.96    v1_funct_2(sK7,k1_enumset1(sK5,sK5,sK5),sK6)),
% 3.33/0.96    inference(definition_unfolding,[],[f70,f74])).
% 3.33/0.96  
% 3.33/0.96  fof(f12,axiom,(
% 3.33/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.33/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/0.96  
% 3.33/0.96  fof(f22,plain,(
% 3.33/0.96    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/0.96    inference(ennf_transformation,[],[f12])).
% 3.33/0.96  
% 3.33/0.96  fof(f23,plain,(
% 3.33/0.96    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/0.96    inference(flattening,[],[f22])).
% 3.33/0.96  
% 3.33/0.96  fof(f39,plain,(
% 3.33/0.96    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/0.96    inference(nnf_transformation,[],[f23])).
% 3.33/0.96  
% 3.33/0.96  fof(f63,plain,(
% 3.33/0.96    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/0.96    inference(cnf_transformation,[],[f39])).
% 3.33/0.96  
% 3.33/0.96  fof(f72,plain,(
% 3.33/0.96    k1_xboole_0 != sK6),
% 3.33/0.96    inference(cnf_transformation,[],[f41])).
% 3.33/0.96  
% 3.33/0.96  fof(f10,axiom,(
% 3.33/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.33/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/0.96  
% 3.33/0.96  fof(f20,plain,(
% 3.33/0.96    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/0.96    inference(ennf_transformation,[],[f10])).
% 3.33/0.96  
% 3.33/0.96  fof(f61,plain,(
% 3.33/0.96    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/0.96    inference(cnf_transformation,[],[f20])).
% 3.33/0.96  
% 3.33/0.96  fof(f2,axiom,(
% 3.33/0.96    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.33/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/0.96  
% 3.33/0.96  fof(f26,plain,(
% 3.33/0.96    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.33/0.96    inference(nnf_transformation,[],[f2])).
% 3.33/0.96  
% 3.33/0.96  fof(f27,plain,(
% 3.33/0.96    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.33/0.96    inference(rectify,[],[f26])).
% 3.33/0.96  
% 3.33/0.96  fof(f28,plain,(
% 3.33/0.96    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 3.33/0.96    introduced(choice_axiom,[])).
% 3.33/0.96  
% 3.33/0.96  fof(f29,plain,(
% 3.33/0.96    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.33/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 3.33/0.96  
% 3.33/0.96  fof(f43,plain,(
% 3.33/0.96    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.33/0.96    inference(cnf_transformation,[],[f29])).
% 3.33/0.96  
% 3.33/0.96  fof(f78,plain,(
% 3.33/0.96    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 3.33/0.96    inference(definition_unfolding,[],[f43,f74])).
% 3.33/0.96  
% 3.33/0.96  fof(f87,plain,(
% 3.33/0.96    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_enumset1(X0,X0,X0))) )),
% 3.33/0.96    inference(equality_resolution,[],[f78])).
% 3.33/0.96  
% 3.33/0.96  fof(f7,axiom,(
% 3.33/0.96    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 3.33/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/0.96  
% 3.33/0.96  fof(f16,plain,(
% 3.33/0.96    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.33/0.96    inference(ennf_transformation,[],[f7])).
% 3.33/0.96  
% 3.33/0.96  fof(f32,plain,(
% 3.33/0.96    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.33/0.96    inference(nnf_transformation,[],[f16])).
% 3.33/0.96  
% 3.33/0.96  fof(f53,plain,(
% 3.33/0.96    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.33/0.96    inference(cnf_transformation,[],[f32])).
% 3.33/0.96  
% 3.33/0.96  fof(f1,axiom,(
% 3.33/0.96    v1_xboole_0(k1_xboole_0)),
% 3.33/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/0.96  
% 3.33/0.96  fof(f42,plain,(
% 3.33/0.96    v1_xboole_0(k1_xboole_0)),
% 3.33/0.96    inference(cnf_transformation,[],[f1])).
% 3.33/0.96  
% 3.33/0.96  fof(f5,axiom,(
% 3.33/0.96    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 3.33/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/0.96  
% 3.33/0.96  fof(f49,plain,(
% 3.33/0.96    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 3.33/0.96    inference(cnf_transformation,[],[f5])).
% 3.33/0.96  
% 3.33/0.96  fof(f79,plain,(
% 3.33/0.96    ( ! [X0] : (~v1_xboole_0(k1_enumset1(X0,X0,X0))) )),
% 3.33/0.96    inference(definition_unfolding,[],[f49,f74])).
% 3.33/0.96  
% 3.33/0.96  fof(f11,axiom,(
% 3.33/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.33/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/0.96  
% 3.33/0.96  fof(f21,plain,(
% 3.33/0.96    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/0.96    inference(ennf_transformation,[],[f11])).
% 3.33/0.96  
% 3.33/0.96  fof(f62,plain,(
% 3.33/0.96    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/0.96    inference(cnf_transformation,[],[f21])).
% 3.33/0.96  
% 3.33/0.96  fof(f73,plain,(
% 3.33/0.96    k1_tarski(k1_funct_1(sK7,sK5)) != k2_relset_1(k1_tarski(sK5),sK6,sK7)),
% 3.33/0.96    inference(cnf_transformation,[],[f41])).
% 3.33/0.96  
% 3.33/0.96  fof(f82,plain,(
% 3.33/0.96    k1_enumset1(k1_funct_1(sK7,sK5),k1_funct_1(sK7,sK5),k1_funct_1(sK7,sK5)) != k2_relset_1(k1_enumset1(sK5,sK5,sK5),sK6,sK7)),
% 3.33/0.96    inference(definition_unfolding,[],[f73,f74,f74])).
% 3.33/0.96  
% 3.33/0.96  fof(f55,plain,(
% 3.33/0.96    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.33/0.96    inference(cnf_transformation,[],[f38])).
% 3.33/0.96  
% 3.33/0.96  fof(f90,plain,(
% 3.33/0.96    ( ! [X0,X5] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.33/0.96    inference(equality_resolution,[],[f55])).
% 3.33/0.96  
% 3.33/0.96  fof(f51,plain,(
% 3.33/0.96    ( ! [X0,X1] : (sK1(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 3.33/0.96    inference(cnf_transformation,[],[f31])).
% 3.33/0.96  
% 3.33/0.96  fof(f80,plain,(
% 3.33/0.96    ( ! [X0,X1] : (sK1(X0,X1) != X1 | k1_xboole_0 = X0 | k1_enumset1(X1,X1,X1) = X0) )),
% 3.33/0.96    inference(definition_unfolding,[],[f51,f74])).
% 3.33/0.96  
% 3.33/0.96  cnf(c_7,plain,
% 3.33/0.96      ( r2_hidden(sK1(X0,X1),X0)
% 3.33/0.96      | k1_enumset1(X1,X1,X1) = X0
% 3.33/0.96      | k1_xboole_0 = X0 ),
% 3.33/0.96      inference(cnf_transformation,[],[f81]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_1312,plain,
% 3.33/0.96      ( k1_enumset1(X0,X0,X0) = X1
% 3.33/0.96      | k1_xboole_0 = X1
% 3.33/0.96      | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
% 3.33/0.96      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_15,plain,
% 3.33/0.96      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.33/0.96      | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
% 3.33/0.96      | ~ v1_funct_1(X1)
% 3.33/0.96      | ~ v1_relat_1(X1) ),
% 3.33/0.96      inference(cnf_transformation,[],[f91]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_29,negated_conjecture,
% 3.33/0.96      ( v1_funct_1(sK7) ),
% 3.33/0.96      inference(cnf_transformation,[],[f69]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_519,plain,
% 3.33/0.96      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.33/0.96      | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
% 3.33/0.96      | ~ v1_relat_1(X1)
% 3.33/0.96      | sK7 != X1 ),
% 3.33/0.96      inference(resolution_lifted,[status(thm)],[c_15,c_29]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_520,plain,
% 3.33/0.96      ( ~ r2_hidden(X0,k2_relat_1(sK7))
% 3.33/0.96      | r2_hidden(sK4(sK7,X0),k1_relat_1(sK7))
% 3.33/0.96      | ~ v1_relat_1(sK7) ),
% 3.33/0.96      inference(unflattening,[status(thm)],[c_519]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_1306,plain,
% 3.33/0.96      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 3.33/0.96      | r2_hidden(sK4(sK7,X0),k1_relat_1(sK7)) = iProver_top
% 3.33/0.96      | v1_relat_1(sK7) != iProver_top ),
% 3.33/0.96      inference(predicate_to_equality,[status(thm)],[c_520]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_521,plain,
% 3.33/0.96      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 3.33/0.96      | r2_hidden(sK4(sK7,X0),k1_relat_1(sK7)) = iProver_top
% 3.33/0.96      | v1_relat_1(sK7) != iProver_top ),
% 3.33/0.96      inference(predicate_to_equality,[status(thm)],[c_520]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_1047,plain,( X0 = X0 ),theory(equality) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_1463,plain,
% 3.33/0.96      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) = k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) ),
% 3.33/0.96      inference(instantiation,[status(thm)],[c_1047]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_16,plain,
% 3.33/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/0.96      | v1_relat_1(X0) ),
% 3.33/0.96      inference(cnf_transformation,[],[f60]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_27,negated_conjecture,
% 3.33/0.96      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6))) ),
% 3.33/0.96      inference(cnf_transformation,[],[f83]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_371,plain,
% 3.33/0.96      ( v1_relat_1(X0)
% 3.33/0.96      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.33/0.96      | sK7 != X0 ),
% 3.33/0.96      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_372,plain,
% 3.33/0.96      ( v1_relat_1(sK7)
% 3.33/0.96      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.33/0.96      inference(unflattening,[status(thm)],[c_371]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_1466,plain,
% 3.33/0.96      ( v1_relat_1(sK7)
% 3.33/0.96      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) ),
% 3.33/0.96      inference(instantiation,[status(thm)],[c_372]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_1467,plain,
% 3.33/0.96      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6))
% 3.33/0.96      | v1_relat_1(sK7) = iProver_top ),
% 3.33/0.96      inference(predicate_to_equality,[status(thm)],[c_1466]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_2080,plain,
% 3.33/0.96      ( r2_hidden(sK4(sK7,X0),k1_relat_1(sK7)) = iProver_top
% 3.33/0.96      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 3.33/0.96      inference(global_propositional_subsumption,
% 3.33/0.96                [status(thm)],
% 3.33/0.96                [c_1306,c_521,c_1463,c_1467]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_2081,plain,
% 3.33/0.96      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 3.33/0.96      | r2_hidden(sK4(sK7,X0),k1_relat_1(sK7)) = iProver_top ),
% 3.33/0.96      inference(renaming,[status(thm)],[c_2080]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_28,negated_conjecture,
% 3.33/0.96      ( v1_funct_2(sK7,k1_enumset1(sK5,sK5,sK5),sK6) ),
% 3.33/0.96      inference(cnf_transformation,[],[f84]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_24,plain,
% 3.33/0.96      ( ~ v1_funct_2(X0,X1,X2)
% 3.33/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/0.96      | k1_relset_1(X1,X2,X0) = X1
% 3.33/0.96      | k1_xboole_0 = X2 ),
% 3.33/0.96      inference(cnf_transformation,[],[f63]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_317,plain,
% 3.33/0.96      ( ~ v1_funct_2(X0,X1,X2)
% 3.33/0.96      | k1_relset_1(X1,X2,X0) = X1
% 3.33/0.96      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.33/0.96      | sK7 != X0
% 3.33/0.96      | k1_xboole_0 = X2 ),
% 3.33/0.96      inference(resolution_lifted,[status(thm)],[c_24,c_27]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_318,plain,
% 3.33/0.96      ( ~ v1_funct_2(sK7,X0,X1)
% 3.33/0.96      | k1_relset_1(X0,X1,sK7) = X0
% 3.33/0.96      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.33/0.96      | k1_xboole_0 = X1 ),
% 3.33/0.96      inference(unflattening,[status(thm)],[c_317]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_769,plain,
% 3.33/0.96      ( k1_relset_1(X0,X1,sK7) = X0
% 3.33/0.96      | k1_enumset1(sK5,sK5,sK5) != X0
% 3.33/0.96      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.33/0.96      | sK6 != X1
% 3.33/0.96      | sK7 != sK7
% 3.33/0.96      | k1_xboole_0 = X1 ),
% 3.33/0.96      inference(resolution_lifted,[status(thm)],[c_28,c_318]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_770,plain,
% 3.33/0.96      ( k1_relset_1(k1_enumset1(sK5,sK5,sK5),sK6,sK7) = k1_enumset1(sK5,sK5,sK5)
% 3.33/0.96      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6))
% 3.33/0.96      | k1_xboole_0 = sK6 ),
% 3.33/0.96      inference(unflattening,[status(thm)],[c_769]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_26,negated_conjecture,
% 3.33/0.96      ( k1_xboole_0 != sK6 ),
% 3.33/0.96      inference(cnf_transformation,[],[f72]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_771,plain,
% 3.33/0.96      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6))
% 3.33/0.96      | k1_relset_1(k1_enumset1(sK5,sK5,sK5),sK6,sK7) = k1_enumset1(sK5,sK5,sK5) ),
% 3.33/0.96      inference(global_propositional_subsumption,
% 3.33/0.96                [status(thm)],
% 3.33/0.96                [c_770,c_26]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_772,plain,
% 3.33/0.96      ( k1_relset_1(k1_enumset1(sK5,sK5,sK5),sK6,sK7) = k1_enumset1(sK5,sK5,sK5)
% 3.33/0.96      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) ),
% 3.33/0.96      inference(renaming,[status(thm)],[c_771]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_823,plain,
% 3.33/0.96      ( k1_relset_1(k1_enumset1(sK5,sK5,sK5),sK6,sK7) = k1_enumset1(sK5,sK5,sK5) ),
% 3.33/0.96      inference(equality_resolution_simp,[status(thm)],[c_772]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_17,plain,
% 3.33/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/0.96      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.33/0.96      inference(cnf_transformation,[],[f61]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_362,plain,
% 3.33/0.96      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.33/0.96      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.33/0.96      | sK7 != X2 ),
% 3.33/0.96      inference(resolution_lifted,[status(thm)],[c_17,c_27]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_363,plain,
% 3.33/0.96      ( k1_relset_1(X0,X1,sK7) = k1_relat_1(sK7)
% 3.33/0.96      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.33/0.96      inference(unflattening,[status(thm)],[c_362]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_1474,plain,
% 3.33/0.96      ( k1_relset_1(k1_enumset1(sK5,sK5,sK5),sK6,sK7) = k1_relat_1(sK7) ),
% 3.33/0.96      inference(equality_resolution,[status(thm)],[c_363]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_1721,plain,
% 3.33/0.96      ( k1_enumset1(sK5,sK5,sK5) = k1_relat_1(sK7) ),
% 3.33/0.96      inference(light_normalisation,[status(thm)],[c_823,c_1474]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_4,plain,
% 3.33/0.96      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1)) | X0 = X1 ),
% 3.33/0.96      inference(cnf_transformation,[],[f87]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_1313,plain,
% 3.33/0.96      ( X0 = X1 | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
% 3.33/0.96      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_1743,plain,
% 3.33/0.96      ( sK5 = X0 | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
% 3.33/0.96      inference(superposition,[status(thm)],[c_1721,c_1313]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_3222,plain,
% 3.33/0.96      ( sK4(sK7,X0) = sK5
% 3.33/0.96      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 3.33/0.96      inference(superposition,[status(thm)],[c_2081,c_1743]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_3347,plain,
% 3.33/0.96      ( k1_enumset1(X0,X0,X0) = k2_relat_1(sK7)
% 3.33/0.96      | sK4(sK7,sK1(k2_relat_1(sK7),X0)) = sK5
% 3.33/0.96      | k2_relat_1(sK7) = k1_xboole_0 ),
% 3.33/0.96      inference(superposition,[status(thm)],[c_1312,c_3222]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_8,plain,
% 3.33/0.96      ( ~ v1_relat_1(X0)
% 3.33/0.96      | k2_relat_1(X0) != k1_xboole_0
% 3.33/0.96      | k1_relat_1(X0) = k1_xboole_0 ),
% 3.33/0.96      inference(cnf_transformation,[],[f53]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_1544,plain,
% 3.33/0.96      ( ~ v1_relat_1(sK7)
% 3.33/0.96      | k2_relat_1(sK7) != k1_xboole_0
% 3.33/0.96      | k1_relat_1(sK7) = k1_xboole_0 ),
% 3.33/0.96      inference(instantiation,[status(thm)],[c_8]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_0,plain,
% 3.33/0.96      ( v1_xboole_0(k1_xboole_0) ),
% 3.33/0.96      inference(cnf_transformation,[],[f42]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_5,plain,
% 3.33/0.96      ( ~ v1_xboole_0(k1_enumset1(X0,X0,X0)) ),
% 3.33/0.96      inference(cnf_transformation,[],[f79]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_311,plain,
% 3.33/0.96      ( k1_enumset1(X0,X0,X0) != k1_xboole_0 ),
% 3.33/0.96      inference(resolution_lifted,[status(thm)],[c_0,c_5]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_1742,plain,
% 3.33/0.96      ( k1_relat_1(sK7) != k1_xboole_0 ),
% 3.33/0.96      inference(superposition,[status(thm)],[c_1721,c_311]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_7996,plain,
% 3.33/0.96      ( sK4(sK7,sK1(k2_relat_1(sK7),X0)) = sK5
% 3.33/0.96      | k1_enumset1(X0,X0,X0) = k2_relat_1(sK7) ),
% 3.33/0.96      inference(global_propositional_subsumption,
% 3.33/0.96                [status(thm)],
% 3.33/0.96                [c_3347,c_1463,c_1466,c_1544,c_1742]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_7997,plain,
% 3.33/0.96      ( k1_enumset1(X0,X0,X0) = k2_relat_1(sK7)
% 3.33/0.96      | sK4(sK7,sK1(k2_relat_1(sK7),X0)) = sK5 ),
% 3.33/0.96      inference(renaming,[status(thm)],[c_7996]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_18,plain,
% 3.33/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/0.96      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.33/0.96      inference(cnf_transformation,[],[f62]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_353,plain,
% 3.33/0.96      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.33/0.96      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.33/0.96      | sK7 != X2 ),
% 3.33/0.96      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_354,plain,
% 3.33/0.96      ( k2_relset_1(X0,X1,sK7) = k2_relat_1(sK7)
% 3.33/0.96      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.33/0.96      inference(unflattening,[status(thm)],[c_353]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_1471,plain,
% 3.33/0.96      ( k2_relset_1(k1_enumset1(sK5,sK5,sK5),sK6,sK7) = k2_relat_1(sK7) ),
% 3.33/0.96      inference(equality_resolution,[status(thm)],[c_354]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_25,negated_conjecture,
% 3.33/0.96      ( k1_enumset1(k1_funct_1(sK7,sK5),k1_funct_1(sK7,sK5),k1_funct_1(sK7,sK5)) != k2_relset_1(k1_enumset1(sK5,sK5,sK5),sK6,sK7) ),
% 3.33/0.96      inference(cnf_transformation,[],[f82]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_1520,plain,
% 3.33/0.96      ( k1_enumset1(k1_funct_1(sK7,sK5),k1_funct_1(sK7,sK5),k1_funct_1(sK7,sK5)) != k2_relat_1(sK7) ),
% 3.33/0.96      inference(demodulation,[status(thm)],[c_1471,c_25]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_8023,plain,
% 3.33/0.96      ( sK4(sK7,sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK5))) = sK5 ),
% 3.33/0.96      inference(superposition,[status(thm)],[c_7997,c_1520]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_14,plain,
% 3.33/0.96      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.33/0.96      | ~ v1_funct_1(X1)
% 3.33/0.96      | ~ v1_relat_1(X1)
% 3.33/0.96      | k1_funct_1(X1,sK4(X1,X0)) = X0 ),
% 3.33/0.96      inference(cnf_transformation,[],[f90]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_534,plain,
% 3.33/0.96      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.33/0.96      | ~ v1_relat_1(X1)
% 3.33/0.96      | k1_funct_1(X1,sK4(X1,X0)) = X0
% 3.33/0.96      | sK7 != X1 ),
% 3.33/0.96      inference(resolution_lifted,[status(thm)],[c_14,c_29]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_535,plain,
% 3.33/0.96      ( ~ r2_hidden(X0,k2_relat_1(sK7))
% 3.33/0.96      | ~ v1_relat_1(sK7)
% 3.33/0.96      | k1_funct_1(sK7,sK4(sK7,X0)) = X0 ),
% 3.33/0.96      inference(unflattening,[status(thm)],[c_534]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_1305,plain,
% 3.33/0.96      ( k1_funct_1(sK7,sK4(sK7,X0)) = X0
% 3.33/0.96      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 3.33/0.96      | v1_relat_1(sK7) != iProver_top ),
% 3.33/0.96      inference(predicate_to_equality,[status(thm)],[c_535]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_536,plain,
% 3.33/0.96      ( k1_funct_1(sK7,sK4(sK7,X0)) = X0
% 3.33/0.96      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 3.33/0.96      | v1_relat_1(sK7) != iProver_top ),
% 3.33/0.96      inference(predicate_to_equality,[status(thm)],[c_535]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_1966,plain,
% 3.33/0.96      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 3.33/0.96      | k1_funct_1(sK7,sK4(sK7,X0)) = X0 ),
% 3.33/0.96      inference(global_propositional_subsumption,
% 3.33/0.96                [status(thm)],
% 3.33/0.96                [c_1305,c_536,c_1463,c_1467]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_1967,plain,
% 3.33/0.96      ( k1_funct_1(sK7,sK4(sK7,X0)) = X0
% 3.33/0.96      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 3.33/0.96      inference(renaming,[status(thm)],[c_1966]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_2287,plain,
% 3.33/0.96      ( k1_enumset1(X0,X0,X0) = k2_relat_1(sK7)
% 3.33/0.96      | k1_funct_1(sK7,sK4(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0)
% 3.33/0.96      | k2_relat_1(sK7) = k1_xboole_0 ),
% 3.33/0.96      inference(superposition,[status(thm)],[c_1312,c_1967]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_7534,plain,
% 3.33/0.96      ( k1_funct_1(sK7,sK4(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0)
% 3.33/0.96      | k1_enumset1(X0,X0,X0) = k2_relat_1(sK7) ),
% 3.33/0.96      inference(global_propositional_subsumption,
% 3.33/0.96                [status(thm)],
% 3.33/0.96                [c_2287,c_1463,c_1466,c_1544,c_1742]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_7535,plain,
% 3.33/0.96      ( k1_enumset1(X0,X0,X0) = k2_relat_1(sK7)
% 3.33/0.96      | k1_funct_1(sK7,sK4(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0) ),
% 3.33/0.96      inference(renaming,[status(thm)],[c_7534]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_7560,plain,
% 3.33/0.96      ( k1_funct_1(sK7,sK4(sK7,sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK5)))) = sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK5)) ),
% 3.33/0.96      inference(superposition,[status(thm)],[c_7535,c_1520]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_8122,plain,
% 3.33/0.96      ( sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK5)) = k1_funct_1(sK7,sK5) ),
% 3.33/0.96      inference(demodulation,[status(thm)],[c_8023,c_7560]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_6,plain,
% 3.33/0.96      ( k1_enumset1(X0,X0,X0) = X1
% 3.33/0.96      | sK1(X1,X0) != X0
% 3.33/0.96      | k1_xboole_0 = X1 ),
% 3.33/0.96      inference(cnf_transformation,[],[f80]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(c_8273,plain,
% 3.33/0.96      ( k1_enumset1(k1_funct_1(sK7,sK5),k1_funct_1(sK7,sK5),k1_funct_1(sK7,sK5)) = k2_relat_1(sK7)
% 3.33/0.96      | k2_relat_1(sK7) = k1_xboole_0 ),
% 3.33/0.96      inference(superposition,[status(thm)],[c_8122,c_6]) ).
% 3.33/0.96  
% 3.33/0.96  cnf(contradiction,plain,
% 3.33/0.96      ( $false ),
% 3.33/0.96      inference(minisat,
% 3.33/0.96                [status(thm)],
% 3.33/0.96                [c_8273,c_1742,c_1544,c_1520,c_1466,c_1463]) ).
% 3.33/0.96  
% 3.33/0.96  
% 3.33/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 3.33/0.96  
% 3.33/0.96  ------                               Statistics
% 3.33/0.96  
% 3.33/0.96  ------ General
% 3.33/0.96  
% 3.33/0.96  abstr_ref_over_cycles:                  0
% 3.33/0.96  abstr_ref_under_cycles:                 0
% 3.33/0.96  gc_basic_clause_elim:                   0
% 3.33/0.96  forced_gc_time:                         0
% 3.33/0.96  parsing_time:                           0.008
% 3.33/0.96  unif_index_cands_time:                  0.
% 3.33/0.96  unif_index_add_time:                    0.
% 3.33/0.96  orderings_time:                         0.
% 3.33/0.96  out_proof_time:                         0.009
% 3.33/0.96  total_time:                             0.256
% 3.33/0.96  num_of_symbols:                         54
% 3.33/0.96  num_of_terms:                           6508
% 3.33/0.96  
% 3.33/0.96  ------ Preprocessing
% 3.33/0.96  
% 3.33/0.96  num_of_splits:                          0
% 3.33/0.96  num_of_split_atoms:                     0
% 3.33/0.96  num_of_reused_defs:                     0
% 3.33/0.96  num_eq_ax_congr_red:                    29
% 3.33/0.96  num_of_sem_filtered_clauses:            1
% 3.33/0.96  num_of_subtypes:                        0
% 3.33/0.96  monotx_restored_types:                  0
% 3.33/0.96  sat_num_of_epr_types:                   0
% 3.33/0.96  sat_num_of_non_cyclic_types:            0
% 3.33/0.96  sat_guarded_non_collapsed_types:        0
% 3.33/0.96  num_pure_diseq_elim:                    0
% 3.33/0.96  simp_replaced_by:                       0
% 3.33/0.96  res_preprocessed:                       127
% 3.33/0.96  prep_upred:                             0
% 3.33/0.96  prep_unflattend:                        35
% 3.33/0.96  smt_new_axioms:                         0
% 3.33/0.96  pred_elim_cands:                        2
% 3.33/0.96  pred_elim:                              4
% 3.33/0.96  pred_elim_cl:                           8
% 3.33/0.96  pred_elim_cycles:                       7
% 3.33/0.96  merged_defs:                            0
% 3.33/0.96  merged_defs_ncl:                        0
% 3.33/0.96  bin_hyper_res:                          0
% 3.33/0.96  prep_cycles:                            4
% 3.33/0.96  pred_elim_time:                         0.013
% 3.33/0.96  splitting_time:                         0.
% 3.33/0.96  sem_filter_time:                        0.
% 3.33/0.96  monotx_time:                            0.
% 3.33/0.96  subtype_inf_time:                       0.
% 3.33/0.96  
% 3.33/0.96  ------ Problem properties
% 3.33/0.96  
% 3.33/0.96  clauses:                                22
% 3.33/0.96  conjectures:                            2
% 3.33/0.96  epr:                                    1
% 3.33/0.96  horn:                                   16
% 3.33/0.96  ground:                                 4
% 3.33/0.96  unary:                                  5
% 3.33/0.96  binary:                                 4
% 3.33/0.96  lits:                                   57
% 3.33/0.96  lits_eq:                                33
% 3.33/0.96  fd_pure:                                0
% 3.33/0.96  fd_pseudo:                              0
% 3.33/0.96  fd_cond:                                3
% 3.33/0.96  fd_pseudo_cond:                         4
% 3.33/0.96  ac_symbols:                             0
% 3.33/0.96  
% 3.33/0.96  ------ Propositional Solver
% 3.33/0.96  
% 3.33/0.96  prop_solver_calls:                      28
% 3.33/0.96  prop_fast_solver_calls:                 994
% 3.33/0.96  smt_solver_calls:                       0
% 3.33/0.96  smt_fast_solver_calls:                  0
% 3.33/0.96  prop_num_of_clauses:                    2854
% 3.33/0.96  prop_preprocess_simplified:             7742
% 3.33/0.96  prop_fo_subsumed:                       16
% 3.33/0.96  prop_solver_time:                       0.
% 3.33/0.96  smt_solver_time:                        0.
% 3.33/0.96  smt_fast_solver_time:                   0.
% 3.33/0.96  prop_fast_solver_time:                  0.
% 3.33/0.96  prop_unsat_core_time:                   0.
% 3.33/0.96  
% 3.33/0.96  ------ QBF
% 3.33/0.96  
% 3.33/0.96  qbf_q_res:                              0
% 3.33/0.96  qbf_num_tautologies:                    0
% 3.33/0.96  qbf_prep_cycles:                        0
% 3.33/0.96  
% 3.33/0.96  ------ BMC1
% 3.33/0.96  
% 3.33/0.96  bmc1_current_bound:                     -1
% 3.33/0.96  bmc1_last_solved_bound:                 -1
% 3.33/0.96  bmc1_unsat_core_size:                   -1
% 3.33/0.96  bmc1_unsat_core_parents_size:           -1
% 3.33/0.96  bmc1_merge_next_fun:                    0
% 3.33/0.96  bmc1_unsat_core_clauses_time:           0.
% 3.33/0.96  
% 3.33/0.96  ------ Instantiation
% 3.33/0.96  
% 3.33/0.96  inst_num_of_clauses:                    837
% 3.33/0.96  inst_num_in_passive:                    341
% 3.33/0.96  inst_num_in_active:                     336
% 3.33/0.96  inst_num_in_unprocessed:                161
% 3.33/0.96  inst_num_of_loops:                      400
% 3.33/0.96  inst_num_of_learning_restarts:          0
% 3.33/0.96  inst_num_moves_active_passive:          62
% 3.33/0.96  inst_lit_activity:                      0
% 3.33/0.96  inst_lit_activity_moves:                0
% 3.33/0.96  inst_num_tautologies:                   0
% 3.33/0.96  inst_num_prop_implied:                  0
% 3.33/0.96  inst_num_existing_simplified:           0
% 3.33/0.96  inst_num_eq_res_simplified:             0
% 3.33/0.96  inst_num_child_elim:                    0
% 3.33/0.96  inst_num_of_dismatching_blockings:      426
% 3.33/0.96  inst_num_of_non_proper_insts:           848
% 3.33/0.96  inst_num_of_duplicates:                 0
% 3.33/0.96  inst_inst_num_from_inst_to_res:         0
% 3.33/0.96  inst_dismatching_checking_time:         0.
% 3.33/0.96  
% 3.33/0.96  ------ Resolution
% 3.33/0.96  
% 3.33/0.96  res_num_of_clauses:                     0
% 3.33/0.96  res_num_in_passive:                     0
% 3.33/0.96  res_num_in_active:                      0
% 3.33/0.96  res_num_of_loops:                       131
% 3.33/0.96  res_forward_subset_subsumed:            98
% 3.33/0.96  res_backward_subset_subsumed:           2
% 3.33/0.96  res_forward_subsumed:                   1
% 3.33/0.96  res_backward_subsumed:                  0
% 3.33/0.96  res_forward_subsumption_resolution:     0
% 3.33/0.96  res_backward_subsumption_resolution:    0
% 3.33/0.96  res_clause_to_clause_subsumption:       824
% 3.33/0.96  res_orphan_elimination:                 0
% 3.33/0.96  res_tautology_del:                      62
% 3.33/0.96  res_num_eq_res_simplified:              1
% 3.33/0.96  res_num_sel_changes:                    0
% 3.33/0.96  res_moves_from_active_to_pass:          0
% 3.33/0.96  
% 3.33/0.96  ------ Superposition
% 3.33/0.96  
% 3.33/0.96  sup_time_total:                         0.
% 3.33/0.96  sup_time_generating:                    0.
% 3.33/0.96  sup_time_sim_full:                      0.
% 3.33/0.96  sup_time_sim_immed:                     0.
% 3.33/0.96  
% 3.33/0.96  sup_num_of_clauses:                     296
% 3.33/0.96  sup_num_in_active:                      72
% 3.33/0.96  sup_num_in_passive:                     224
% 3.33/0.96  sup_num_of_loops:                       78
% 3.33/0.96  sup_fw_superposition:                   221
% 3.33/0.96  sup_bw_superposition:                   127
% 3.33/0.96  sup_immediate_simplified:               20
% 3.33/0.96  sup_given_eliminated:                   0
% 3.33/0.96  comparisons_done:                       0
% 3.33/0.96  comparisons_avoided:                    24
% 3.33/0.96  
% 3.33/0.96  ------ Simplifications
% 3.33/0.96  
% 3.33/0.96  
% 3.33/0.96  sim_fw_subset_subsumed:                 11
% 3.33/0.96  sim_bw_subset_subsumed:                 0
% 3.33/0.96  sim_fw_subsumed:                        3
% 3.33/0.96  sim_bw_subsumed:                        1
% 3.33/0.96  sim_fw_subsumption_res:                 1
% 3.33/0.96  sim_bw_subsumption_res:                 0
% 3.33/0.96  sim_tautology_del:                      1
% 3.33/0.96  sim_eq_tautology_del:                   30
% 3.33/0.96  sim_eq_res_simp:                        0
% 3.33/0.96  sim_fw_demodulated:                     0
% 3.33/0.96  sim_bw_demodulated:                     7
% 3.33/0.96  sim_light_normalised:                   9
% 3.33/0.96  sim_joinable_taut:                      0
% 3.33/0.96  sim_joinable_simp:                      0
% 3.33/0.96  sim_ac_normalised:                      0
% 3.33/0.96  sim_smt_subsumption:                    0
% 3.33/0.96  
%------------------------------------------------------------------------------
