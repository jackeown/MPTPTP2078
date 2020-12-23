%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:01 EST 2020

% Result     : Theorem 7.73s
% Output     : CNFRefutation 7.73s
% Verified   : 
% Statistics : Number of formulae       :  181 (1175 expanded)
%              Number of clauses        :  105 ( 397 expanded)
%              Number of leaves         :   24 ( 259 expanded)
%              Depth                    :   31
%              Number of atoms          :  640 (5066 expanded)
%              Number of equality atoms :  249 (1097 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f38,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f38])).

fof(f41,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f39])).

fof(f79,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f80,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f79])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK10
            | ~ r2_hidden(X5,X2)
            | ~ m1_subset_1(X5,X0) )
        & r2_hidden(sK10,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f107,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK9,X5) != X4
              | ~ r2_hidden(X5,sK8)
              | ~ m1_subset_1(X5,sK6) )
          & r2_hidden(X4,k7_relset_1(sK6,sK7,sK9,sK8)) )
      & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
      & v1_funct_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f109,plain,
    ( ! [X5] :
        ( k1_funct_1(sK9,X5) != sK10
        | ~ r2_hidden(X5,sK8)
        | ~ m1_subset_1(X5,sK6) )
    & r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8))
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    & v1_funct_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10])],[f80,f108,f107])).

fof(f173,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f109])).

fof(f30,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f154,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f33,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f99,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                          | ! [X5] :
                              ( ~ r2_hidden(X5,X1)
                              | ~ r2_hidden(k4_tarski(X5,X4),X3)
                              | ~ m1_subset_1(X5,X2) ) )
                        & ( ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X5,X4),X3)
                              & m1_subset_1(X5,X2) )
                          | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f75])).

fof(f100,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                          | ! [X5] :
                              ( ~ r2_hidden(X5,X1)
                              | ~ r2_hidden(k4_tarski(X5,X4),X3)
                              | ~ m1_subset_1(X5,X2) ) )
                        & ( ? [X6] :
                              ( r2_hidden(X6,X1)
                              & r2_hidden(k4_tarski(X6,X4),X3)
                              & m1_subset_1(X6,X2) )
                          | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f99])).

fof(f101,plain,(
    ! [X4,X3,X2,X1] :
      ( ? [X6] :
          ( r2_hidden(X6,X1)
          & r2_hidden(k4_tarski(X6,X4),X3)
          & m1_subset_1(X6,X2) )
     => ( r2_hidden(sK3(X1,X2,X3,X4),X1)
        & r2_hidden(k4_tarski(sK3(X1,X2,X3,X4),X4),X3)
        & m1_subset_1(sK3(X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f102,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                          | ! [X5] :
                              ( ~ r2_hidden(X5,X1)
                              | ~ r2_hidden(k4_tarski(X5,X4),X3)
                              | ~ m1_subset_1(X5,X2) ) )
                        & ( ( r2_hidden(sK3(X1,X2,X3,X4),X1)
                            & r2_hidden(k4_tarski(sK3(X1,X2,X3,X4),X4),X3)
                            & m1_subset_1(sK3(X1,X2,X3,X4),X2) )
                          | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f100,f101])).

fof(f160,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK3(X1,X2,X3,X4),X1)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f174,plain,(
    r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8)) ),
    inference(cnf_transformation,[],[f109])).

fof(f159,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK3(X1,X2,X3,X4),X4),X3)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f66])).

fof(f96,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f67])).

fof(f97,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f96])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f172,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f109])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f92,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f93,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f92])).

fof(f94,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f95,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
            & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f93,f94])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f88,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f87])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f82,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f81])).

fof(f83,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f82,f83])).

fof(f111,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f131,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f112,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f175,plain,(
    ! [X5] :
      ( k1_funct_1(sK9,X5) != sK10
      | ~ r2_hidden(X5,sK8)
      | ~ m1_subset_1(X5,sK6) ) ),
    inference(cnf_transformation,[],[f109])).

fof(f158,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK3(X1,X2,X3,X4),X2)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f35,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & v1_xboole_0(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & v1_xboole_0(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f35])).

fof(f105,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & v1_xboole_0(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v4_relat_1(sK5(X0,X1),X0)
        & v1_relat_1(sK5(X0,X1))
        & v1_xboole_0(sK5(X0,X1))
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v4_relat_1(sK5(X0,X1),X0)
      & v1_relat_1(sK5(X0,X1))
      & v1_xboole_0(sK5(X0,X1))
      & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f105])).

fof(f166,plain,(
    ! [X0,X1] : v1_xboole_0(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f106])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f89])).

fof(f121,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f90])).

fof(f185,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f121])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_61,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f173])).

cnf(c_2009,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61])).

cnf(c_42,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f154])).

cnf(c_2027,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_5967,plain,
    ( k7_relset_1(sK6,sK7,sK9,X0) = k9_relat_1(sK9,X0) ),
    inference(superposition,[status(thm)],[c_2009,c_2027])).

cnf(c_47,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | r2_hidden(sK3(X4,X3,X2,X0),X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f160])).

cnf(c_2022,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | r2_hidden(sK3(X4,X3,X2,X0),X4) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_6993,plain,
    ( m1_subset_1(X0,sK7) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
    | r2_hidden(sK3(X1,sK6,sK9,X0),X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK7) = iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_5967,c_2022])).

cnf(c_64,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61])).

cnf(c_8474,plain,
    ( m1_subset_1(X0,sK7) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
    | r2_hidden(sK3(X1,sK6,sK9,X0),X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK7) = iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6993,c_64])).

cnf(c_60,negated_conjecture,
    ( r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8)) ),
    inference(cnf_transformation,[],[f174])).

cnf(c_2010,plain,
    ( r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_5984,plain,
    ( r2_hidden(sK10,k9_relat_1(sK9,sK8)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5967,c_2010])).

cnf(c_48,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | r2_hidden(k4_tarski(sK3(X4,X3,X2,X0),X0),X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f159])).

cnf(c_2021,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | r2_hidden(k4_tarski(sK3(X4,X3,X2,X0),X0),X2) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_6279,plain,
    ( m1_subset_1(X0,sK7) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK3(X1,sK6,sK9,X0),X0),sK9) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK7) = iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_5967,c_2021])).

cnf(c_6550,plain,
    ( m1_subset_1(X0,sK7) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK3(X1,sK6,sK9,X0),X0),sK9) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK7) = iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6279,c_64])).

cnf(c_34,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f146])).

cnf(c_2035,plain,
    ( k1_funct_1(X0,X1) = X2
    | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_10777,plain,
    ( k1_funct_1(sK9,sK3(X0,sK6,sK9,X1)) = X1
    | m1_subset_1(X1,sK7) != iProver_top
    | r2_hidden(X1,k9_relat_1(sK9,X0)) != iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_relat_1(sK9) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK7) = iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_6550,c_2035])).

cnf(c_62,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f172])).

cnf(c_63,plain,
    ( v1_funct_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62])).

cnf(c_38,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f150])).

cnf(c_2031,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_4587,plain,
    ( v1_relat_1(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_2009,c_2031])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK2(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_2043,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_2051,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7148,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK6,sK7)) = iProver_top
    | r2_hidden(X0,sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_2009,c_2051])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_2054,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7769,plain,
    ( r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_7148,c_2054])).

cnf(c_10574,plain,
    ( r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_2043,c_7769])).

cnf(c_11194,plain,
    ( r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10574,c_4587])).

cnf(c_11195,plain,
    ( r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_11194])).

cnf(c_11206,plain,
    ( r2_hidden(sK10,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_5984,c_11195])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_2060,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_11237,plain,
    ( v1_xboole_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_11206,c_2060])).

cnf(c_19910,plain,
    ( v1_xboole_0(X0) = iProver_top
    | r2_hidden(X1,k9_relat_1(sK9,X0)) != iProver_top
    | m1_subset_1(X1,sK7) != iProver_top
    | k1_funct_1(sK9,sK3(X0,sK6,sK9,X1)) = X1
    | v1_xboole_0(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10777,c_63,c_4587,c_11237])).

cnf(c_19911,plain,
    ( k1_funct_1(sK9,sK3(X0,sK6,sK9,X1)) = X1
    | m1_subset_1(X1,sK7) != iProver_top
    | r2_hidden(X1,k9_relat_1(sK9,X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_19910])).

cnf(c_19921,plain,
    ( k1_funct_1(sK9,sK3(sK8,sK6,sK9,sK10)) = sK10
    | m1_subset_1(sK10,sK7) != iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_5984,c_19911])).

cnf(c_65,plain,
    ( r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_2124,plain,
    ( ~ r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8))
    | ~ v1_xboole_0(k7_relset_1(sK6,sK7,sK9,sK8)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2125,plain,
    ( r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8)) != iProver_top
    | v1_xboole_0(k7_relset_1(sK6,sK7,sK9,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2124])).

cnf(c_1136,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2169,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k7_relset_1(sK6,sK7,sK9,sK8))
    | k7_relset_1(sK6,sK7,sK9,sK8) != X0 ),
    inference(instantiation,[status(thm)],[c_1136])).

cnf(c_2338,plain,
    ( v1_xboole_0(k7_relset_1(sK6,sK7,sK9,sK8))
    | ~ v1_xboole_0(k9_relat_1(sK9,sK8))
    | k7_relset_1(sK6,sK7,sK9,sK8) != k9_relat_1(sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_2169])).

cnf(c_2339,plain,
    ( k7_relset_1(sK6,sK7,sK9,sK8) != k9_relat_1(sK9,sK8)
    | v1_xboole_0(k7_relset_1(sK6,sK7,sK9,sK8)) = iProver_top
    | v1_xboole_0(k9_relat_1(sK9,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2338])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_2844,plain,
    ( r2_hidden(sK0(k9_relat_1(sK9,sK8)),k9_relat_1(sK9,sK8))
    | v1_xboole_0(k9_relat_1(sK9,sK8)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2845,plain,
    ( r2_hidden(sK0(k9_relat_1(sK9,sK8)),k9_relat_1(sK9,sK8)) = iProver_top
    | v1_xboole_0(k9_relat_1(sK9,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2844])).

cnf(c_3630,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | k7_relset_1(sK6,sK7,sK9,sK8) = k9_relat_1(sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_5568,plain,
    ( r2_hidden(sK2(sK0(k9_relat_1(sK9,sK8)),sK8,sK9),sK8)
    | ~ r2_hidden(sK0(k9_relat_1(sK9,sK8)),k9_relat_1(sK9,sK8))
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_5569,plain,
    ( r2_hidden(sK2(sK0(k9_relat_1(sK9,sK8)),sK8,sK9),sK8) = iProver_top
    | r2_hidden(sK0(k9_relat_1(sK9,sK8)),k9_relat_1(sK9,sK8)) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5568])).

cnf(c_19,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_2048,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11238,plain,
    ( m1_subset_1(sK10,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_11206,c_2048])).

cnf(c_12606,plain,
    ( ~ r2_hidden(sK2(sK0(k9_relat_1(sK9,sK8)),sK8,sK9),sK8)
    | ~ v1_xboole_0(sK8) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_12607,plain,
    ( r2_hidden(sK2(sK0(k9_relat_1(sK9,sK8)),sK8,sK9),sK8) != iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12606])).

cnf(c_20111,plain,
    ( v1_xboole_0(sK6) = iProver_top
    | k1_funct_1(sK9,sK3(sK8,sK6,sK9,sK10)) = sK10 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19921,c_61,c_65,c_2125,c_2339,c_2845,c_3630,c_4587,c_5569,c_11238,c_12607])).

cnf(c_20112,plain,
    ( k1_funct_1(sK9,sK3(sK8,sK6,sK9,sK10)) = sK10
    | v1_xboole_0(sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_20111])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_2059,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_20115,plain,
    ( k1_funct_1(sK9,sK3(sK8,sK6,sK9,sK10)) = sK10
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_20112,c_2059])).

cnf(c_59,negated_conjecture,
    ( ~ m1_subset_1(X0,sK6)
    | ~ r2_hidden(X0,sK8)
    | k1_funct_1(sK9,X0) != sK10 ),
    inference(cnf_transformation,[],[f175])).

cnf(c_2011,plain,
    ( k1_funct_1(sK9,X0) != sK10
    | m1_subset_1(X0,sK6) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_20397,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(sK3(sK8,sK6,sK9,sK10),sK6) != iProver_top
    | r2_hidden(sK3(sK8,sK6,sK9,sK10),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_20115,c_2011])).

cnf(c_1134,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2687,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1134])).

cnf(c_1135,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2324,plain,
    ( X0 != X1
    | sK6 != X1
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_1135])).

cnf(c_2689,plain,
    ( X0 != sK6
    | sK6 = X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2324])).

cnf(c_2690,plain,
    ( sK6 != sK6
    | sK6 = k1_xboole_0
    | k1_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_2689])).

cnf(c_4294,plain,
    ( ~ v1_xboole_0(sK6)
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4295,plain,
    ( k1_xboole_0 = sK6
    | v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4294])).

cnf(c_49,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | m1_subset_1(sK3(X4,X3,X2,X0),X3)
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f158])).

cnf(c_2020,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(sK3(X4,X3,X2,X0),X3) = iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_5872,plain,
    ( m1_subset_1(sK3(sK8,sK6,sK9,sK10),sK6) = iProver_top
    | m1_subset_1(sK10,sK7) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | v1_xboole_0(sK7) = iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2010,c_2020])).

cnf(c_20939,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK3(sK8,sK6,sK9,sK10),sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20397,c_61,c_64,c_65,c_2125,c_2339,c_2687,c_2690,c_2845,c_3630,c_4295,c_4587,c_5569,c_5872,c_11237,c_11238,c_12607])).

cnf(c_20943,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(sK10,sK7) != iProver_top
    | r2_hidden(sK10,k9_relat_1(sK9,sK8)) != iProver_top
    | v1_xboole_0(sK7) = iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_8474,c_20939])).

cnf(c_55,plain,
    ( v1_xboole_0(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

cnf(c_2014,plain,
    ( v1_xboole_0(sK5(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_3885,plain,
    ( sK5(X0,X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2014,c_2059])).

cnf(c_3951,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3885,c_2014])).

cnf(c_9318,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK6)
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_1136])).

cnf(c_9319,plain,
    ( sK6 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9318])).

cnf(c_9321,plain,
    ( sK6 != k1_xboole_0
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9319])).

cnf(c_20946,plain,
    ( v1_xboole_0(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20943,c_61,c_65,c_2125,c_2339,c_2845,c_3630,c_3951,c_4587,c_5569,c_5984,c_9321,c_11237,c_11238,c_12607])).

cnf(c_20951,plain,
    ( sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_20946,c_2059])).

cnf(c_21099,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK7))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_20951,c_2009])).

cnf(c_11,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f185])).

cnf(c_21100,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_21099,c_11])).

cnf(c_40,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f152])).

cnf(c_2029,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_6402,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_2029])).

cnf(c_21221,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_21100,c_6402])).

cnf(c_21229,plain,
    ( v1_xboole_0(sK9) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_21221])).

cnf(c_12460,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK0(k9_relat_1(sK9,sK8)),sK8,sK9),sK0(k9_relat_1(sK9,sK8))),sK9)
    | ~ v1_xboole_0(sK9) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_12461,plain,
    ( r2_hidden(k4_tarski(sK2(sK0(k9_relat_1(sK9,sK8)),sK8,sK9),sK0(k9_relat_1(sK9,sK8))),sK9) != iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12460])).

cnf(c_5567,plain,
    ( r2_hidden(k4_tarski(sK2(sK0(k9_relat_1(sK9,sK8)),sK8,sK9),sK0(k9_relat_1(sK9,sK8))),sK9)
    | ~ r2_hidden(sK0(k9_relat_1(sK9,sK8)),k9_relat_1(sK9,sK8))
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_5571,plain,
    ( r2_hidden(k4_tarski(sK2(sK0(k9_relat_1(sK9,sK8)),sK8,sK9),sK0(k9_relat_1(sK9,sK8))),sK9) = iProver_top
    | r2_hidden(sK0(k9_relat_1(sK9,sK8)),k9_relat_1(sK9,sK8)) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5567])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21229,c_12461,c_5571,c_4587,c_3951,c_3630,c_2845,c_2339,c_2125,c_65,c_61])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:21:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.73/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.73/1.49  
% 7.73/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.73/1.49  
% 7.73/1.49  ------  iProver source info
% 7.73/1.49  
% 7.73/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.73/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.73/1.49  git: non_committed_changes: false
% 7.73/1.49  git: last_make_outside_of_git: false
% 7.73/1.49  
% 7.73/1.49  ------ 
% 7.73/1.49  
% 7.73/1.49  ------ Input Options
% 7.73/1.49  
% 7.73/1.49  --out_options                           all
% 7.73/1.49  --tptp_safe_out                         true
% 7.73/1.49  --problem_path                          ""
% 7.73/1.49  --include_path                          ""
% 7.73/1.49  --clausifier                            res/vclausify_rel
% 7.73/1.49  --clausifier_options                    ""
% 7.73/1.49  --stdin                                 false
% 7.73/1.49  --stats_out                             all
% 7.73/1.49  
% 7.73/1.49  ------ General Options
% 7.73/1.49  
% 7.73/1.49  --fof                                   false
% 7.73/1.49  --time_out_real                         305.
% 7.73/1.49  --time_out_virtual                      -1.
% 7.73/1.49  --symbol_type_check                     false
% 7.73/1.49  --clausify_out                          false
% 7.73/1.49  --sig_cnt_out                           false
% 7.73/1.49  --trig_cnt_out                          false
% 7.73/1.49  --trig_cnt_out_tolerance                1.
% 7.73/1.49  --trig_cnt_out_sk_spl                   false
% 7.73/1.49  --abstr_cl_out                          false
% 7.73/1.49  
% 7.73/1.49  ------ Global Options
% 7.73/1.49  
% 7.73/1.49  --schedule                              default
% 7.73/1.49  --add_important_lit                     false
% 7.73/1.49  --prop_solver_per_cl                    1000
% 7.73/1.49  --min_unsat_core                        false
% 7.73/1.49  --soft_assumptions                      false
% 7.73/1.49  --soft_lemma_size                       3
% 7.73/1.49  --prop_impl_unit_size                   0
% 7.73/1.49  --prop_impl_unit                        []
% 7.73/1.49  --share_sel_clauses                     true
% 7.73/1.49  --reset_solvers                         false
% 7.73/1.49  --bc_imp_inh                            [conj_cone]
% 7.73/1.49  --conj_cone_tolerance                   3.
% 7.73/1.49  --extra_neg_conj                        none
% 7.73/1.49  --large_theory_mode                     true
% 7.73/1.49  --prolific_symb_bound                   200
% 7.73/1.49  --lt_threshold                          2000
% 7.73/1.49  --clause_weak_htbl                      true
% 7.73/1.49  --gc_record_bc_elim                     false
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing Options
% 7.73/1.49  
% 7.73/1.49  --preprocessing_flag                    true
% 7.73/1.49  --time_out_prep_mult                    0.1
% 7.73/1.49  --splitting_mode                        input
% 7.73/1.49  --splitting_grd                         true
% 7.73/1.49  --splitting_cvd                         false
% 7.73/1.49  --splitting_cvd_svl                     false
% 7.73/1.49  --splitting_nvd                         32
% 7.73/1.49  --sub_typing                            true
% 7.73/1.49  --prep_gs_sim                           true
% 7.73/1.49  --prep_unflatten                        true
% 7.73/1.49  --prep_res_sim                          true
% 7.73/1.49  --prep_upred                            true
% 7.73/1.49  --prep_sem_filter                       exhaustive
% 7.73/1.49  --prep_sem_filter_out                   false
% 7.73/1.49  --pred_elim                             true
% 7.73/1.49  --res_sim_input                         true
% 7.73/1.49  --eq_ax_congr_red                       true
% 7.73/1.49  --pure_diseq_elim                       true
% 7.73/1.49  --brand_transform                       false
% 7.73/1.49  --non_eq_to_eq                          false
% 7.73/1.49  --prep_def_merge                        true
% 7.73/1.49  --prep_def_merge_prop_impl              false
% 7.73/1.49  --prep_def_merge_mbd                    true
% 7.73/1.49  --prep_def_merge_tr_red                 false
% 7.73/1.49  --prep_def_merge_tr_cl                  false
% 7.73/1.49  --smt_preprocessing                     true
% 7.73/1.49  --smt_ac_axioms                         fast
% 7.73/1.49  --preprocessed_out                      false
% 7.73/1.49  --preprocessed_stats                    false
% 7.73/1.49  
% 7.73/1.49  ------ Abstraction refinement Options
% 7.73/1.49  
% 7.73/1.49  --abstr_ref                             []
% 7.73/1.49  --abstr_ref_prep                        false
% 7.73/1.49  --abstr_ref_until_sat                   false
% 7.73/1.49  --abstr_ref_sig_restrict                funpre
% 7.73/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.73/1.49  --abstr_ref_under                       []
% 7.73/1.49  
% 7.73/1.49  ------ SAT Options
% 7.73/1.49  
% 7.73/1.49  --sat_mode                              false
% 7.73/1.49  --sat_fm_restart_options                ""
% 7.73/1.49  --sat_gr_def                            false
% 7.73/1.49  --sat_epr_types                         true
% 7.73/1.49  --sat_non_cyclic_types                  false
% 7.73/1.49  --sat_finite_models                     false
% 7.73/1.49  --sat_fm_lemmas                         false
% 7.73/1.49  --sat_fm_prep                           false
% 7.73/1.49  --sat_fm_uc_incr                        true
% 7.73/1.49  --sat_out_model                         small
% 7.73/1.49  --sat_out_clauses                       false
% 7.73/1.49  
% 7.73/1.49  ------ QBF Options
% 7.73/1.49  
% 7.73/1.49  --qbf_mode                              false
% 7.73/1.49  --qbf_elim_univ                         false
% 7.73/1.49  --qbf_dom_inst                          none
% 7.73/1.49  --qbf_dom_pre_inst                      false
% 7.73/1.49  --qbf_sk_in                             false
% 7.73/1.49  --qbf_pred_elim                         true
% 7.73/1.49  --qbf_split                             512
% 7.73/1.49  
% 7.73/1.49  ------ BMC1 Options
% 7.73/1.49  
% 7.73/1.49  --bmc1_incremental                      false
% 7.73/1.49  --bmc1_axioms                           reachable_all
% 7.73/1.49  --bmc1_min_bound                        0
% 7.73/1.49  --bmc1_max_bound                        -1
% 7.73/1.49  --bmc1_max_bound_default                -1
% 7.73/1.49  --bmc1_symbol_reachability              true
% 7.73/1.49  --bmc1_property_lemmas                  false
% 7.73/1.49  --bmc1_k_induction                      false
% 7.73/1.49  --bmc1_non_equiv_states                 false
% 7.73/1.49  --bmc1_deadlock                         false
% 7.73/1.49  --bmc1_ucm                              false
% 7.73/1.49  --bmc1_add_unsat_core                   none
% 7.73/1.49  --bmc1_unsat_core_children              false
% 7.73/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.73/1.49  --bmc1_out_stat                         full
% 7.73/1.49  --bmc1_ground_init                      false
% 7.73/1.49  --bmc1_pre_inst_next_state              false
% 7.73/1.49  --bmc1_pre_inst_state                   false
% 7.73/1.49  --bmc1_pre_inst_reach_state             false
% 7.73/1.49  --bmc1_out_unsat_core                   false
% 7.73/1.49  --bmc1_aig_witness_out                  false
% 7.73/1.49  --bmc1_verbose                          false
% 7.73/1.49  --bmc1_dump_clauses_tptp                false
% 7.73/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.73/1.49  --bmc1_dump_file                        -
% 7.73/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.73/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.73/1.49  --bmc1_ucm_extend_mode                  1
% 7.73/1.49  --bmc1_ucm_init_mode                    2
% 7.73/1.49  --bmc1_ucm_cone_mode                    none
% 7.73/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.73/1.49  --bmc1_ucm_relax_model                  4
% 7.73/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.73/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.73/1.49  --bmc1_ucm_layered_model                none
% 7.73/1.49  --bmc1_ucm_max_lemma_size               10
% 7.73/1.49  
% 7.73/1.49  ------ AIG Options
% 7.73/1.49  
% 7.73/1.49  --aig_mode                              false
% 7.73/1.49  
% 7.73/1.49  ------ Instantiation Options
% 7.73/1.49  
% 7.73/1.49  --instantiation_flag                    true
% 7.73/1.49  --inst_sos_flag                         true
% 7.73/1.49  --inst_sos_phase                        true
% 7.73/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.73/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.73/1.49  --inst_lit_sel_side                     num_symb
% 7.73/1.49  --inst_solver_per_active                1400
% 7.73/1.49  --inst_solver_calls_frac                1.
% 7.73/1.49  --inst_passive_queue_type               priority_queues
% 7.73/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.73/1.49  --inst_passive_queues_freq              [25;2]
% 7.73/1.49  --inst_dismatching                      true
% 7.73/1.49  --inst_eager_unprocessed_to_passive     true
% 7.73/1.49  --inst_prop_sim_given                   true
% 7.73/1.49  --inst_prop_sim_new                     false
% 7.73/1.49  --inst_subs_new                         false
% 7.73/1.49  --inst_eq_res_simp                      false
% 7.73/1.49  --inst_subs_given                       false
% 7.73/1.49  --inst_orphan_elimination               true
% 7.73/1.49  --inst_learning_loop_flag               true
% 7.73/1.49  --inst_learning_start                   3000
% 7.73/1.49  --inst_learning_factor                  2
% 7.73/1.49  --inst_start_prop_sim_after_learn       3
% 7.73/1.49  --inst_sel_renew                        solver
% 7.73/1.49  --inst_lit_activity_flag                true
% 7.73/1.49  --inst_restr_to_given                   false
% 7.73/1.49  --inst_activity_threshold               500
% 7.73/1.49  --inst_out_proof                        true
% 7.73/1.49  
% 7.73/1.49  ------ Resolution Options
% 7.73/1.49  
% 7.73/1.49  --resolution_flag                       true
% 7.73/1.49  --res_lit_sel                           adaptive
% 7.73/1.49  --res_lit_sel_side                      none
% 7.73/1.49  --res_ordering                          kbo
% 7.73/1.49  --res_to_prop_solver                    active
% 7.73/1.49  --res_prop_simpl_new                    false
% 7.73/1.49  --res_prop_simpl_given                  true
% 7.73/1.49  --res_passive_queue_type                priority_queues
% 7.73/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.73/1.49  --res_passive_queues_freq               [15;5]
% 7.73/1.49  --res_forward_subs                      full
% 7.73/1.49  --res_backward_subs                     full
% 7.73/1.49  --res_forward_subs_resolution           true
% 7.73/1.49  --res_backward_subs_resolution          true
% 7.73/1.49  --res_orphan_elimination                true
% 7.73/1.49  --res_time_limit                        2.
% 7.73/1.49  --res_out_proof                         true
% 7.73/1.49  
% 7.73/1.49  ------ Superposition Options
% 7.73/1.49  
% 7.73/1.49  --superposition_flag                    true
% 7.73/1.49  --sup_passive_queue_type                priority_queues
% 7.73/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.73/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.73/1.49  --demod_completeness_check              fast
% 7.73/1.49  --demod_use_ground                      true
% 7.73/1.49  --sup_to_prop_solver                    passive
% 7.73/1.49  --sup_prop_simpl_new                    true
% 7.73/1.49  --sup_prop_simpl_given                  true
% 7.73/1.49  --sup_fun_splitting                     true
% 7.73/1.49  --sup_smt_interval                      50000
% 7.73/1.49  
% 7.73/1.49  ------ Superposition Simplification Setup
% 7.73/1.49  
% 7.73/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.73/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.73/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.73/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.73/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.73/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.73/1.49  --sup_immed_triv                        [TrivRules]
% 7.73/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.49  --sup_immed_bw_main                     []
% 7.73/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.73/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.73/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.49  --sup_input_bw                          []
% 7.73/1.49  
% 7.73/1.49  ------ Combination Options
% 7.73/1.49  
% 7.73/1.49  --comb_res_mult                         3
% 7.73/1.49  --comb_sup_mult                         2
% 7.73/1.49  --comb_inst_mult                        10
% 7.73/1.49  
% 7.73/1.49  ------ Debug Options
% 7.73/1.49  
% 7.73/1.49  --dbg_backtrace                         false
% 7.73/1.49  --dbg_dump_prop_clauses                 false
% 7.73/1.49  --dbg_dump_prop_clauses_file            -
% 7.73/1.49  --dbg_out_stat                          false
% 7.73/1.49  ------ Parsing...
% 7.73/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  ------ Proving...
% 7.73/1.49  ------ Problem Properties 
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  clauses                                 61
% 7.73/1.49  conjectures                             4
% 7.73/1.49  EPR                                     7
% 7.73/1.49  Horn                                    52
% 7.73/1.49  unary                                   18
% 7.73/1.49  binary                                  15
% 7.73/1.49  lits                                    159
% 7.73/1.49  lits eq                                 24
% 7.73/1.49  fd_pure                                 0
% 7.73/1.49  fd_pseudo                               0
% 7.73/1.49  fd_cond                                 6
% 7.73/1.49  fd_pseudo_cond                          1
% 7.73/1.49  AC symbols                              0
% 7.73/1.49  
% 7.73/1.49  ------ Schedule dynamic 5 is on 
% 7.73/1.49  
% 7.73/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ 
% 7.73/1.49  Current options:
% 7.73/1.49  ------ 
% 7.73/1.49  
% 7.73/1.49  ------ Input Options
% 7.73/1.49  
% 7.73/1.49  --out_options                           all
% 7.73/1.49  --tptp_safe_out                         true
% 7.73/1.49  --problem_path                          ""
% 7.73/1.49  --include_path                          ""
% 7.73/1.49  --clausifier                            res/vclausify_rel
% 7.73/1.49  --clausifier_options                    ""
% 7.73/1.49  --stdin                                 false
% 7.73/1.49  --stats_out                             all
% 7.73/1.49  
% 7.73/1.49  ------ General Options
% 7.73/1.49  
% 7.73/1.49  --fof                                   false
% 7.73/1.49  --time_out_real                         305.
% 7.73/1.49  --time_out_virtual                      -1.
% 7.73/1.49  --symbol_type_check                     false
% 7.73/1.49  --clausify_out                          false
% 7.73/1.49  --sig_cnt_out                           false
% 7.73/1.49  --trig_cnt_out                          false
% 7.73/1.49  --trig_cnt_out_tolerance                1.
% 7.73/1.49  --trig_cnt_out_sk_spl                   false
% 7.73/1.49  --abstr_cl_out                          false
% 7.73/1.49  
% 7.73/1.49  ------ Global Options
% 7.73/1.49  
% 7.73/1.49  --schedule                              default
% 7.73/1.49  --add_important_lit                     false
% 7.73/1.49  --prop_solver_per_cl                    1000
% 7.73/1.49  --min_unsat_core                        false
% 7.73/1.49  --soft_assumptions                      false
% 7.73/1.49  --soft_lemma_size                       3
% 7.73/1.49  --prop_impl_unit_size                   0
% 7.73/1.49  --prop_impl_unit                        []
% 7.73/1.49  --share_sel_clauses                     true
% 7.73/1.49  --reset_solvers                         false
% 7.73/1.49  --bc_imp_inh                            [conj_cone]
% 7.73/1.49  --conj_cone_tolerance                   3.
% 7.73/1.49  --extra_neg_conj                        none
% 7.73/1.49  --large_theory_mode                     true
% 7.73/1.49  --prolific_symb_bound                   200
% 7.73/1.49  --lt_threshold                          2000
% 7.73/1.49  --clause_weak_htbl                      true
% 7.73/1.49  --gc_record_bc_elim                     false
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing Options
% 7.73/1.49  
% 7.73/1.49  --preprocessing_flag                    true
% 7.73/1.49  --time_out_prep_mult                    0.1
% 7.73/1.49  --splitting_mode                        input
% 7.73/1.49  --splitting_grd                         true
% 7.73/1.49  --splitting_cvd                         false
% 7.73/1.49  --splitting_cvd_svl                     false
% 7.73/1.49  --splitting_nvd                         32
% 7.73/1.49  --sub_typing                            true
% 7.73/1.49  --prep_gs_sim                           true
% 7.73/1.49  --prep_unflatten                        true
% 7.73/1.49  --prep_res_sim                          true
% 7.73/1.49  --prep_upred                            true
% 7.73/1.49  --prep_sem_filter                       exhaustive
% 7.73/1.49  --prep_sem_filter_out                   false
% 7.73/1.49  --pred_elim                             true
% 7.73/1.49  --res_sim_input                         true
% 7.73/1.49  --eq_ax_congr_red                       true
% 7.73/1.49  --pure_diseq_elim                       true
% 7.73/1.49  --brand_transform                       false
% 7.73/1.49  --non_eq_to_eq                          false
% 7.73/1.49  --prep_def_merge                        true
% 7.73/1.49  --prep_def_merge_prop_impl              false
% 7.73/1.49  --prep_def_merge_mbd                    true
% 7.73/1.49  --prep_def_merge_tr_red                 false
% 7.73/1.49  --prep_def_merge_tr_cl                  false
% 7.73/1.49  --smt_preprocessing                     true
% 7.73/1.49  --smt_ac_axioms                         fast
% 7.73/1.49  --preprocessed_out                      false
% 7.73/1.49  --preprocessed_stats                    false
% 7.73/1.49  
% 7.73/1.49  ------ Abstraction refinement Options
% 7.73/1.49  
% 7.73/1.49  --abstr_ref                             []
% 7.73/1.49  --abstr_ref_prep                        false
% 7.73/1.49  --abstr_ref_until_sat                   false
% 7.73/1.49  --abstr_ref_sig_restrict                funpre
% 7.73/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.73/1.49  --abstr_ref_under                       []
% 7.73/1.49  
% 7.73/1.49  ------ SAT Options
% 7.73/1.49  
% 7.73/1.49  --sat_mode                              false
% 7.73/1.49  --sat_fm_restart_options                ""
% 7.73/1.49  --sat_gr_def                            false
% 7.73/1.49  --sat_epr_types                         true
% 7.73/1.49  --sat_non_cyclic_types                  false
% 7.73/1.49  --sat_finite_models                     false
% 7.73/1.49  --sat_fm_lemmas                         false
% 7.73/1.49  --sat_fm_prep                           false
% 7.73/1.49  --sat_fm_uc_incr                        true
% 7.73/1.49  --sat_out_model                         small
% 7.73/1.49  --sat_out_clauses                       false
% 7.73/1.49  
% 7.73/1.49  ------ QBF Options
% 7.73/1.49  
% 7.73/1.49  --qbf_mode                              false
% 7.73/1.49  --qbf_elim_univ                         false
% 7.73/1.49  --qbf_dom_inst                          none
% 7.73/1.49  --qbf_dom_pre_inst                      false
% 7.73/1.49  --qbf_sk_in                             false
% 7.73/1.49  --qbf_pred_elim                         true
% 7.73/1.49  --qbf_split                             512
% 7.73/1.49  
% 7.73/1.49  ------ BMC1 Options
% 7.73/1.49  
% 7.73/1.49  --bmc1_incremental                      false
% 7.73/1.49  --bmc1_axioms                           reachable_all
% 7.73/1.49  --bmc1_min_bound                        0
% 7.73/1.49  --bmc1_max_bound                        -1
% 7.73/1.49  --bmc1_max_bound_default                -1
% 7.73/1.49  --bmc1_symbol_reachability              true
% 7.73/1.49  --bmc1_property_lemmas                  false
% 7.73/1.49  --bmc1_k_induction                      false
% 7.73/1.49  --bmc1_non_equiv_states                 false
% 7.73/1.49  --bmc1_deadlock                         false
% 7.73/1.49  --bmc1_ucm                              false
% 7.73/1.49  --bmc1_add_unsat_core                   none
% 7.73/1.49  --bmc1_unsat_core_children              false
% 7.73/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.73/1.49  --bmc1_out_stat                         full
% 7.73/1.49  --bmc1_ground_init                      false
% 7.73/1.49  --bmc1_pre_inst_next_state              false
% 7.73/1.49  --bmc1_pre_inst_state                   false
% 7.73/1.49  --bmc1_pre_inst_reach_state             false
% 7.73/1.49  --bmc1_out_unsat_core                   false
% 7.73/1.49  --bmc1_aig_witness_out                  false
% 7.73/1.49  --bmc1_verbose                          false
% 7.73/1.49  --bmc1_dump_clauses_tptp                false
% 7.73/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.73/1.49  --bmc1_dump_file                        -
% 7.73/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.73/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.73/1.49  --bmc1_ucm_extend_mode                  1
% 7.73/1.49  --bmc1_ucm_init_mode                    2
% 7.73/1.49  --bmc1_ucm_cone_mode                    none
% 7.73/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.73/1.49  --bmc1_ucm_relax_model                  4
% 7.73/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.73/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.73/1.49  --bmc1_ucm_layered_model                none
% 7.73/1.49  --bmc1_ucm_max_lemma_size               10
% 7.73/1.49  
% 7.73/1.49  ------ AIG Options
% 7.73/1.49  
% 7.73/1.49  --aig_mode                              false
% 7.73/1.49  
% 7.73/1.49  ------ Instantiation Options
% 7.73/1.49  
% 7.73/1.49  --instantiation_flag                    true
% 7.73/1.49  --inst_sos_flag                         true
% 7.73/1.49  --inst_sos_phase                        true
% 7.73/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.73/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.73/1.49  --inst_lit_sel_side                     none
% 7.73/1.49  --inst_solver_per_active                1400
% 7.73/1.49  --inst_solver_calls_frac                1.
% 7.73/1.49  --inst_passive_queue_type               priority_queues
% 7.73/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.73/1.49  --inst_passive_queues_freq              [25;2]
% 7.73/1.49  --inst_dismatching                      true
% 7.73/1.49  --inst_eager_unprocessed_to_passive     true
% 7.73/1.49  --inst_prop_sim_given                   true
% 7.73/1.49  --inst_prop_sim_new                     false
% 7.73/1.49  --inst_subs_new                         false
% 7.73/1.49  --inst_eq_res_simp                      false
% 7.73/1.49  --inst_subs_given                       false
% 7.73/1.49  --inst_orphan_elimination               true
% 7.73/1.49  --inst_learning_loop_flag               true
% 7.73/1.49  --inst_learning_start                   3000
% 7.73/1.49  --inst_learning_factor                  2
% 7.73/1.49  --inst_start_prop_sim_after_learn       3
% 7.73/1.49  --inst_sel_renew                        solver
% 7.73/1.49  --inst_lit_activity_flag                true
% 7.73/1.49  --inst_restr_to_given                   false
% 7.73/1.49  --inst_activity_threshold               500
% 7.73/1.49  --inst_out_proof                        true
% 7.73/1.49  
% 7.73/1.49  ------ Resolution Options
% 7.73/1.49  
% 7.73/1.49  --resolution_flag                       false
% 7.73/1.49  --res_lit_sel                           adaptive
% 7.73/1.49  --res_lit_sel_side                      none
% 7.73/1.49  --res_ordering                          kbo
% 7.73/1.49  --res_to_prop_solver                    active
% 7.73/1.49  --res_prop_simpl_new                    false
% 7.73/1.49  --res_prop_simpl_given                  true
% 7.73/1.49  --res_passive_queue_type                priority_queues
% 7.73/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.73/1.49  --res_passive_queues_freq               [15;5]
% 7.73/1.49  --res_forward_subs                      full
% 7.73/1.49  --res_backward_subs                     full
% 7.73/1.49  --res_forward_subs_resolution           true
% 7.73/1.49  --res_backward_subs_resolution          true
% 7.73/1.49  --res_orphan_elimination                true
% 7.73/1.49  --res_time_limit                        2.
% 7.73/1.49  --res_out_proof                         true
% 7.73/1.49  
% 7.73/1.49  ------ Superposition Options
% 7.73/1.49  
% 7.73/1.49  --superposition_flag                    true
% 7.73/1.49  --sup_passive_queue_type                priority_queues
% 7.73/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.73/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.73/1.49  --demod_completeness_check              fast
% 7.73/1.49  --demod_use_ground                      true
% 7.73/1.49  --sup_to_prop_solver                    passive
% 7.73/1.49  --sup_prop_simpl_new                    true
% 7.73/1.49  --sup_prop_simpl_given                  true
% 7.73/1.49  --sup_fun_splitting                     true
% 7.73/1.49  --sup_smt_interval                      50000
% 7.73/1.49  
% 7.73/1.49  ------ Superposition Simplification Setup
% 7.73/1.49  
% 7.73/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.73/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.73/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.73/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.73/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.73/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.73/1.49  --sup_immed_triv                        [TrivRules]
% 7.73/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.49  --sup_immed_bw_main                     []
% 7.73/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.73/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.73/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.49  --sup_input_bw                          []
% 7.73/1.49  
% 7.73/1.49  ------ Combination Options
% 7.73/1.49  
% 7.73/1.49  --comb_res_mult                         3
% 7.73/1.49  --comb_sup_mult                         2
% 7.73/1.49  --comb_inst_mult                        10
% 7.73/1.49  
% 7.73/1.49  ------ Debug Options
% 7.73/1.49  
% 7.73/1.49  --dbg_backtrace                         false
% 7.73/1.49  --dbg_dump_prop_clauses                 false
% 7.73/1.49  --dbg_dump_prop_clauses_file            -
% 7.73/1.49  --dbg_out_stat                          false
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  % SZS status Theorem for theBenchmark.p
% 7.73/1.49  
% 7.73/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.73/1.49  
% 7.73/1.49  fof(f38,conjecture,(
% 7.73/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f39,negated_conjecture,(
% 7.73/1.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 7.73/1.49    inference(negated_conjecture,[],[f38])).
% 7.73/1.49  
% 7.73/1.49  fof(f41,plain,(
% 7.73/1.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 7.73/1.49    inference(pure_predicate_removal,[],[f39])).
% 7.73/1.49  
% 7.73/1.49  fof(f79,plain,(
% 7.73/1.49    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 7.73/1.49    inference(ennf_transformation,[],[f41])).
% 7.73/1.49  
% 7.73/1.49  fof(f80,plain,(
% 7.73/1.49    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 7.73/1.49    inference(flattening,[],[f79])).
% 7.73/1.49  
% 7.73/1.49  fof(f108,plain,(
% 7.73/1.49    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK10 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(sK10,k7_relset_1(X0,X1,X3,X2)))) )),
% 7.73/1.49    introduced(choice_axiom,[])).
% 7.73/1.49  
% 7.73/1.49  fof(f107,plain,(
% 7.73/1.49    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK9,X5) != X4 | ~r2_hidden(X5,sK8) | ~m1_subset_1(X5,sK6)) & r2_hidden(X4,k7_relset_1(sK6,sK7,sK9,sK8))) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_1(sK9))),
% 7.73/1.49    introduced(choice_axiom,[])).
% 7.73/1.49  
% 7.73/1.49  fof(f109,plain,(
% 7.73/1.49    (! [X5] : (k1_funct_1(sK9,X5) != sK10 | ~r2_hidden(X5,sK8) | ~m1_subset_1(X5,sK6)) & r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8))) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_1(sK9)),
% 7.73/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10])],[f80,f108,f107])).
% 7.73/1.49  
% 7.73/1.49  fof(f173,plain,(
% 7.73/1.49    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))),
% 7.73/1.49    inference(cnf_transformation,[],[f109])).
% 7.73/1.49  
% 7.73/1.49  fof(f30,axiom,(
% 7.73/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f72,plain,(
% 7.73/1.49    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.73/1.49    inference(ennf_transformation,[],[f30])).
% 7.73/1.49  
% 7.73/1.49  fof(f154,plain,(
% 7.73/1.49    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.73/1.49    inference(cnf_transformation,[],[f72])).
% 7.73/1.49  
% 7.73/1.49  fof(f33,axiom,(
% 7.73/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f75,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.73/1.49    inference(ennf_transformation,[],[f33])).
% 7.73/1.49  
% 7.73/1.49  fof(f99,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.73/1.49    inference(nnf_transformation,[],[f75])).
% 7.73/1.49  
% 7.73/1.49  fof(f100,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.73/1.49    inference(rectify,[],[f99])).
% 7.73/1.49  
% 7.73/1.49  fof(f101,plain,(
% 7.73/1.49    ! [X4,X3,X2,X1] : (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) => (r2_hidden(sK3(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK3(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK3(X1,X2,X3,X4),X2)))),
% 7.73/1.49    introduced(choice_axiom,[])).
% 7.73/1.49  
% 7.73/1.49  fof(f102,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & ((r2_hidden(sK3(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK3(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK3(X1,X2,X3,X4),X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.73/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f100,f101])).
% 7.73/1.49  
% 7.73/1.49  fof(f160,plain,(
% 7.73/1.49    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK3(X1,X2,X3,X4),X1) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f102])).
% 7.73/1.49  
% 7.73/1.49  fof(f174,plain,(
% 7.73/1.49    r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8))),
% 7.73/1.49    inference(cnf_transformation,[],[f109])).
% 7.73/1.49  
% 7.73/1.49  fof(f159,plain,(
% 7.73/1.49    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK3(X1,X2,X3,X4),X4),X3) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f102])).
% 7.73/1.49  
% 7.73/1.49  fof(f24,axiom,(
% 7.73/1.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f66,plain,(
% 7.73/1.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.73/1.49    inference(ennf_transformation,[],[f24])).
% 7.73/1.49  
% 7.73/1.49  fof(f67,plain,(
% 7.73/1.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.73/1.49    inference(flattening,[],[f66])).
% 7.73/1.49  
% 7.73/1.49  fof(f96,plain,(
% 7.73/1.49    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.73/1.49    inference(nnf_transformation,[],[f67])).
% 7.73/1.49  
% 7.73/1.49  fof(f97,plain,(
% 7.73/1.49    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.73/1.49    inference(flattening,[],[f96])).
% 7.73/1.49  
% 7.73/1.49  fof(f146,plain,(
% 7.73/1.49    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f97])).
% 7.73/1.49  
% 7.73/1.49  fof(f172,plain,(
% 7.73/1.49    v1_funct_1(sK9)),
% 7.73/1.49    inference(cnf_transformation,[],[f109])).
% 7.73/1.49  
% 7.73/1.49  fof(f26,axiom,(
% 7.73/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f68,plain,(
% 7.73/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.73/1.49    inference(ennf_transformation,[],[f26])).
% 7.73/1.49  
% 7.73/1.49  fof(f150,plain,(
% 7.73/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.73/1.49    inference(cnf_transformation,[],[f68])).
% 7.73/1.49  
% 7.73/1.49  fof(f17,axiom,(
% 7.73/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f57,plain,(
% 7.73/1.49    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 7.73/1.49    inference(ennf_transformation,[],[f17])).
% 7.73/1.49  
% 7.73/1.49  fof(f92,plain,(
% 7.73/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.73/1.49    inference(nnf_transformation,[],[f57])).
% 7.73/1.49  
% 7.73/1.49  fof(f93,plain,(
% 7.73/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.73/1.49    inference(rectify,[],[f92])).
% 7.73/1.49  
% 7.73/1.49  fof(f94,plain,(
% 7.73/1.49    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))))),
% 7.73/1.49    introduced(choice_axiom,[])).
% 7.73/1.49  
% 7.73/1.49  fof(f95,plain,(
% 7.73/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.73/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f93,f94])).
% 7.73/1.49  
% 7.73/1.49  fof(f135,plain,(
% 7.73/1.49    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f95])).
% 7.73/1.49  
% 7.73/1.49  fof(f10,axiom,(
% 7.73/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f50,plain,(
% 7.73/1.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.73/1.49    inference(ennf_transformation,[],[f10])).
% 7.73/1.49  
% 7.73/1.49  fof(f126,plain,(
% 7.73/1.49    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.73/1.49    inference(cnf_transformation,[],[f50])).
% 7.73/1.49  
% 7.73/1.49  fof(f5,axiom,(
% 7.73/1.49    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f87,plain,(
% 7.73/1.49    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 7.73/1.49    inference(nnf_transformation,[],[f5])).
% 7.73/1.49  
% 7.73/1.49  fof(f88,plain,(
% 7.73/1.49    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 7.73/1.49    inference(flattening,[],[f87])).
% 7.73/1.49  
% 7.73/1.49  fof(f118,plain,(
% 7.73/1.49    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 7.73/1.49    inference(cnf_transformation,[],[f88])).
% 7.73/1.49  
% 7.73/1.49  fof(f4,axiom,(
% 7.73/1.49    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f49,plain,(
% 7.73/1.49    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 7.73/1.49    inference(ennf_transformation,[],[f4])).
% 7.73/1.49  
% 7.73/1.49  fof(f116,plain,(
% 7.73/1.49    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f49])).
% 7.73/1.49  
% 7.73/1.49  fof(f1,axiom,(
% 7.73/1.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f81,plain,(
% 7.73/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.73/1.49    inference(nnf_transformation,[],[f1])).
% 7.73/1.49  
% 7.73/1.49  fof(f82,plain,(
% 7.73/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.73/1.49    inference(rectify,[],[f81])).
% 7.73/1.49  
% 7.73/1.49  fof(f83,plain,(
% 7.73/1.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.73/1.49    introduced(choice_axiom,[])).
% 7.73/1.49  
% 7.73/1.49  fof(f84,plain,(
% 7.73/1.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.73/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f82,f83])).
% 7.73/1.49  
% 7.73/1.49  fof(f111,plain,(
% 7.73/1.49    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f84])).
% 7.73/1.49  
% 7.73/1.49  fof(f136,plain,(
% 7.73/1.49    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f95])).
% 7.73/1.49  
% 7.73/1.49  fof(f14,axiom,(
% 7.73/1.49    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f52,plain,(
% 7.73/1.49    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 7.73/1.49    inference(ennf_transformation,[],[f14])).
% 7.73/1.49  
% 7.73/1.49  fof(f131,plain,(
% 7.73/1.49    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f52])).
% 7.73/1.49  
% 7.73/1.49  fof(f2,axiom,(
% 7.73/1.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f47,plain,(
% 7.73/1.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 7.73/1.49    inference(ennf_transformation,[],[f2])).
% 7.73/1.49  
% 7.73/1.49  fof(f112,plain,(
% 7.73/1.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f47])).
% 7.73/1.49  
% 7.73/1.49  fof(f175,plain,(
% 7.73/1.49    ( ! [X5] : (k1_funct_1(sK9,X5) != sK10 | ~r2_hidden(X5,sK8) | ~m1_subset_1(X5,sK6)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f109])).
% 7.73/1.49  
% 7.73/1.49  fof(f158,plain,(
% 7.73/1.49    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK3(X1,X2,X3,X4),X2) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f102])).
% 7.73/1.49  
% 7.73/1.49  fof(f35,axiom,(
% 7.73/1.49    ! [X0,X1] : ? [X2] : (v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & v1_xboole_0(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f44,plain,(
% 7.73/1.49    ! [X0,X1] : ? [X2] : (v4_relat_1(X2,X0) & v1_relat_1(X2) & v1_xboole_0(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.73/1.49    inference(pure_predicate_removal,[],[f35])).
% 7.73/1.49  
% 7.73/1.49  fof(f105,plain,(
% 7.73/1.49    ! [X1,X0] : (? [X2] : (v4_relat_1(X2,X0) & v1_relat_1(X2) & v1_xboole_0(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v4_relat_1(sK5(X0,X1),X0) & v1_relat_1(sK5(X0,X1)) & v1_xboole_0(sK5(X0,X1)) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.73/1.49    introduced(choice_axiom,[])).
% 7.73/1.49  
% 7.73/1.49  fof(f106,plain,(
% 7.73/1.49    ! [X0,X1] : (v4_relat_1(sK5(X0,X1),X0) & v1_relat_1(sK5(X0,X1)) & v1_xboole_0(sK5(X0,X1)) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.73/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f105])).
% 7.73/1.49  
% 7.73/1.49  fof(f166,plain,(
% 7.73/1.49    ( ! [X0,X1] : (v1_xboole_0(sK5(X0,X1))) )),
% 7.73/1.49    inference(cnf_transformation,[],[f106])).
% 7.73/1.49  
% 7.73/1.49  fof(f6,axiom,(
% 7.73/1.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f89,plain,(
% 7.73/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.73/1.49    inference(nnf_transformation,[],[f6])).
% 7.73/1.49  
% 7.73/1.49  fof(f90,plain,(
% 7.73/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.73/1.49    inference(flattening,[],[f89])).
% 7.73/1.49  
% 7.73/1.49  fof(f121,plain,(
% 7.73/1.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.73/1.49    inference(cnf_transformation,[],[f90])).
% 7.73/1.49  
% 7.73/1.49  fof(f185,plain,(
% 7.73/1.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.73/1.49    inference(equality_resolution,[],[f121])).
% 7.73/1.49  
% 7.73/1.49  fof(f28,axiom,(
% 7.73/1.49    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f70,plain,(
% 7.73/1.49    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 7.73/1.49    inference(ennf_transformation,[],[f28])).
% 7.73/1.49  
% 7.73/1.49  fof(f152,plain,(
% 7.73/1.49    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f70])).
% 7.73/1.49  
% 7.73/1.49  cnf(c_61,negated_conjecture,
% 7.73/1.49      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
% 7.73/1.49      inference(cnf_transformation,[],[f173]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2009,plain,
% 7.73/1.49      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_61]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_42,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.49      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 7.73/1.49      inference(cnf_transformation,[],[f154]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2027,plain,
% 7.73/1.49      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 7.73/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_5967,plain,
% 7.73/1.49      ( k7_relset_1(sK6,sK7,sK9,X0) = k9_relat_1(sK9,X0) ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_2009,c_2027]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_47,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,X1)
% 7.73/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 7.73/1.49      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 7.73/1.49      | r2_hidden(sK3(X4,X3,X2,X0),X4)
% 7.73/1.49      | v1_xboole_0(X1)
% 7.73/1.49      | v1_xboole_0(X3)
% 7.73/1.49      | v1_xboole_0(X4) ),
% 7.73/1.49      inference(cnf_transformation,[],[f160]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2022,plain,
% 7.73/1.49      ( m1_subset_1(X0,X1) != iProver_top
% 7.73/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 7.73/1.49      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 7.73/1.49      | r2_hidden(sK3(X4,X3,X2,X0),X4) = iProver_top
% 7.73/1.49      | v1_xboole_0(X1) = iProver_top
% 7.73/1.49      | v1_xboole_0(X3) = iProver_top
% 7.73/1.49      | v1_xboole_0(X4) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_6993,plain,
% 7.73/1.49      ( m1_subset_1(X0,sK7) != iProver_top
% 7.73/1.49      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
% 7.73/1.49      | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
% 7.73/1.49      | r2_hidden(sK3(X1,sK6,sK9,X0),X1) = iProver_top
% 7.73/1.49      | v1_xboole_0(X1) = iProver_top
% 7.73/1.49      | v1_xboole_0(sK7) = iProver_top
% 7.73/1.49      | v1_xboole_0(sK6) = iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_5967,c_2022]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_64,plain,
% 7.73/1.49      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_61]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_8474,plain,
% 7.73/1.49      ( m1_subset_1(X0,sK7) != iProver_top
% 7.73/1.49      | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
% 7.73/1.49      | r2_hidden(sK3(X1,sK6,sK9,X0),X1) = iProver_top
% 7.73/1.49      | v1_xboole_0(X1) = iProver_top
% 7.73/1.49      | v1_xboole_0(sK7) = iProver_top
% 7.73/1.49      | v1_xboole_0(sK6) = iProver_top ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_6993,c_64]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_60,negated_conjecture,
% 7.73/1.49      ( r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8)) ),
% 7.73/1.49      inference(cnf_transformation,[],[f174]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2010,plain,
% 7.73/1.49      ( r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8)) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_5984,plain,
% 7.73/1.49      ( r2_hidden(sK10,k9_relat_1(sK9,sK8)) = iProver_top ),
% 7.73/1.49      inference(demodulation,[status(thm)],[c_5967,c_2010]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_48,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,X1)
% 7.73/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 7.73/1.49      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 7.73/1.49      | r2_hidden(k4_tarski(sK3(X4,X3,X2,X0),X0),X2)
% 7.73/1.49      | v1_xboole_0(X1)
% 7.73/1.49      | v1_xboole_0(X3)
% 7.73/1.49      | v1_xboole_0(X4) ),
% 7.73/1.49      inference(cnf_transformation,[],[f159]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2021,plain,
% 7.73/1.49      ( m1_subset_1(X0,X1) != iProver_top
% 7.73/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 7.73/1.49      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 7.73/1.49      | r2_hidden(k4_tarski(sK3(X4,X3,X2,X0),X0),X2) = iProver_top
% 7.73/1.49      | v1_xboole_0(X1) = iProver_top
% 7.73/1.49      | v1_xboole_0(X3) = iProver_top
% 7.73/1.49      | v1_xboole_0(X4) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_6279,plain,
% 7.73/1.49      ( m1_subset_1(X0,sK7) != iProver_top
% 7.73/1.49      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
% 7.73/1.49      | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
% 7.73/1.49      | r2_hidden(k4_tarski(sK3(X1,sK6,sK9,X0),X0),sK9) = iProver_top
% 7.73/1.49      | v1_xboole_0(X1) = iProver_top
% 7.73/1.49      | v1_xboole_0(sK7) = iProver_top
% 7.73/1.49      | v1_xboole_0(sK6) = iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_5967,c_2021]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_6550,plain,
% 7.73/1.49      ( m1_subset_1(X0,sK7) != iProver_top
% 7.73/1.49      | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
% 7.73/1.49      | r2_hidden(k4_tarski(sK3(X1,sK6,sK9,X0),X0),sK9) = iProver_top
% 7.73/1.49      | v1_xboole_0(X1) = iProver_top
% 7.73/1.49      | v1_xboole_0(sK7) = iProver_top
% 7.73/1.49      | v1_xboole_0(sK6) = iProver_top ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_6279,c_64]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_34,plain,
% 7.73/1.49      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 7.73/1.49      | ~ v1_funct_1(X2)
% 7.73/1.49      | ~ v1_relat_1(X2)
% 7.73/1.49      | k1_funct_1(X2,X0) = X1 ),
% 7.73/1.49      inference(cnf_transformation,[],[f146]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2035,plain,
% 7.73/1.49      ( k1_funct_1(X0,X1) = X2
% 7.73/1.49      | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
% 7.73/1.49      | v1_funct_1(X0) != iProver_top
% 7.73/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_10777,plain,
% 7.73/1.49      ( k1_funct_1(sK9,sK3(X0,sK6,sK9,X1)) = X1
% 7.73/1.49      | m1_subset_1(X1,sK7) != iProver_top
% 7.73/1.49      | r2_hidden(X1,k9_relat_1(sK9,X0)) != iProver_top
% 7.73/1.49      | v1_funct_1(sK9) != iProver_top
% 7.73/1.49      | v1_relat_1(sK9) != iProver_top
% 7.73/1.49      | v1_xboole_0(X0) = iProver_top
% 7.73/1.49      | v1_xboole_0(sK7) = iProver_top
% 7.73/1.49      | v1_xboole_0(sK6) = iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_6550,c_2035]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_62,negated_conjecture,
% 7.73/1.49      ( v1_funct_1(sK9) ),
% 7.73/1.49      inference(cnf_transformation,[],[f172]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_63,plain,
% 7.73/1.49      ( v1_funct_1(sK9) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_62]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_38,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.49      | v1_relat_1(X0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f150]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2031,plain,
% 7.73/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.73/1.49      | v1_relat_1(X0) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_4587,plain,
% 7.73/1.49      ( v1_relat_1(sK9) = iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_2009,c_2031]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_24,plain,
% 7.73/1.49      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.73/1.49      | r2_hidden(k4_tarski(sK2(X0,X2,X1),X0),X1)
% 7.73/1.49      | ~ v1_relat_1(X1) ),
% 7.73/1.49      inference(cnf_transformation,[],[f135]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2043,plain,
% 7.73/1.49      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 7.73/1.49      | r2_hidden(k4_tarski(sK2(X0,X2,X1),X0),X1) = iProver_top
% 7.73/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_15,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.73/1.49      | ~ r2_hidden(X2,X0)
% 7.73/1.49      | r2_hidden(X2,X1) ),
% 7.73/1.49      inference(cnf_transformation,[],[f126]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2051,plain,
% 7.73/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.73/1.49      | r2_hidden(X2,X0) != iProver_top
% 7.73/1.49      | r2_hidden(X2,X1) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_7148,plain,
% 7.73/1.49      ( r2_hidden(X0,k2_zfmisc_1(sK6,sK7)) = iProver_top
% 7.73/1.49      | r2_hidden(X0,sK9) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_2009,c_2051]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_8,plain,
% 7.73/1.49      ( r2_hidden(X0,X1)
% 7.73/1.49      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 7.73/1.49      inference(cnf_transformation,[],[f118]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2054,plain,
% 7.73/1.49      ( r2_hidden(X0,X1) = iProver_top
% 7.73/1.49      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_7769,plain,
% 7.73/1.49      ( r2_hidden(X0,sK7) = iProver_top
% 7.73/1.49      | r2_hidden(k4_tarski(X1,X0),sK9) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_7148,c_2054]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_10574,plain,
% 7.73/1.49      ( r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
% 7.73/1.49      | r2_hidden(X0,sK7) = iProver_top
% 7.73/1.49      | v1_relat_1(sK9) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_2043,c_7769]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_11194,plain,
% 7.73/1.49      ( r2_hidden(X0,sK7) = iProver_top
% 7.73/1.49      | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_10574,c_4587]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_11195,plain,
% 7.73/1.49      ( r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
% 7.73/1.49      | r2_hidden(X0,sK7) = iProver_top ),
% 7.73/1.49      inference(renaming,[status(thm)],[c_11194]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_11206,plain,
% 7.73/1.49      ( r2_hidden(sK10,sK7) = iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_5984,c_11195]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_6,plain,
% 7.73/1.49      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.73/1.49      inference(cnf_transformation,[],[f116]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2060,plain,
% 7.73/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.73/1.49      | v1_xboole_0(X1) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_11237,plain,
% 7.73/1.49      ( v1_xboole_0(sK7) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_11206,c_2060]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_19910,plain,
% 7.73/1.49      ( v1_xboole_0(X0) = iProver_top
% 7.73/1.49      | r2_hidden(X1,k9_relat_1(sK9,X0)) != iProver_top
% 7.73/1.49      | m1_subset_1(X1,sK7) != iProver_top
% 7.73/1.49      | k1_funct_1(sK9,sK3(X0,sK6,sK9,X1)) = X1
% 7.73/1.49      | v1_xboole_0(sK6) = iProver_top ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_10777,c_63,c_4587,c_11237]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_19911,plain,
% 7.73/1.49      ( k1_funct_1(sK9,sK3(X0,sK6,sK9,X1)) = X1
% 7.73/1.49      | m1_subset_1(X1,sK7) != iProver_top
% 7.73/1.49      | r2_hidden(X1,k9_relat_1(sK9,X0)) != iProver_top
% 7.73/1.49      | v1_xboole_0(X0) = iProver_top
% 7.73/1.49      | v1_xboole_0(sK6) = iProver_top ),
% 7.73/1.49      inference(renaming,[status(thm)],[c_19910]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_19921,plain,
% 7.73/1.49      ( k1_funct_1(sK9,sK3(sK8,sK6,sK9,sK10)) = sK10
% 7.73/1.49      | m1_subset_1(sK10,sK7) != iProver_top
% 7.73/1.49      | v1_xboole_0(sK6) = iProver_top
% 7.73/1.49      | v1_xboole_0(sK8) = iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_5984,c_19911]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_65,plain,
% 7.73/1.49      ( r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8)) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2124,plain,
% 7.73/1.49      ( ~ r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8))
% 7.73/1.49      | ~ v1_xboole_0(k7_relset_1(sK6,sK7,sK9,sK8)) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2125,plain,
% 7.73/1.49      ( r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8)) != iProver_top
% 7.73/1.49      | v1_xboole_0(k7_relset_1(sK6,sK7,sK9,sK8)) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_2124]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1136,plain,
% 7.73/1.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 7.73/1.49      theory(equality) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2169,plain,
% 7.73/1.49      ( ~ v1_xboole_0(X0)
% 7.73/1.49      | v1_xboole_0(k7_relset_1(sK6,sK7,sK9,sK8))
% 7.73/1.49      | k7_relset_1(sK6,sK7,sK9,sK8) != X0 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_1136]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2338,plain,
% 7.73/1.49      ( v1_xboole_0(k7_relset_1(sK6,sK7,sK9,sK8))
% 7.73/1.49      | ~ v1_xboole_0(k9_relat_1(sK9,sK8))
% 7.73/1.49      | k7_relset_1(sK6,sK7,sK9,sK8) != k9_relat_1(sK9,sK8) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_2169]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2339,plain,
% 7.73/1.49      ( k7_relset_1(sK6,sK7,sK9,sK8) != k9_relat_1(sK9,sK8)
% 7.73/1.49      | v1_xboole_0(k7_relset_1(sK6,sK7,sK9,sK8)) = iProver_top
% 7.73/1.49      | v1_xboole_0(k9_relat_1(sK9,sK8)) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_2338]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_0,plain,
% 7.73/1.49      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f111]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2844,plain,
% 7.73/1.49      ( r2_hidden(sK0(k9_relat_1(sK9,sK8)),k9_relat_1(sK9,sK8))
% 7.73/1.49      | v1_xboole_0(k9_relat_1(sK9,sK8)) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2845,plain,
% 7.73/1.49      ( r2_hidden(sK0(k9_relat_1(sK9,sK8)),k9_relat_1(sK9,sK8)) = iProver_top
% 7.73/1.49      | v1_xboole_0(k9_relat_1(sK9,sK8)) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_2844]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_3630,plain,
% 7.73/1.49      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 7.73/1.49      | k7_relset_1(sK6,sK7,sK9,sK8) = k9_relat_1(sK9,sK8) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_42]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_23,plain,
% 7.73/1.49      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.73/1.49      | r2_hidden(sK2(X0,X2,X1),X2)
% 7.73/1.49      | ~ v1_relat_1(X1) ),
% 7.73/1.49      inference(cnf_transformation,[],[f136]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_5568,plain,
% 7.73/1.49      ( r2_hidden(sK2(sK0(k9_relat_1(sK9,sK8)),sK8,sK9),sK8)
% 7.73/1.49      | ~ r2_hidden(sK0(k9_relat_1(sK9,sK8)),k9_relat_1(sK9,sK8))
% 7.73/1.49      | ~ v1_relat_1(sK9) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_23]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_5569,plain,
% 7.73/1.49      ( r2_hidden(sK2(sK0(k9_relat_1(sK9,sK8)),sK8,sK9),sK8) = iProver_top
% 7.73/1.49      | r2_hidden(sK0(k9_relat_1(sK9,sK8)),k9_relat_1(sK9,sK8)) != iProver_top
% 7.73/1.49      | v1_relat_1(sK9) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_5568]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_19,plain,
% 7.73/1.49      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 7.73/1.49      inference(cnf_transformation,[],[f131]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2048,plain,
% 7.73/1.49      ( m1_subset_1(X0,X1) = iProver_top
% 7.73/1.49      | r2_hidden(X0,X1) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_11238,plain,
% 7.73/1.49      ( m1_subset_1(sK10,sK7) = iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_11206,c_2048]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_12606,plain,
% 7.73/1.49      ( ~ r2_hidden(sK2(sK0(k9_relat_1(sK9,sK8)),sK8,sK9),sK8)
% 7.73/1.49      | ~ v1_xboole_0(sK8) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_12607,plain,
% 7.73/1.49      ( r2_hidden(sK2(sK0(k9_relat_1(sK9,sK8)),sK8,sK9),sK8) != iProver_top
% 7.73/1.49      | v1_xboole_0(sK8) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_12606]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_20111,plain,
% 7.73/1.49      ( v1_xboole_0(sK6) = iProver_top
% 7.73/1.49      | k1_funct_1(sK9,sK3(sK8,sK6,sK9,sK10)) = sK10 ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_19921,c_61,c_65,c_2125,c_2339,c_2845,c_3630,c_4587,
% 7.73/1.49                 c_5569,c_11238,c_12607]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_20112,plain,
% 7.73/1.49      ( k1_funct_1(sK9,sK3(sK8,sK6,sK9,sK10)) = sK10
% 7.73/1.49      | v1_xboole_0(sK6) = iProver_top ),
% 7.73/1.49      inference(renaming,[status(thm)],[c_20111]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2,plain,
% 7.73/1.49      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 7.73/1.49      inference(cnf_transformation,[],[f112]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2059,plain,
% 7.73/1.49      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_20115,plain,
% 7.73/1.49      ( k1_funct_1(sK9,sK3(sK8,sK6,sK9,sK10)) = sK10
% 7.73/1.49      | sK6 = k1_xboole_0 ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_20112,c_2059]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_59,negated_conjecture,
% 7.73/1.49      ( ~ m1_subset_1(X0,sK6)
% 7.73/1.49      | ~ r2_hidden(X0,sK8)
% 7.73/1.49      | k1_funct_1(sK9,X0) != sK10 ),
% 7.73/1.49      inference(cnf_transformation,[],[f175]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2011,plain,
% 7.73/1.49      ( k1_funct_1(sK9,X0) != sK10
% 7.73/1.49      | m1_subset_1(X0,sK6) != iProver_top
% 7.73/1.49      | r2_hidden(X0,sK8) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_20397,plain,
% 7.73/1.49      ( sK6 = k1_xboole_0
% 7.73/1.49      | m1_subset_1(sK3(sK8,sK6,sK9,sK10),sK6) != iProver_top
% 7.73/1.49      | r2_hidden(sK3(sK8,sK6,sK9,sK10),sK8) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_20115,c_2011]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1134,plain,( X0 = X0 ),theory(equality) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2687,plain,
% 7.73/1.49      ( sK6 = sK6 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_1134]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1135,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2324,plain,
% 7.73/1.49      ( X0 != X1 | sK6 != X1 | sK6 = X0 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_1135]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2689,plain,
% 7.73/1.49      ( X0 != sK6 | sK6 = X0 | sK6 != sK6 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_2324]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2690,plain,
% 7.73/1.49      ( sK6 != sK6 | sK6 = k1_xboole_0 | k1_xboole_0 != sK6 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_2689]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_4294,plain,
% 7.73/1.49      ( ~ v1_xboole_0(sK6) | k1_xboole_0 = sK6 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_2]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_4295,plain,
% 7.73/1.49      ( k1_xboole_0 = sK6 | v1_xboole_0(sK6) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_4294]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_49,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,X1)
% 7.73/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 7.73/1.49      | m1_subset_1(sK3(X4,X3,X2,X0),X3)
% 7.73/1.49      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 7.73/1.49      | v1_xboole_0(X1)
% 7.73/1.49      | v1_xboole_0(X3)
% 7.73/1.49      | v1_xboole_0(X4) ),
% 7.73/1.49      inference(cnf_transformation,[],[f158]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2020,plain,
% 7.73/1.49      ( m1_subset_1(X0,X1) != iProver_top
% 7.73/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 7.73/1.49      | m1_subset_1(sK3(X4,X3,X2,X0),X3) = iProver_top
% 7.73/1.49      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 7.73/1.49      | v1_xboole_0(X1) = iProver_top
% 7.73/1.49      | v1_xboole_0(X3) = iProver_top
% 7.73/1.49      | v1_xboole_0(X4) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_5872,plain,
% 7.73/1.49      ( m1_subset_1(sK3(sK8,sK6,sK9,sK10),sK6) = iProver_top
% 7.73/1.49      | m1_subset_1(sK10,sK7) != iProver_top
% 7.73/1.49      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
% 7.73/1.49      | v1_xboole_0(sK7) = iProver_top
% 7.73/1.49      | v1_xboole_0(sK6) = iProver_top
% 7.73/1.49      | v1_xboole_0(sK8) = iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_2010,c_2020]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_20939,plain,
% 7.73/1.49      ( sK6 = k1_xboole_0
% 7.73/1.49      | r2_hidden(sK3(sK8,sK6,sK9,sK10),sK8) != iProver_top ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_20397,c_61,c_64,c_65,c_2125,c_2339,c_2687,c_2690,
% 7.73/1.49                 c_2845,c_3630,c_4295,c_4587,c_5569,c_5872,c_11237,
% 7.73/1.49                 c_11238,c_12607]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_20943,plain,
% 7.73/1.49      ( sK6 = k1_xboole_0
% 7.73/1.49      | m1_subset_1(sK10,sK7) != iProver_top
% 7.73/1.49      | r2_hidden(sK10,k9_relat_1(sK9,sK8)) != iProver_top
% 7.73/1.49      | v1_xboole_0(sK7) = iProver_top
% 7.73/1.49      | v1_xboole_0(sK6) = iProver_top
% 7.73/1.49      | v1_xboole_0(sK8) = iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_8474,c_20939]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_55,plain,
% 7.73/1.49      ( v1_xboole_0(sK5(X0,X1)) ),
% 7.73/1.49      inference(cnf_transformation,[],[f166]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2014,plain,
% 7.73/1.49      ( v1_xboole_0(sK5(X0,X1)) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_3885,plain,
% 7.73/1.49      ( sK5(X0,X1) = k1_xboole_0 ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_2014,c_2059]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_3951,plain,
% 7.73/1.49      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.73/1.49      inference(demodulation,[status(thm)],[c_3885,c_2014]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_9318,plain,
% 7.73/1.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK6) | sK6 != X0 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_1136]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_9319,plain,
% 7.73/1.49      ( sK6 != X0
% 7.73/1.49      | v1_xboole_0(X0) != iProver_top
% 7.73/1.49      | v1_xboole_0(sK6) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_9318]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_9321,plain,
% 7.73/1.49      ( sK6 != k1_xboole_0
% 7.73/1.49      | v1_xboole_0(sK6) = iProver_top
% 7.73/1.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_9319]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_20946,plain,
% 7.73/1.49      ( v1_xboole_0(sK6) = iProver_top ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_20943,c_61,c_65,c_2125,c_2339,c_2845,c_3630,c_3951,
% 7.73/1.49                 c_4587,c_5569,c_5984,c_9321,c_11237,c_11238,c_12607]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_20951,plain,
% 7.73/1.49      ( sK6 = k1_xboole_0 ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_20946,c_2059]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_21099,plain,
% 7.73/1.49      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK7))) = iProver_top ),
% 7.73/1.49      inference(demodulation,[status(thm)],[c_20951,c_2009]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_11,plain,
% 7.73/1.49      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.73/1.49      inference(cnf_transformation,[],[f185]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_21100,plain,
% 7.73/1.49      ( m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.73/1.49      inference(demodulation,[status(thm)],[c_21099,c_11]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_40,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.49      | ~ v1_xboole_0(X2)
% 7.73/1.49      | v1_xboole_0(X0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f152]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2029,plain,
% 7.73/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.73/1.49      | v1_xboole_0(X2) != iProver_top
% 7.73/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_6402,plain,
% 7.73/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.73/1.49      | v1_xboole_0(X1) != iProver_top
% 7.73/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_11,c_2029]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_21221,plain,
% 7.73/1.49      ( v1_xboole_0(X0) != iProver_top | v1_xboole_0(sK9) = iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_21100,c_6402]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_21229,plain,
% 7.73/1.49      ( v1_xboole_0(sK9) = iProver_top
% 7.73/1.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_21221]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_12460,plain,
% 7.73/1.49      ( ~ r2_hidden(k4_tarski(sK2(sK0(k9_relat_1(sK9,sK8)),sK8,sK9),sK0(k9_relat_1(sK9,sK8))),sK9)
% 7.73/1.49      | ~ v1_xboole_0(sK9) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_12461,plain,
% 7.73/1.49      ( r2_hidden(k4_tarski(sK2(sK0(k9_relat_1(sK9,sK8)),sK8,sK9),sK0(k9_relat_1(sK9,sK8))),sK9) != iProver_top
% 7.73/1.49      | v1_xboole_0(sK9) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_12460]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_5567,plain,
% 7.73/1.49      ( r2_hidden(k4_tarski(sK2(sK0(k9_relat_1(sK9,sK8)),sK8,sK9),sK0(k9_relat_1(sK9,sK8))),sK9)
% 7.73/1.49      | ~ r2_hidden(sK0(k9_relat_1(sK9,sK8)),k9_relat_1(sK9,sK8))
% 7.73/1.49      | ~ v1_relat_1(sK9) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_24]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_5571,plain,
% 7.73/1.49      ( r2_hidden(k4_tarski(sK2(sK0(k9_relat_1(sK9,sK8)),sK8,sK9),sK0(k9_relat_1(sK9,sK8))),sK9) = iProver_top
% 7.73/1.49      | r2_hidden(sK0(k9_relat_1(sK9,sK8)),k9_relat_1(sK9,sK8)) != iProver_top
% 7.73/1.49      | v1_relat_1(sK9) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_5567]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(contradiction,plain,
% 7.73/1.49      ( $false ),
% 7.73/1.49      inference(minisat,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_21229,c_12461,c_5571,c_4587,c_3951,c_3630,c_2845,
% 7.73/1.49                 c_2339,c_2125,c_65,c_61]) ).
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.73/1.49  
% 7.73/1.49  ------                               Statistics
% 7.73/1.49  
% 7.73/1.49  ------ General
% 7.73/1.49  
% 7.73/1.49  abstr_ref_over_cycles:                  0
% 7.73/1.49  abstr_ref_under_cycles:                 0
% 7.73/1.49  gc_basic_clause_elim:                   0
% 7.73/1.49  forced_gc_time:                         0
% 7.73/1.49  parsing_time:                           0.012
% 7.73/1.49  unif_index_cands_time:                  0.
% 7.73/1.49  unif_index_add_time:                    0.
% 7.73/1.49  orderings_time:                         0.
% 7.73/1.49  out_proof_time:                         0.017
% 7.73/1.49  total_time:                             0.755
% 7.73/1.49  num_of_symbols:                         66
% 7.73/1.49  num_of_terms:                           30381
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing
% 7.73/1.49  
% 7.73/1.49  num_of_splits:                          0
% 7.73/1.49  num_of_split_atoms:                     0
% 7.73/1.49  num_of_reused_defs:                     0
% 7.73/1.49  num_eq_ax_congr_red:                    96
% 7.73/1.49  num_of_sem_filtered_clauses:            1
% 7.73/1.49  num_of_subtypes:                        0
% 7.73/1.49  monotx_restored_types:                  0
% 7.73/1.49  sat_num_of_epr_types:                   0
% 7.73/1.49  sat_num_of_non_cyclic_types:            0
% 7.73/1.49  sat_guarded_non_collapsed_types:        0
% 7.73/1.49  num_pure_diseq_elim:                    0
% 7.73/1.49  simp_replaced_by:                       0
% 7.73/1.49  res_preprocessed:                       285
% 7.73/1.49  prep_upred:                             0
% 7.73/1.49  prep_unflattend:                        0
% 7.73/1.49  smt_new_axioms:                         0
% 7.73/1.49  pred_elim_cands:                        8
% 7.73/1.49  pred_elim:                              0
% 7.73/1.49  pred_elim_cl:                           0
% 7.73/1.49  pred_elim_cycles:                       2
% 7.73/1.49  merged_defs:                            0
% 7.73/1.49  merged_defs_ncl:                        0
% 7.73/1.49  bin_hyper_res:                          0
% 7.73/1.49  prep_cycles:                            4
% 7.73/1.49  pred_elim_time:                         0.004
% 7.73/1.49  splitting_time:                         0.
% 7.73/1.49  sem_filter_time:                        0.
% 7.73/1.49  monotx_time:                            0.001
% 7.73/1.49  subtype_inf_time:                       0.
% 7.73/1.49  
% 7.73/1.49  ------ Problem properties
% 7.73/1.49  
% 7.73/1.49  clauses:                                61
% 7.73/1.49  conjectures:                            4
% 7.73/1.49  epr:                                    7
% 7.73/1.49  horn:                                   52
% 7.73/1.49  ground:                                 7
% 7.73/1.49  unary:                                  18
% 7.73/1.49  binary:                                 15
% 7.73/1.49  lits:                                   159
% 7.73/1.49  lits_eq:                                24
% 7.73/1.49  fd_pure:                                0
% 7.73/1.49  fd_pseudo:                              0
% 7.73/1.49  fd_cond:                                6
% 7.73/1.49  fd_pseudo_cond:                         1
% 7.73/1.49  ac_symbols:                             0
% 7.73/1.49  
% 7.73/1.49  ------ Propositional Solver
% 7.73/1.49  
% 7.73/1.49  prop_solver_calls:                      31
% 7.73/1.49  prop_fast_solver_calls:                 2258
% 7.73/1.49  smt_solver_calls:                       0
% 7.73/1.49  smt_fast_solver_calls:                  0
% 7.73/1.49  prop_num_of_clauses:                    11823
% 7.73/1.49  prop_preprocess_simplified:             25408
% 7.73/1.49  prop_fo_subsumed:                       53
% 7.73/1.49  prop_solver_time:                       0.
% 7.73/1.49  smt_solver_time:                        0.
% 7.73/1.49  smt_fast_solver_time:                   0.
% 7.73/1.49  prop_fast_solver_time:                  0.
% 7.73/1.49  prop_unsat_core_time:                   0.001
% 7.73/1.49  
% 7.73/1.49  ------ QBF
% 7.73/1.49  
% 7.73/1.49  qbf_q_res:                              0
% 7.73/1.49  qbf_num_tautologies:                    0
% 7.73/1.49  qbf_prep_cycles:                        0
% 7.73/1.49  
% 7.73/1.49  ------ BMC1
% 7.73/1.49  
% 7.73/1.49  bmc1_current_bound:                     -1
% 7.73/1.49  bmc1_last_solved_bound:                 -1
% 7.73/1.49  bmc1_unsat_core_size:                   -1
% 7.73/1.49  bmc1_unsat_core_parents_size:           -1
% 7.73/1.49  bmc1_merge_next_fun:                    0
% 7.73/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.73/1.49  
% 7.73/1.49  ------ Instantiation
% 7.73/1.49  
% 7.73/1.49  inst_num_of_clauses:                    3152
% 7.73/1.49  inst_num_in_passive:                    1011
% 7.73/1.49  inst_num_in_active:                     847
% 7.73/1.49  inst_num_in_unprocessed:                1294
% 7.73/1.49  inst_num_of_loops:                      980
% 7.73/1.49  inst_num_of_learning_restarts:          0
% 7.73/1.49  inst_num_moves_active_passive:          132
% 7.73/1.49  inst_lit_activity:                      0
% 7.73/1.49  inst_lit_activity_moves:                0
% 7.73/1.49  inst_num_tautologies:                   0
% 7.73/1.49  inst_num_prop_implied:                  0
% 7.73/1.49  inst_num_existing_simplified:           0
% 7.73/1.49  inst_num_eq_res_simplified:             0
% 7.73/1.49  inst_num_child_elim:                    0
% 7.73/1.49  inst_num_of_dismatching_blockings:      734
% 7.73/1.49  inst_num_of_non_proper_insts:           2090
% 7.73/1.49  inst_num_of_duplicates:                 0
% 7.73/1.49  inst_inst_num_from_inst_to_res:         0
% 7.73/1.49  inst_dismatching_checking_time:         0.
% 7.73/1.49  
% 7.73/1.49  ------ Resolution
% 7.73/1.49  
% 7.73/1.49  res_num_of_clauses:                     0
% 7.73/1.49  res_num_in_passive:                     0
% 7.73/1.49  res_num_in_active:                      0
% 7.73/1.49  res_num_of_loops:                       289
% 7.73/1.49  res_forward_subset_subsumed:            108
% 7.73/1.49  res_backward_subset_subsumed:           0
% 7.73/1.49  res_forward_subsumed:                   0
% 7.73/1.49  res_backward_subsumed:                  0
% 7.73/1.49  res_forward_subsumption_resolution:     0
% 7.73/1.49  res_backward_subsumption_resolution:    0
% 7.73/1.49  res_clause_to_clause_subsumption:       1584
% 7.73/1.49  res_orphan_elimination:                 0
% 7.73/1.49  res_tautology_del:                      66
% 7.73/1.49  res_num_eq_res_simplified:              0
% 7.73/1.49  res_num_sel_changes:                    0
% 7.73/1.49  res_moves_from_active_to_pass:          0
% 7.73/1.49  
% 7.73/1.49  ------ Superposition
% 7.73/1.49  
% 7.73/1.49  sup_time_total:                         0.
% 7.73/1.49  sup_time_generating:                    0.
% 7.73/1.49  sup_time_sim_full:                      0.
% 7.73/1.49  sup_time_sim_immed:                     0.
% 7.73/1.49  
% 7.73/1.49  sup_num_of_clauses:                     468
% 7.73/1.49  sup_num_in_active:                      121
% 7.73/1.49  sup_num_in_passive:                     347
% 7.73/1.49  sup_num_of_loops:                       195
% 7.73/1.49  sup_fw_superposition:                   298
% 7.73/1.49  sup_bw_superposition:                   268
% 7.73/1.49  sup_immediate_simplified:               111
% 7.73/1.49  sup_given_eliminated:                   2
% 7.73/1.49  comparisons_done:                       0
% 7.73/1.49  comparisons_avoided:                    3
% 7.73/1.49  
% 7.73/1.49  ------ Simplifications
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  sim_fw_subset_subsumed:                 26
% 7.73/1.49  sim_bw_subset_subsumed:                 5
% 7.73/1.49  sim_fw_subsumed:                        37
% 7.73/1.49  sim_bw_subsumed:                        30
% 7.73/1.49  sim_fw_subsumption_res:                 0
% 7.73/1.49  sim_bw_subsumption_res:                 0
% 7.73/1.49  sim_tautology_del:                      10
% 7.73/1.49  sim_eq_tautology_del:                   9
% 7.73/1.49  sim_eq_res_simp:                        0
% 7.73/1.49  sim_fw_demodulated:                     41
% 7.73/1.49  sim_bw_demodulated:                     47
% 7.73/1.49  sim_light_normalised:                   22
% 7.73/1.49  sim_joinable_taut:                      0
% 7.73/1.49  sim_joinable_simp:                      0
% 7.73/1.49  sim_ac_normalised:                      0
% 7.73/1.49  sim_smt_subsumption:                    0
% 7.73/1.49  
%------------------------------------------------------------------------------
