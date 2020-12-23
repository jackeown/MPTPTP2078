%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:02 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :  173 (1232 expanded)
%              Number of clauses        :  101 ( 397 expanded)
%              Number of leaves         :   18 ( 261 expanded)
%              Depth                    :   21
%              Number of atoms          :  641 (5588 expanded)
%              Number of equality atoms :  184 (1089 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f17,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f33,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f34,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f33])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK7
            | ~ r2_hidden(X5,X2)
            | ~ m1_subset_1(X5,X0) )
        & r2_hidden(sK7,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
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
              ( k1_funct_1(sK6,X5) != X4
              | ~ r2_hidden(X5,sK5)
              | ~ m1_subset_1(X5,sK3) )
          & r2_hidden(X4,k7_relset_1(sK3,sK4,sK6,sK5)) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ! [X5] :
        ( k1_funct_1(sK6,X5) != sK7
        | ~ r2_hidden(X5,sK5)
        | ~ m1_subset_1(X5,sK3) )
    & r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f34,f53,f52])).

fof(f83,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f84,plain,(
    r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
    inference(cnf_transformation,[],[f54])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X4,X3,X2,X1] :
      ( ? [X6] :
          ( r2_hidden(X6,X1)
          & r2_hidden(k4_tarski(X6,X4),X3)
          & m1_subset_1(X6,X2) )
     => ( r2_hidden(sK2(X1,X2,X3,X4),X1)
        & r2_hidden(k4_tarski(sK2(X1,X2,X3,X4),X4),X3)
        & m1_subset_1(sK2(X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
                        & ( ( r2_hidden(sK2(X1,X2,X3,X4),X1)
                            & r2_hidden(k4_tarski(sK2(X1,X2,X3,X4),X4),X3)
                            & m1_subset_1(sK2(X1,X2,X3,X4),X2) )
                          | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f49,f50])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK2(X1,X2,X3,X4),X4),X3)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
            & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f82,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f54])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f85,plain,(
    ! [X5] :
      ( k1_funct_1(sK6,X5) != sK7
      | ~ r2_hidden(X5,sK5)
      | ~ m1_subset_1(X5,sK3) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK2(X1,X2,X3,X4),X1)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK2(X1,X2,X3,X4),X2)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1358,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1365,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2585,plain,
    ( k7_relset_1(sK3,sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_1358,c_1365])).

cnf(c_28,negated_conjecture,
    ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1359,plain,
    ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2659,plain,
    ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2585,c_1359])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | r2_hidden(k4_tarski(sK2(X4,X3,X2,X0),X0),X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X4)
    | v1_xboole_0(X3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1362,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X4,X3,X2,X0),X0),X2) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X4) = iProver_top
    | v1_xboole_0(X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3048,plain,
    ( m1_subset_1(X0,sK4) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X1,sK3,sK6,X0),X0),sK6) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2585,c_1362])).

cnf(c_32,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1605,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1606,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1605])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1368,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_19,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_14,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_343,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_19,c_14])).

cnf(c_347,plain,
    ( ~ v1_funct_1(X0)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_343,c_18])).

cnf(c_348,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_347])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_392,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_348,c_30])).

cnf(c_393,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,k1_relat_1(sK6))
    | r2_hidden(k1_funct_1(sK6,X2),X1) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_1356,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(X2,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_393])).

cnf(c_1702,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1358,c_1356])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1378,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1804,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1702,c_1378])).

cnf(c_3303,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1368,c_1804])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1366,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3086,plain,
    ( m1_subset_1(k9_relat_1(sK6,X0),k1_zfmisc_1(sK4)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2585,c_1366])).

cnf(c_3398,plain,
    ( m1_subset_1(k9_relat_1(sK6,X0),k1_zfmisc_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3086,c_32])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1372,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3405,plain,
    ( m1_subset_1(X0,sK4) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3398,c_1372])).

cnf(c_3410,plain,
    ( v1_xboole_0(X1) = iProver_top
    | r2_hidden(k4_tarski(sK2(X1,sK3,sK6,X0),X0),sK6) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3048,c_32,c_1606,c_3303,c_3405])).

cnf(c_3411,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X1,sK3,sK6,X0),X0),sK6) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3410])).

cnf(c_16,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_437,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_30])).

cnf(c_438,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK6)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_1353,plain,
    ( k1_funct_1(sK6,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_438])).

cnf(c_439,plain,
    ( k1_funct_1(sK6,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_438])).

cnf(c_1630,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | k1_funct_1(sK6,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1353,c_32,c_439,c_1606])).

cnf(c_1631,plain,
    ( k1_funct_1(sK6,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_1630])).

cnf(c_3422,plain,
    ( k1_funct_1(sK6,sK2(X0,sK3,sK6,X1)) = X1
    | r2_hidden(X1,k9_relat_1(sK6,X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3411,c_1631])).

cnf(c_3543,plain,
    ( k1_funct_1(sK6,sK2(sK5,sK3,sK6,sK7)) = sK7
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2659,c_3422])).

cnf(c_20,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_371,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_20,c_9])).

cnf(c_375,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_371,c_18])).

cnf(c_376,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_375])).

cnf(c_1357,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_376])).

cnf(c_1790,plain,
    ( r1_tarski(k1_relat_1(sK6),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1358,c_1357])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1375,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2593,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1790,c_1375])).

cnf(c_3302,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK1(X0,X1,sK6),sK3) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1368,c_2593])).

cnf(c_7063,plain,
    ( r2_hidden(sK1(X0,X1,sK6),sK3) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3302,c_32,c_1606])).

cnf(c_7064,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK1(X0,X1,sK6),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_7063])).

cnf(c_7072,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7064,c_1378])).

cnf(c_7547,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2659,c_7072])).

cnf(c_7908,plain,
    ( k1_funct_1(sK6,sK2(sK5,sK3,sK6,sK7)) = sK7
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3543,c_7547])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1370,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK1(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3211,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1370,c_1378])).

cnf(c_6127,plain,
    ( v1_relat_1(sK6) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2659,c_3211])).

cnf(c_10580,plain,
    ( k1_funct_1(sK6,sK2(sK5,sK3,sK6,sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7908,c_32,c_1606,c_3543,c_6127,c_7547])).

cnf(c_27,negated_conjecture,
    ( ~ m1_subset_1(X0,sK3)
    | ~ r2_hidden(X0,sK5)
    | k1_funct_1(sK6,X0) != sK7 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1360,plain,
    ( k1_funct_1(sK6,X0) != sK7
    | m1_subset_1(X0,sK3) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_10590,plain,
    ( m1_subset_1(sK2(sK5,sK3,sK6,sK7),sK3) != iProver_top
    | r2_hidden(sK2(sK5,sK3,sK6,sK7),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_10580,c_1360])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | r2_hidden(sK2(X4,X3,X2,X0),X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X4)
    | v1_xboole_0(X3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1882,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK4)))
    | ~ m1_subset_1(sK7,sK4)
    | r2_hidden(sK2(X2,X1,X0,sK7),X2)
    | ~ r2_hidden(sK7,k7_relset_1(X1,sK4,X0,X2))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_3009,plain,
    ( ~ m1_subset_1(sK7,sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | r2_hidden(sK2(X0,sK3,sK6,sK7),X0)
    | ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1882])).

cnf(c_7664,plain,
    ( ~ m1_subset_1(sK7,sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | r2_hidden(sK2(sK5,sK3,sK6,sK7),sK5)
    | ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_3009])).

cnf(c_7665,plain,
    ( m1_subset_1(sK7,sK4) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | r2_hidden(sK2(sK5,sK3,sK6,sK7),sK5) = iProver_top
    | r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) != iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7664])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1369,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4129,plain,
    ( k1_funct_1(sK6,sK1(X0,X1,sK6)) = X0
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1369,c_1631])).

cnf(c_4408,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | k1_funct_1(sK6,sK1(X0,X1,sK6)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4129,c_32,c_1606])).

cnf(c_4409,plain,
    ( k1_funct_1(sK6,sK1(X0,X1,sK6)) = X0
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4408])).

cnf(c_4419,plain,
    ( k1_funct_1(sK6,sK1(sK7,sK5,sK6)) = sK7 ),
    inference(superposition,[status(thm)],[c_2659,c_4409])).

cnf(c_4448,plain,
    ( r2_hidden(sK1(sK7,sK5,sK6),k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK7,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4419,c_1702])).

cnf(c_4518,plain,
    ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
    | r2_hidden(sK7,sK4) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1368,c_4448])).

cnf(c_3179,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3795,plain,
    ( ~ r2_hidden(sK7,sK4)
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3179])).

cnf(c_3798,plain,
    ( r2_hidden(sK7,sK4) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3795])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | m1_subset_1(sK2(X4,X3,X2,X0),X3)
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | v1_xboole_0(X1)
    | v1_xboole_0(X4)
    | v1_xboole_0(X3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1361,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(sK2(X4,X3,X2,X0),X3) = iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X4) = iProver_top
    | v1_xboole_0(X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2423,plain,
    ( m1_subset_1(sK2(sK5,sK3,sK6,sK7),sK3) = iProver_top
    | m1_subset_1(sK7,sK4) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1359,c_1361])).

cnf(c_33,plain,
    ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1620,plain,
    ( ~ m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(X0))
    | m1_subset_1(sK7,X0)
    | ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1750,plain,
    ( ~ m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(sK4))
    | m1_subset_1(sK7,sK4)
    | ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_1620])).

cnf(c_1752,plain,
    ( m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(sK4)) != iProver_top
    | m1_subset_1(sK7,sK4) = iProver_top
    | r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1750])).

cnf(c_1638,plain,
    ( m1_subset_1(k7_relset_1(sK3,sK4,sK6,X0),k1_zfmisc_1(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1751,plain,
    ( m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_1638])).

cnf(c_1754,plain,
    ( m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(sK4)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1751])).

cnf(c_2764,plain,
    ( m1_subset_1(sK2(sK5,sK3,sK6,sK7),sK3) = iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2423,c_32,c_33,c_1752,c_1754])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10590,c_7665,c_7547,c_6127,c_4518,c_3798,c_2764,c_2659,c_1754,c_1752,c_1606,c_33,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n025.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 15:33:35 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.17/0.32  % Running in FOF mode
% 3.26/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/0.97  
% 3.26/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.26/0.97  
% 3.26/0.97  ------  iProver source info
% 3.26/0.97  
% 3.26/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.26/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.26/0.97  git: non_committed_changes: false
% 3.26/0.97  git: last_make_outside_of_git: false
% 3.26/0.97  
% 3.26/0.97  ------ 
% 3.26/0.97  
% 3.26/0.97  ------ Input Options
% 3.26/0.97  
% 3.26/0.97  --out_options                           all
% 3.26/0.97  --tptp_safe_out                         true
% 3.26/0.97  --problem_path                          ""
% 3.26/0.97  --include_path                          ""
% 3.26/0.97  --clausifier                            res/vclausify_rel
% 3.26/0.97  --clausifier_options                    --mode clausify
% 3.26/0.97  --stdin                                 false
% 3.26/0.97  --stats_out                             all
% 3.26/0.97  
% 3.26/0.97  ------ General Options
% 3.26/0.97  
% 3.26/0.97  --fof                                   false
% 3.26/0.97  --time_out_real                         305.
% 3.26/0.97  --time_out_virtual                      -1.
% 3.26/0.97  --symbol_type_check                     false
% 3.26/0.97  --clausify_out                          false
% 3.26/0.97  --sig_cnt_out                           false
% 3.26/0.97  --trig_cnt_out                          false
% 3.26/0.97  --trig_cnt_out_tolerance                1.
% 3.26/0.97  --trig_cnt_out_sk_spl                   false
% 3.26/0.97  --abstr_cl_out                          false
% 3.26/0.97  
% 3.26/0.97  ------ Global Options
% 3.26/0.97  
% 3.26/0.97  --schedule                              default
% 3.26/0.97  --add_important_lit                     false
% 3.26/0.97  --prop_solver_per_cl                    1000
% 3.26/0.97  --min_unsat_core                        false
% 3.26/0.97  --soft_assumptions                      false
% 3.26/0.97  --soft_lemma_size                       3
% 3.26/0.97  --prop_impl_unit_size                   0
% 3.26/0.97  --prop_impl_unit                        []
% 3.26/0.97  --share_sel_clauses                     true
% 3.26/0.97  --reset_solvers                         false
% 3.26/0.97  --bc_imp_inh                            [conj_cone]
% 3.26/0.97  --conj_cone_tolerance                   3.
% 3.26/0.97  --extra_neg_conj                        none
% 3.26/0.97  --large_theory_mode                     true
% 3.26/0.97  --prolific_symb_bound                   200
% 3.26/0.97  --lt_threshold                          2000
% 3.26/0.97  --clause_weak_htbl                      true
% 3.26/0.97  --gc_record_bc_elim                     false
% 3.26/0.97  
% 3.26/0.97  ------ Preprocessing Options
% 3.26/0.97  
% 3.26/0.97  --preprocessing_flag                    true
% 3.26/0.97  --time_out_prep_mult                    0.1
% 3.26/0.97  --splitting_mode                        input
% 3.26/0.97  --splitting_grd                         true
% 3.26/0.97  --splitting_cvd                         false
% 3.26/0.97  --splitting_cvd_svl                     false
% 3.26/0.97  --splitting_nvd                         32
% 3.26/0.97  --sub_typing                            true
% 3.26/0.97  --prep_gs_sim                           true
% 3.26/0.97  --prep_unflatten                        true
% 3.26/0.97  --prep_res_sim                          true
% 3.26/0.97  --prep_upred                            true
% 3.26/0.97  --prep_sem_filter                       exhaustive
% 3.26/0.97  --prep_sem_filter_out                   false
% 3.26/0.97  --pred_elim                             true
% 3.26/0.97  --res_sim_input                         true
% 3.26/0.97  --eq_ax_congr_red                       true
% 3.26/0.97  --pure_diseq_elim                       true
% 3.26/0.97  --brand_transform                       false
% 3.26/0.97  --non_eq_to_eq                          false
% 3.26/0.97  --prep_def_merge                        true
% 3.26/0.97  --prep_def_merge_prop_impl              false
% 3.26/0.97  --prep_def_merge_mbd                    true
% 3.26/0.97  --prep_def_merge_tr_red                 false
% 3.26/0.97  --prep_def_merge_tr_cl                  false
% 3.26/0.97  --smt_preprocessing                     true
% 3.26/0.97  --smt_ac_axioms                         fast
% 3.26/0.97  --preprocessed_out                      false
% 3.26/0.97  --preprocessed_stats                    false
% 3.26/0.97  
% 3.26/0.97  ------ Abstraction refinement Options
% 3.26/0.97  
% 3.26/0.97  --abstr_ref                             []
% 3.26/0.97  --abstr_ref_prep                        false
% 3.26/0.97  --abstr_ref_until_sat                   false
% 3.26/0.97  --abstr_ref_sig_restrict                funpre
% 3.26/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.26/0.97  --abstr_ref_under                       []
% 3.26/0.97  
% 3.26/0.97  ------ SAT Options
% 3.26/0.97  
% 3.26/0.97  --sat_mode                              false
% 3.26/0.97  --sat_fm_restart_options                ""
% 3.26/0.97  --sat_gr_def                            false
% 3.26/0.97  --sat_epr_types                         true
% 3.26/0.97  --sat_non_cyclic_types                  false
% 3.26/0.97  --sat_finite_models                     false
% 3.26/0.97  --sat_fm_lemmas                         false
% 3.26/0.97  --sat_fm_prep                           false
% 3.26/0.97  --sat_fm_uc_incr                        true
% 3.26/0.97  --sat_out_model                         small
% 3.26/0.97  --sat_out_clauses                       false
% 3.26/0.97  
% 3.26/0.97  ------ QBF Options
% 3.26/0.97  
% 3.26/0.97  --qbf_mode                              false
% 3.26/0.97  --qbf_elim_univ                         false
% 3.26/0.97  --qbf_dom_inst                          none
% 3.26/0.97  --qbf_dom_pre_inst                      false
% 3.26/0.97  --qbf_sk_in                             false
% 3.26/0.97  --qbf_pred_elim                         true
% 3.26/0.97  --qbf_split                             512
% 3.26/0.97  
% 3.26/0.97  ------ BMC1 Options
% 3.26/0.97  
% 3.26/0.97  --bmc1_incremental                      false
% 3.26/0.97  --bmc1_axioms                           reachable_all
% 3.26/0.97  --bmc1_min_bound                        0
% 3.26/0.97  --bmc1_max_bound                        -1
% 3.26/0.97  --bmc1_max_bound_default                -1
% 3.26/0.97  --bmc1_symbol_reachability              true
% 3.26/0.97  --bmc1_property_lemmas                  false
% 3.26/0.97  --bmc1_k_induction                      false
% 3.26/0.97  --bmc1_non_equiv_states                 false
% 3.26/0.97  --bmc1_deadlock                         false
% 3.26/0.97  --bmc1_ucm                              false
% 3.26/0.97  --bmc1_add_unsat_core                   none
% 3.26/0.97  --bmc1_unsat_core_children              false
% 3.26/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.26/0.97  --bmc1_out_stat                         full
% 3.26/0.97  --bmc1_ground_init                      false
% 3.26/0.97  --bmc1_pre_inst_next_state              false
% 3.26/0.97  --bmc1_pre_inst_state                   false
% 3.26/0.97  --bmc1_pre_inst_reach_state             false
% 3.26/0.97  --bmc1_out_unsat_core                   false
% 3.26/0.97  --bmc1_aig_witness_out                  false
% 3.26/0.97  --bmc1_verbose                          false
% 3.26/0.97  --bmc1_dump_clauses_tptp                false
% 3.26/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.26/0.97  --bmc1_dump_file                        -
% 3.26/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.26/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.26/0.97  --bmc1_ucm_extend_mode                  1
% 3.26/0.97  --bmc1_ucm_init_mode                    2
% 3.26/0.97  --bmc1_ucm_cone_mode                    none
% 3.26/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.26/0.97  --bmc1_ucm_relax_model                  4
% 3.26/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.26/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.26/0.97  --bmc1_ucm_layered_model                none
% 3.26/0.97  --bmc1_ucm_max_lemma_size               10
% 3.26/0.97  
% 3.26/0.97  ------ AIG Options
% 3.26/0.97  
% 3.26/0.97  --aig_mode                              false
% 3.26/0.97  
% 3.26/0.97  ------ Instantiation Options
% 3.26/0.97  
% 3.26/0.97  --instantiation_flag                    true
% 3.26/0.97  --inst_sos_flag                         false
% 3.26/0.97  --inst_sos_phase                        true
% 3.26/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.26/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.26/0.97  --inst_lit_sel_side                     num_symb
% 3.26/0.97  --inst_solver_per_active                1400
% 3.26/0.97  --inst_solver_calls_frac                1.
% 3.26/0.97  --inst_passive_queue_type               priority_queues
% 3.26/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.26/0.97  --inst_passive_queues_freq              [25;2]
% 3.26/0.97  --inst_dismatching                      true
% 3.26/0.97  --inst_eager_unprocessed_to_passive     true
% 3.26/0.97  --inst_prop_sim_given                   true
% 3.26/0.97  --inst_prop_sim_new                     false
% 3.26/0.97  --inst_subs_new                         false
% 3.26/0.97  --inst_eq_res_simp                      false
% 3.26/0.97  --inst_subs_given                       false
% 3.26/0.97  --inst_orphan_elimination               true
% 3.26/0.97  --inst_learning_loop_flag               true
% 3.26/0.97  --inst_learning_start                   3000
% 3.26/0.97  --inst_learning_factor                  2
% 3.26/0.97  --inst_start_prop_sim_after_learn       3
% 3.26/0.97  --inst_sel_renew                        solver
% 3.26/0.97  --inst_lit_activity_flag                true
% 3.26/0.97  --inst_restr_to_given                   false
% 3.26/0.97  --inst_activity_threshold               500
% 3.26/0.97  --inst_out_proof                        true
% 3.26/0.97  
% 3.26/0.97  ------ Resolution Options
% 3.26/0.97  
% 3.26/0.97  --resolution_flag                       true
% 3.26/0.97  --res_lit_sel                           adaptive
% 3.26/0.97  --res_lit_sel_side                      none
% 3.26/0.97  --res_ordering                          kbo
% 3.26/0.97  --res_to_prop_solver                    active
% 3.26/0.97  --res_prop_simpl_new                    false
% 3.26/0.97  --res_prop_simpl_given                  true
% 3.26/0.97  --res_passive_queue_type                priority_queues
% 3.26/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.26/0.97  --res_passive_queues_freq               [15;5]
% 3.26/0.97  --res_forward_subs                      full
% 3.26/0.97  --res_backward_subs                     full
% 3.26/0.97  --res_forward_subs_resolution           true
% 3.26/0.97  --res_backward_subs_resolution          true
% 3.26/0.97  --res_orphan_elimination                true
% 3.26/0.97  --res_time_limit                        2.
% 3.26/0.97  --res_out_proof                         true
% 3.26/0.97  
% 3.26/0.97  ------ Superposition Options
% 3.26/0.97  
% 3.26/0.97  --superposition_flag                    true
% 3.26/0.97  --sup_passive_queue_type                priority_queues
% 3.26/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.26/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.26/0.97  --demod_completeness_check              fast
% 3.26/0.97  --demod_use_ground                      true
% 3.26/0.97  --sup_to_prop_solver                    passive
% 3.26/0.97  --sup_prop_simpl_new                    true
% 3.26/0.97  --sup_prop_simpl_given                  true
% 3.26/0.97  --sup_fun_splitting                     false
% 3.26/0.97  --sup_smt_interval                      50000
% 3.26/0.97  
% 3.26/0.97  ------ Superposition Simplification Setup
% 3.26/0.97  
% 3.26/0.97  --sup_indices_passive                   []
% 3.26/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.26/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.97  --sup_full_bw                           [BwDemod]
% 3.26/0.97  --sup_immed_triv                        [TrivRules]
% 3.26/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.26/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.97  --sup_immed_bw_main                     []
% 3.26/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.26/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.97  
% 3.26/0.97  ------ Combination Options
% 3.26/0.97  
% 3.26/0.97  --comb_res_mult                         3
% 3.26/0.97  --comb_sup_mult                         2
% 3.26/0.97  --comb_inst_mult                        10
% 3.26/0.97  
% 3.26/0.97  ------ Debug Options
% 3.26/0.97  
% 3.26/0.97  --dbg_backtrace                         false
% 3.26/0.97  --dbg_dump_prop_clauses                 false
% 3.26/0.97  --dbg_dump_prop_clauses_file            -
% 3.26/0.97  --dbg_out_stat                          false
% 3.26/0.97  ------ Parsing...
% 3.26/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.26/0.97  
% 3.26/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.26/0.97  
% 3.26/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.26/0.97  
% 3.26/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.26/0.97  ------ Proving...
% 3.26/0.97  ------ Problem Properties 
% 3.26/0.97  
% 3.26/0.97  
% 3.26/0.97  clauses                                 26
% 3.26/0.97  conjectures                             3
% 3.26/0.97  EPR                                     4
% 3.26/0.97  Horn                                    21
% 3.26/0.97  unary                                   3
% 3.26/0.97  binary                                  7
% 3.26/0.97  lits                                    85
% 3.26/0.97  lits eq                                 4
% 3.26/0.97  fd_pure                                 0
% 3.26/0.97  fd_pseudo                               0
% 3.26/0.97  fd_cond                                 0
% 3.26/0.97  fd_pseudo_cond                          2
% 3.26/0.97  AC symbols                              0
% 3.26/0.97  
% 3.26/0.97  ------ Schedule dynamic 5 is on 
% 3.26/0.97  
% 3.26/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.26/0.97  
% 3.26/0.97  
% 3.26/0.97  ------ 
% 3.26/0.97  Current options:
% 3.26/0.97  ------ 
% 3.26/0.97  
% 3.26/0.97  ------ Input Options
% 3.26/0.97  
% 3.26/0.97  --out_options                           all
% 3.26/0.97  --tptp_safe_out                         true
% 3.26/0.97  --problem_path                          ""
% 3.26/0.97  --include_path                          ""
% 3.26/0.97  --clausifier                            res/vclausify_rel
% 3.26/0.97  --clausifier_options                    --mode clausify
% 3.26/0.97  --stdin                                 false
% 3.26/0.97  --stats_out                             all
% 3.26/0.97  
% 3.26/0.97  ------ General Options
% 3.26/0.97  
% 3.26/0.97  --fof                                   false
% 3.26/0.97  --time_out_real                         305.
% 3.26/0.97  --time_out_virtual                      -1.
% 3.26/0.97  --symbol_type_check                     false
% 3.26/0.97  --clausify_out                          false
% 3.26/0.97  --sig_cnt_out                           false
% 3.26/0.97  --trig_cnt_out                          false
% 3.26/0.97  --trig_cnt_out_tolerance                1.
% 3.26/0.97  --trig_cnt_out_sk_spl                   false
% 3.26/0.97  --abstr_cl_out                          false
% 3.26/0.97  
% 3.26/0.97  ------ Global Options
% 3.26/0.97  
% 3.26/0.97  --schedule                              default
% 3.26/0.97  --add_important_lit                     false
% 3.26/0.97  --prop_solver_per_cl                    1000
% 3.26/0.97  --min_unsat_core                        false
% 3.26/0.97  --soft_assumptions                      false
% 3.26/0.97  --soft_lemma_size                       3
% 3.26/0.97  --prop_impl_unit_size                   0
% 3.26/0.97  --prop_impl_unit                        []
% 3.26/0.97  --share_sel_clauses                     true
% 3.26/0.97  --reset_solvers                         false
% 3.26/0.97  --bc_imp_inh                            [conj_cone]
% 3.26/0.97  --conj_cone_tolerance                   3.
% 3.26/0.97  --extra_neg_conj                        none
% 3.26/0.97  --large_theory_mode                     true
% 3.26/0.97  --prolific_symb_bound                   200
% 3.26/0.97  --lt_threshold                          2000
% 3.26/0.97  --clause_weak_htbl                      true
% 3.26/0.97  --gc_record_bc_elim                     false
% 3.26/0.97  
% 3.26/0.97  ------ Preprocessing Options
% 3.26/0.97  
% 3.26/0.97  --preprocessing_flag                    true
% 3.26/0.97  --time_out_prep_mult                    0.1
% 3.26/0.97  --splitting_mode                        input
% 3.26/0.97  --splitting_grd                         true
% 3.26/0.97  --splitting_cvd                         false
% 3.26/0.97  --splitting_cvd_svl                     false
% 3.26/0.97  --splitting_nvd                         32
% 3.26/0.97  --sub_typing                            true
% 3.26/0.97  --prep_gs_sim                           true
% 3.26/0.97  --prep_unflatten                        true
% 3.26/0.97  --prep_res_sim                          true
% 3.26/0.97  --prep_upred                            true
% 3.26/0.97  --prep_sem_filter                       exhaustive
% 3.26/0.97  --prep_sem_filter_out                   false
% 3.26/0.97  --pred_elim                             true
% 3.26/0.97  --res_sim_input                         true
% 3.26/0.97  --eq_ax_congr_red                       true
% 3.26/0.97  --pure_diseq_elim                       true
% 3.26/0.97  --brand_transform                       false
% 3.26/0.97  --non_eq_to_eq                          false
% 3.26/0.97  --prep_def_merge                        true
% 3.26/0.97  --prep_def_merge_prop_impl              false
% 3.26/0.97  --prep_def_merge_mbd                    true
% 3.26/0.97  --prep_def_merge_tr_red                 false
% 3.26/0.97  --prep_def_merge_tr_cl                  false
% 3.26/0.97  --smt_preprocessing                     true
% 3.26/0.97  --smt_ac_axioms                         fast
% 3.26/0.97  --preprocessed_out                      false
% 3.26/0.97  --preprocessed_stats                    false
% 3.26/0.97  
% 3.26/0.97  ------ Abstraction refinement Options
% 3.26/0.97  
% 3.26/0.97  --abstr_ref                             []
% 3.26/0.97  --abstr_ref_prep                        false
% 3.26/0.97  --abstr_ref_until_sat                   false
% 3.26/0.97  --abstr_ref_sig_restrict                funpre
% 3.26/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.26/0.97  --abstr_ref_under                       []
% 3.26/0.97  
% 3.26/0.97  ------ SAT Options
% 3.26/0.97  
% 3.26/0.97  --sat_mode                              false
% 3.26/0.97  --sat_fm_restart_options                ""
% 3.26/0.97  --sat_gr_def                            false
% 3.26/0.97  --sat_epr_types                         true
% 3.26/0.97  --sat_non_cyclic_types                  false
% 3.26/0.97  --sat_finite_models                     false
% 3.26/0.97  --sat_fm_lemmas                         false
% 3.26/0.97  --sat_fm_prep                           false
% 3.26/0.97  --sat_fm_uc_incr                        true
% 3.26/0.97  --sat_out_model                         small
% 3.26/0.97  --sat_out_clauses                       false
% 3.26/0.97  
% 3.26/0.97  ------ QBF Options
% 3.26/0.97  
% 3.26/0.97  --qbf_mode                              false
% 3.26/0.97  --qbf_elim_univ                         false
% 3.26/0.97  --qbf_dom_inst                          none
% 3.26/0.97  --qbf_dom_pre_inst                      false
% 3.26/0.97  --qbf_sk_in                             false
% 3.26/0.97  --qbf_pred_elim                         true
% 3.26/0.97  --qbf_split                             512
% 3.26/0.97  
% 3.26/0.97  ------ BMC1 Options
% 3.26/0.97  
% 3.26/0.97  --bmc1_incremental                      false
% 3.26/0.97  --bmc1_axioms                           reachable_all
% 3.26/0.97  --bmc1_min_bound                        0
% 3.26/0.97  --bmc1_max_bound                        -1
% 3.26/0.97  --bmc1_max_bound_default                -1
% 3.26/0.97  --bmc1_symbol_reachability              true
% 3.26/0.97  --bmc1_property_lemmas                  false
% 3.26/0.97  --bmc1_k_induction                      false
% 3.26/0.97  --bmc1_non_equiv_states                 false
% 3.26/0.97  --bmc1_deadlock                         false
% 3.26/0.97  --bmc1_ucm                              false
% 3.26/0.97  --bmc1_add_unsat_core                   none
% 3.26/0.97  --bmc1_unsat_core_children              false
% 3.26/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.26/0.97  --bmc1_out_stat                         full
% 3.26/0.97  --bmc1_ground_init                      false
% 3.26/0.97  --bmc1_pre_inst_next_state              false
% 3.26/0.97  --bmc1_pre_inst_state                   false
% 3.26/0.97  --bmc1_pre_inst_reach_state             false
% 3.26/0.97  --bmc1_out_unsat_core                   false
% 3.26/0.97  --bmc1_aig_witness_out                  false
% 3.26/0.97  --bmc1_verbose                          false
% 3.26/0.97  --bmc1_dump_clauses_tptp                false
% 3.26/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.26/0.97  --bmc1_dump_file                        -
% 3.26/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.26/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.26/0.97  --bmc1_ucm_extend_mode                  1
% 3.26/0.97  --bmc1_ucm_init_mode                    2
% 3.26/0.97  --bmc1_ucm_cone_mode                    none
% 3.26/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.26/0.97  --bmc1_ucm_relax_model                  4
% 3.26/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.26/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.26/0.97  --bmc1_ucm_layered_model                none
% 3.26/0.97  --bmc1_ucm_max_lemma_size               10
% 3.26/0.97  
% 3.26/0.97  ------ AIG Options
% 3.26/0.97  
% 3.26/0.97  --aig_mode                              false
% 3.26/0.97  
% 3.26/0.97  ------ Instantiation Options
% 3.26/0.97  
% 3.26/0.97  --instantiation_flag                    true
% 3.26/0.97  --inst_sos_flag                         false
% 3.26/0.97  --inst_sos_phase                        true
% 3.26/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.26/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.26/0.97  --inst_lit_sel_side                     none
% 3.26/0.97  --inst_solver_per_active                1400
% 3.26/0.97  --inst_solver_calls_frac                1.
% 3.26/0.97  --inst_passive_queue_type               priority_queues
% 3.26/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.26/0.97  --inst_passive_queues_freq              [25;2]
% 3.26/0.97  --inst_dismatching                      true
% 3.26/0.97  --inst_eager_unprocessed_to_passive     true
% 3.26/0.97  --inst_prop_sim_given                   true
% 3.26/0.97  --inst_prop_sim_new                     false
% 3.26/0.97  --inst_subs_new                         false
% 3.26/0.97  --inst_eq_res_simp                      false
% 3.26/0.97  --inst_subs_given                       false
% 3.26/0.97  --inst_orphan_elimination               true
% 3.26/0.97  --inst_learning_loop_flag               true
% 3.26/0.97  --inst_learning_start                   3000
% 3.26/0.97  --inst_learning_factor                  2
% 3.26/0.97  --inst_start_prop_sim_after_learn       3
% 3.26/0.97  --inst_sel_renew                        solver
% 3.26/0.97  --inst_lit_activity_flag                true
% 3.26/0.97  --inst_restr_to_given                   false
% 3.26/0.97  --inst_activity_threshold               500
% 3.26/0.97  --inst_out_proof                        true
% 3.26/0.97  
% 3.26/0.97  ------ Resolution Options
% 3.26/0.97  
% 3.26/0.97  --resolution_flag                       false
% 3.26/0.97  --res_lit_sel                           adaptive
% 3.26/0.97  --res_lit_sel_side                      none
% 3.26/0.97  --res_ordering                          kbo
% 3.26/0.97  --res_to_prop_solver                    active
% 3.26/0.97  --res_prop_simpl_new                    false
% 3.26/0.97  --res_prop_simpl_given                  true
% 3.26/0.97  --res_passive_queue_type                priority_queues
% 3.26/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.26/0.97  --res_passive_queues_freq               [15;5]
% 3.26/0.97  --res_forward_subs                      full
% 3.26/0.97  --res_backward_subs                     full
% 3.26/0.97  --res_forward_subs_resolution           true
% 3.26/0.97  --res_backward_subs_resolution          true
% 3.26/0.97  --res_orphan_elimination                true
% 3.26/0.97  --res_time_limit                        2.
% 3.26/0.97  --res_out_proof                         true
% 3.26/0.97  
% 3.26/0.97  ------ Superposition Options
% 3.26/0.97  
% 3.26/0.97  --superposition_flag                    true
% 3.26/0.97  --sup_passive_queue_type                priority_queues
% 3.26/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.26/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.26/0.97  --demod_completeness_check              fast
% 3.26/0.97  --demod_use_ground                      true
% 3.26/0.97  --sup_to_prop_solver                    passive
% 3.26/0.97  --sup_prop_simpl_new                    true
% 3.26/0.97  --sup_prop_simpl_given                  true
% 3.26/0.97  --sup_fun_splitting                     false
% 3.26/0.97  --sup_smt_interval                      50000
% 3.26/0.97  
% 3.26/0.97  ------ Superposition Simplification Setup
% 3.26/0.97  
% 3.26/0.97  --sup_indices_passive                   []
% 3.26/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.26/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.97  --sup_full_bw                           [BwDemod]
% 3.26/0.97  --sup_immed_triv                        [TrivRules]
% 3.26/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.26/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.97  --sup_immed_bw_main                     []
% 3.26/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.26/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.97  
% 3.26/0.97  ------ Combination Options
% 3.26/0.97  
% 3.26/0.97  --comb_res_mult                         3
% 3.26/0.97  --comb_sup_mult                         2
% 3.26/0.97  --comb_inst_mult                        10
% 3.26/0.97  
% 3.26/0.97  ------ Debug Options
% 3.26/0.97  
% 3.26/0.97  --dbg_backtrace                         false
% 3.26/0.97  --dbg_dump_prop_clauses                 false
% 3.26/0.97  --dbg_dump_prop_clauses_file            -
% 3.26/0.97  --dbg_out_stat                          false
% 3.26/0.97  
% 3.26/0.97  
% 3.26/0.97  
% 3.26/0.97  
% 3.26/0.97  ------ Proving...
% 3.26/0.97  
% 3.26/0.97  
% 3.26/0.97  % SZS status Theorem for theBenchmark.p
% 3.26/0.97  
% 3.26/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.26/0.97  
% 3.26/0.97  fof(f14,conjecture,(
% 3.26/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.26/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/0.97  
% 3.26/0.97  fof(f15,negated_conjecture,(
% 3.26/0.97    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.26/0.97    inference(negated_conjecture,[],[f14])).
% 3.26/0.97  
% 3.26/0.97  fof(f17,plain,(
% 3.26/0.97    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.26/0.97    inference(pure_predicate_removal,[],[f15])).
% 3.26/0.97  
% 3.26/0.97  fof(f33,plain,(
% 3.26/0.97    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 3.26/0.97    inference(ennf_transformation,[],[f17])).
% 3.26/0.97  
% 3.26/0.97  fof(f34,plain,(
% 3.26/0.97    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 3.26/0.97    inference(flattening,[],[f33])).
% 3.26/0.97  
% 3.26/0.97  fof(f53,plain,(
% 3.26/0.97    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK7 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(sK7,k7_relset_1(X0,X1,X3,X2)))) )),
% 3.26/0.97    introduced(choice_axiom,[])).
% 3.26/0.97  
% 3.26/0.97  fof(f52,plain,(
% 3.26/0.97    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK6,X5) != X4 | ~r2_hidden(X5,sK5) | ~m1_subset_1(X5,sK3)) & r2_hidden(X4,k7_relset_1(sK3,sK4,sK6,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK6))),
% 3.26/0.97    introduced(choice_axiom,[])).
% 3.26/0.97  
% 3.26/0.97  fof(f54,plain,(
% 3.26/0.97    (! [X5] : (k1_funct_1(sK6,X5) != sK7 | ~r2_hidden(X5,sK5) | ~m1_subset_1(X5,sK3)) & r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK6)),
% 3.26/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f34,f53,f52])).
% 3.26/0.97  
% 3.26/0.97  fof(f83,plain,(
% 3.26/0.97    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.26/0.97    inference(cnf_transformation,[],[f54])).
% 3.26/0.97  
% 3.26/0.97  fof(f12,axiom,(
% 3.26/0.97    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.26/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/0.97  
% 3.26/0.97  fof(f31,plain,(
% 3.26/0.97    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.26/0.97    inference(ennf_transformation,[],[f12])).
% 3.26/0.97  
% 3.26/0.97  fof(f77,plain,(
% 3.26/0.97    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.26/0.97    inference(cnf_transformation,[],[f31])).
% 3.26/0.97  
% 3.26/0.97  fof(f84,plain,(
% 3.26/0.97    r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))),
% 3.26/0.97    inference(cnf_transformation,[],[f54])).
% 3.26/0.97  
% 3.26/0.97  fof(f13,axiom,(
% 3.26/0.97    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 3.26/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/0.97  
% 3.26/0.97  fof(f32,plain,(
% 3.26/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.26/0.97    inference(ennf_transformation,[],[f13])).
% 3.26/0.97  
% 3.26/0.97  fof(f48,plain,(
% 3.26/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.26/0.97    inference(nnf_transformation,[],[f32])).
% 3.26/0.97  
% 3.26/0.97  fof(f49,plain,(
% 3.26/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.26/0.97    inference(rectify,[],[f48])).
% 3.26/0.97  
% 3.26/0.97  fof(f50,plain,(
% 3.26/0.97    ! [X4,X3,X2,X1] : (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) => (r2_hidden(sK2(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK2(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK2(X1,X2,X3,X4),X2)))),
% 3.26/0.97    introduced(choice_axiom,[])).
% 3.26/0.97  
% 3.26/0.97  fof(f51,plain,(
% 3.26/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & ((r2_hidden(sK2(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK2(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK2(X1,X2,X3,X4),X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.26/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f49,f50])).
% 3.26/0.97  
% 3.26/0.97  fof(f79,plain,(
% 3.26/0.97    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK2(X1,X2,X3,X4),X4),X3) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.26/0.97    inference(cnf_transformation,[],[f51])).
% 3.26/0.97  
% 3.26/0.97  fof(f9,axiom,(
% 3.26/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.26/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/0.97  
% 3.26/0.97  fof(f28,plain,(
% 3.26/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.26/0.97    inference(ennf_transformation,[],[f9])).
% 3.26/0.97  
% 3.26/0.97  fof(f73,plain,(
% 3.26/0.97    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.26/0.97    inference(cnf_transformation,[],[f28])).
% 3.26/0.97  
% 3.26/0.97  fof(f6,axiom,(
% 3.26/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.26/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/0.97  
% 3.26/0.97  fof(f23,plain,(
% 3.26/0.97    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.26/0.97    inference(ennf_transformation,[],[f6])).
% 3.26/0.97  
% 3.26/0.97  fof(f42,plain,(
% 3.26/0.97    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.26/0.97    inference(nnf_transformation,[],[f23])).
% 3.26/0.97  
% 3.26/0.97  fof(f43,plain,(
% 3.26/0.97    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.26/0.97    inference(rectify,[],[f42])).
% 3.26/0.97  
% 3.26/0.97  fof(f44,plain,(
% 3.26/0.97    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 3.26/0.97    introduced(choice_axiom,[])).
% 3.26/0.97  
% 3.26/0.97  fof(f45,plain,(
% 3.26/0.97    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.26/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).
% 3.26/0.97  
% 3.26/0.97  fof(f65,plain,(
% 3.26/0.97    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.26/0.97    inference(cnf_transformation,[],[f45])).
% 3.26/0.97  
% 3.26/0.97  fof(f10,axiom,(
% 3.26/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.26/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/0.97  
% 3.26/0.97  fof(f29,plain,(
% 3.26/0.97    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.26/0.97    inference(ennf_transformation,[],[f10])).
% 3.26/0.97  
% 3.26/0.97  fof(f75,plain,(
% 3.26/0.97    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.26/0.97    inference(cnf_transformation,[],[f29])).
% 3.26/0.97  
% 3.26/0.97  fof(f7,axiom,(
% 3.26/0.97    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 3.26/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/0.97  
% 3.26/0.97  fof(f24,plain,(
% 3.26/0.97    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.26/0.97    inference(ennf_transformation,[],[f7])).
% 3.26/0.97  
% 3.26/0.97  fof(f25,plain,(
% 3.26/0.97    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.26/0.97    inference(flattening,[],[f24])).
% 3.26/0.97  
% 3.26/0.97  fof(f69,plain,(
% 3.26/0.97    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.26/0.97    inference(cnf_transformation,[],[f25])).
% 3.26/0.97  
% 3.26/0.97  fof(f82,plain,(
% 3.26/0.97    v1_funct_1(sK6)),
% 3.26/0.97    inference(cnf_transformation,[],[f54])).
% 3.26/0.97  
% 3.26/0.97  fof(f1,axiom,(
% 3.26/0.97    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.26/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/0.97  
% 3.26/0.97  fof(f16,plain,(
% 3.26/0.97    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 3.26/0.97    inference(unused_predicate_definition_removal,[],[f1])).
% 3.26/0.97  
% 3.26/0.97  fof(f18,plain,(
% 3.26/0.97    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 3.26/0.97    inference(ennf_transformation,[],[f16])).
% 3.26/0.97  
% 3.26/0.97  fof(f55,plain,(
% 3.26/0.97    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.26/0.97    inference(cnf_transformation,[],[f18])).
% 3.26/0.97  
% 3.26/0.97  fof(f11,axiom,(
% 3.26/0.97    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 3.26/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/0.97  
% 3.26/0.97  fof(f30,plain,(
% 3.26/0.97    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.26/0.97    inference(ennf_transformation,[],[f11])).
% 3.26/0.97  
% 3.26/0.97  fof(f76,plain,(
% 3.26/0.97    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.26/0.97    inference(cnf_transformation,[],[f30])).
% 3.26/0.97  
% 3.26/0.97  fof(f4,axiom,(
% 3.26/0.97    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.26/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/0.97  
% 3.26/0.97  fof(f20,plain,(
% 3.26/0.97    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.26/0.97    inference(ennf_transformation,[],[f4])).
% 3.26/0.97  
% 3.26/0.97  fof(f21,plain,(
% 3.26/0.97    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.26/0.97    inference(flattening,[],[f20])).
% 3.26/0.97  
% 3.26/0.97  fof(f62,plain,(
% 3.26/0.97    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.26/0.97    inference(cnf_transformation,[],[f21])).
% 3.26/0.97  
% 3.26/0.97  fof(f8,axiom,(
% 3.26/0.97    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.26/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/0.97  
% 3.26/0.97  fof(f26,plain,(
% 3.26/0.97    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.26/0.97    inference(ennf_transformation,[],[f8])).
% 3.26/0.97  
% 3.26/0.97  fof(f27,plain,(
% 3.26/0.97    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.26/0.97    inference(flattening,[],[f26])).
% 3.26/0.97  
% 3.26/0.97  fof(f46,plain,(
% 3.26/0.97    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.26/0.97    inference(nnf_transformation,[],[f27])).
% 3.26/0.97  
% 3.26/0.97  fof(f47,plain,(
% 3.26/0.97    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.26/0.97    inference(flattening,[],[f46])).
% 3.26/0.97  
% 3.26/0.97  fof(f71,plain,(
% 3.26/0.97    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.26/0.97    inference(cnf_transformation,[],[f47])).
% 3.26/0.97  
% 3.26/0.97  fof(f74,plain,(
% 3.26/0.97    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.26/0.97    inference(cnf_transformation,[],[f29])).
% 3.26/0.97  
% 3.26/0.97  fof(f5,axiom,(
% 3.26/0.97    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.26/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/0.97  
% 3.26/0.97  fof(f22,plain,(
% 3.26/0.97    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.26/0.97    inference(ennf_transformation,[],[f5])).
% 3.26/0.97  
% 3.26/0.97  fof(f41,plain,(
% 3.26/0.97    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.26/0.97    inference(nnf_transformation,[],[f22])).
% 3.26/0.97  
% 3.26/0.97  fof(f63,plain,(
% 3.26/0.97    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.26/0.97    inference(cnf_transformation,[],[f41])).
% 3.26/0.97  
% 3.26/0.97  fof(f2,axiom,(
% 3.26/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.26/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/0.97  
% 3.26/0.97  fof(f19,plain,(
% 3.26/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.26/0.97    inference(ennf_transformation,[],[f2])).
% 3.26/0.97  
% 3.26/0.97  fof(f35,plain,(
% 3.26/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.26/0.97    inference(nnf_transformation,[],[f19])).
% 3.26/0.97  
% 3.26/0.97  fof(f36,plain,(
% 3.26/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.26/0.97    inference(rectify,[],[f35])).
% 3.26/0.97  
% 3.26/0.97  fof(f37,plain,(
% 3.26/0.97    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.26/0.97    introduced(choice_axiom,[])).
% 3.26/0.97  
% 3.26/0.97  fof(f38,plain,(
% 3.26/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.26/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 3.26/0.97  
% 3.26/0.97  fof(f56,plain,(
% 3.26/0.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.26/0.97    inference(cnf_transformation,[],[f38])).
% 3.26/0.97  
% 3.26/0.97  fof(f67,plain,(
% 3.26/0.97    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.26/0.97    inference(cnf_transformation,[],[f45])).
% 3.26/0.97  
% 3.26/0.97  fof(f85,plain,(
% 3.26/0.97    ( ! [X5] : (k1_funct_1(sK6,X5) != sK7 | ~r2_hidden(X5,sK5) | ~m1_subset_1(X5,sK3)) )),
% 3.26/0.97    inference(cnf_transformation,[],[f54])).
% 3.26/0.97  
% 3.26/0.97  fof(f80,plain,(
% 3.26/0.97    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK2(X1,X2,X3,X4),X1) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.26/0.97    inference(cnf_transformation,[],[f51])).
% 3.26/0.97  
% 3.26/0.97  fof(f66,plain,(
% 3.26/0.97    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.26/0.97    inference(cnf_transformation,[],[f45])).
% 3.26/0.97  
% 3.26/0.97  fof(f78,plain,(
% 3.26/0.97    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK2(X1,X2,X3,X4),X2) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.26/0.97    inference(cnf_transformation,[],[f51])).
% 3.26/0.97  
% 3.26/0.97  cnf(c_29,negated_conjecture,
% 3.26/0.97      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.26/0.97      inference(cnf_transformation,[],[f83]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_1358,plain,
% 3.26/0.97      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.26/0.97      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_22,plain,
% 3.26/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.97      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.26/0.97      inference(cnf_transformation,[],[f77]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_1365,plain,
% 3.26/0.97      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.26/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.26/0.97      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_2585,plain,
% 3.26/0.97      ( k7_relset_1(sK3,sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
% 3.26/0.97      inference(superposition,[status(thm)],[c_1358,c_1365]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_28,negated_conjecture,
% 3.26/0.97      ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
% 3.26/0.97      inference(cnf_transformation,[],[f84]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_1359,plain,
% 3.26/0.97      ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
% 3.26/0.97      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_2659,plain,
% 3.26/0.97      ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) = iProver_top ),
% 3.26/0.97      inference(demodulation,[status(thm)],[c_2585,c_1359]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_25,plain,
% 3.26/0.97      ( ~ m1_subset_1(X0,X1)
% 3.26/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 3.26/0.97      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 3.26/0.97      | r2_hidden(k4_tarski(sK2(X4,X3,X2,X0),X0),X2)
% 3.26/0.97      | v1_xboole_0(X1)
% 3.26/0.97      | v1_xboole_0(X4)
% 3.26/0.97      | v1_xboole_0(X3) ),
% 3.26/0.97      inference(cnf_transformation,[],[f79]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_1362,plain,
% 3.26/0.97      ( m1_subset_1(X0,X1) != iProver_top
% 3.26/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 3.26/0.97      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 3.26/0.97      | r2_hidden(k4_tarski(sK2(X4,X3,X2,X0),X0),X2) = iProver_top
% 3.26/0.97      | v1_xboole_0(X1) = iProver_top
% 3.26/0.97      | v1_xboole_0(X4) = iProver_top
% 3.26/0.97      | v1_xboole_0(X3) = iProver_top ),
% 3.26/0.97      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_3048,plain,
% 3.26/0.97      ( m1_subset_1(X0,sK4) != iProver_top
% 3.26/0.97      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.26/0.97      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.26/0.97      | r2_hidden(k4_tarski(sK2(X1,sK3,sK6,X0),X0),sK6) = iProver_top
% 3.26/0.97      | v1_xboole_0(X1) = iProver_top
% 3.26/0.97      | v1_xboole_0(sK4) = iProver_top
% 3.26/0.97      | v1_xboole_0(sK3) = iProver_top ),
% 3.26/0.97      inference(superposition,[status(thm)],[c_2585,c_1362]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_32,plain,
% 3.26/0.97      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.26/0.97      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_18,plain,
% 3.26/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.97      | v1_relat_1(X0) ),
% 3.26/0.97      inference(cnf_transformation,[],[f73]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_1605,plain,
% 3.26/0.97      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.26/0.97      | v1_relat_1(sK6) ),
% 3.26/0.97      inference(instantiation,[status(thm)],[c_18]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_1606,plain,
% 3.26/0.97      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.26/0.97      | v1_relat_1(sK6) = iProver_top ),
% 3.26/0.97      inference(predicate_to_equality,[status(thm)],[c_1605]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_13,plain,
% 3.26/0.97      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.26/0.97      | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
% 3.26/0.97      | ~ v1_relat_1(X1) ),
% 3.26/0.97      inference(cnf_transformation,[],[f65]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_1368,plain,
% 3.26/0.97      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.26/0.97      | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 3.26/0.97      | v1_relat_1(X1) != iProver_top ),
% 3.26/0.97      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_19,plain,
% 3.26/0.97      ( v5_relat_1(X0,X1)
% 3.26/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.26/0.97      inference(cnf_transformation,[],[f75]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_14,plain,
% 3.26/0.97      ( ~ v5_relat_1(X0,X1)
% 3.26/0.97      | ~ r2_hidden(X2,k1_relat_1(X0))
% 3.26/0.97      | r2_hidden(k1_funct_1(X0,X2),X1)
% 3.26/0.97      | ~ v1_funct_1(X0)
% 3.26/0.97      | ~ v1_relat_1(X0) ),
% 3.26/0.97      inference(cnf_transformation,[],[f69]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_343,plain,
% 3.26/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.97      | ~ r2_hidden(X3,k1_relat_1(X0))
% 3.26/0.97      | r2_hidden(k1_funct_1(X0,X3),X2)
% 3.26/0.97      | ~ v1_funct_1(X0)
% 3.26/0.97      | ~ v1_relat_1(X0) ),
% 3.26/0.97      inference(resolution,[status(thm)],[c_19,c_14]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_347,plain,
% 3.26/0.97      ( ~ v1_funct_1(X0)
% 3.26/0.97      | r2_hidden(k1_funct_1(X0,X3),X2)
% 3.26/0.97      | ~ r2_hidden(X3,k1_relat_1(X0))
% 3.26/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.26/0.97      inference(global_propositional_subsumption,
% 3.26/0.97                [status(thm)],
% 3.26/0.97                [c_343,c_18]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_348,plain,
% 3.26/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.97      | ~ r2_hidden(X3,k1_relat_1(X0))
% 3.26/0.97      | r2_hidden(k1_funct_1(X0,X3),X2)
% 3.26/0.97      | ~ v1_funct_1(X0) ),
% 3.26/0.97      inference(renaming,[status(thm)],[c_347]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_30,negated_conjecture,
% 3.26/0.97      ( v1_funct_1(sK6) ),
% 3.26/0.97      inference(cnf_transformation,[],[f82]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_392,plain,
% 3.26/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.97      | ~ r2_hidden(X3,k1_relat_1(X0))
% 3.26/0.97      | r2_hidden(k1_funct_1(X0,X3),X2)
% 3.26/0.97      | sK6 != X0 ),
% 3.26/0.97      inference(resolution_lifted,[status(thm)],[c_348,c_30]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_393,plain,
% 3.26/0.97      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.26/0.97      | ~ r2_hidden(X2,k1_relat_1(sK6))
% 3.26/0.97      | r2_hidden(k1_funct_1(sK6,X2),X1) ),
% 3.26/0.97      inference(unflattening,[status(thm)],[c_392]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_1356,plain,
% 3.26/0.97      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.26/0.97      | r2_hidden(X2,k1_relat_1(sK6)) != iProver_top
% 3.26/0.97      | r2_hidden(k1_funct_1(sK6,X2),X1) = iProver_top ),
% 3.26/0.97      inference(predicate_to_equality,[status(thm)],[c_393]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_1702,plain,
% 3.26/0.97      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.26/0.97      | r2_hidden(k1_funct_1(sK6,X0),sK4) = iProver_top ),
% 3.26/0.97      inference(superposition,[status(thm)],[c_1358,c_1356]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_0,plain,
% 3.26/0.97      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.26/0.97      inference(cnf_transformation,[],[f55]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_1378,plain,
% 3.26/0.97      ( r2_hidden(X0,X1) != iProver_top
% 3.26/0.97      | v1_xboole_0(X1) != iProver_top ),
% 3.26/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_1804,plain,
% 3.26/0.97      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.26/0.97      | v1_xboole_0(sK4) != iProver_top ),
% 3.26/0.97      inference(superposition,[status(thm)],[c_1702,c_1378]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_3303,plain,
% 3.26/0.97      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.26/0.97      | v1_relat_1(sK6) != iProver_top
% 3.26/0.97      | v1_xboole_0(sK4) != iProver_top ),
% 3.26/0.97      inference(superposition,[status(thm)],[c_1368,c_1804]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_21,plain,
% 3.26/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.97      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
% 3.26/0.97      inference(cnf_transformation,[],[f76]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_1366,plain,
% 3.26/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.26/0.97      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
% 3.26/0.97      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_3086,plain,
% 3.26/0.97      ( m1_subset_1(k9_relat_1(sK6,X0),k1_zfmisc_1(sK4)) = iProver_top
% 3.26/0.97      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
% 3.26/0.97      inference(superposition,[status(thm)],[c_2585,c_1366]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_3398,plain,
% 3.26/0.97      ( m1_subset_1(k9_relat_1(sK6,X0),k1_zfmisc_1(sK4)) = iProver_top ),
% 3.26/0.97      inference(global_propositional_subsumption,
% 3.26/0.97                [status(thm)],
% 3.26/0.97                [c_3086,c_32]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_7,plain,
% 3.26/0.97      ( m1_subset_1(X0,X1)
% 3.26/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.26/0.97      | ~ r2_hidden(X0,X2) ),
% 3.26/0.97      inference(cnf_transformation,[],[f62]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_1372,plain,
% 3.26/0.97      ( m1_subset_1(X0,X1) = iProver_top
% 3.26/0.97      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.26/0.97      | r2_hidden(X0,X2) != iProver_top ),
% 3.26/0.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_3405,plain,
% 3.26/0.97      ( m1_subset_1(X0,sK4) = iProver_top
% 3.26/0.97      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
% 3.26/0.97      inference(superposition,[status(thm)],[c_3398,c_1372]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_3410,plain,
% 3.26/0.97      ( v1_xboole_0(X1) = iProver_top
% 3.26/0.97      | r2_hidden(k4_tarski(sK2(X1,sK3,sK6,X0),X0),sK6) = iProver_top
% 3.26/0.97      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.26/0.97      | v1_xboole_0(sK3) = iProver_top ),
% 3.26/0.97      inference(global_propositional_subsumption,
% 3.26/0.97                [status(thm)],
% 3.26/0.97                [c_3048,c_32,c_1606,c_3303,c_3405]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_3411,plain,
% 3.26/0.97      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.26/0.97      | r2_hidden(k4_tarski(sK2(X1,sK3,sK6,X0),X0),sK6) = iProver_top
% 3.26/0.97      | v1_xboole_0(X1) = iProver_top
% 3.26/0.97      | v1_xboole_0(sK3) = iProver_top ),
% 3.26/0.97      inference(renaming,[status(thm)],[c_3410]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_16,plain,
% 3.26/0.97      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.26/0.97      | ~ v1_funct_1(X2)
% 3.26/0.97      | ~ v1_relat_1(X2)
% 3.26/0.97      | k1_funct_1(X2,X0) = X1 ),
% 3.26/0.97      inference(cnf_transformation,[],[f71]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_437,plain,
% 3.26/0.97      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.26/0.97      | ~ v1_relat_1(X2)
% 3.26/0.97      | k1_funct_1(X2,X0) = X1
% 3.26/0.97      | sK6 != X2 ),
% 3.26/0.97      inference(resolution_lifted,[status(thm)],[c_16,c_30]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_438,plain,
% 3.26/0.97      ( ~ r2_hidden(k4_tarski(X0,X1),sK6)
% 3.26/0.97      | ~ v1_relat_1(sK6)
% 3.26/0.97      | k1_funct_1(sK6,X0) = X1 ),
% 3.26/0.97      inference(unflattening,[status(thm)],[c_437]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_1353,plain,
% 3.26/0.97      ( k1_funct_1(sK6,X0) = X1
% 3.26/0.97      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
% 3.26/0.97      | v1_relat_1(sK6) != iProver_top ),
% 3.26/0.97      inference(predicate_to_equality,[status(thm)],[c_438]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_439,plain,
% 3.26/0.97      ( k1_funct_1(sK6,X0) = X1
% 3.26/0.97      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
% 3.26/0.97      | v1_relat_1(sK6) != iProver_top ),
% 3.26/0.97      inference(predicate_to_equality,[status(thm)],[c_438]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_1630,plain,
% 3.26/0.97      ( r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
% 3.26/0.97      | k1_funct_1(sK6,X0) = X1 ),
% 3.26/0.97      inference(global_propositional_subsumption,
% 3.26/0.97                [status(thm)],
% 3.26/0.97                [c_1353,c_32,c_439,c_1606]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_1631,plain,
% 3.26/0.97      ( k1_funct_1(sK6,X0) = X1
% 3.26/0.97      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top ),
% 3.26/0.97      inference(renaming,[status(thm)],[c_1630]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_3422,plain,
% 3.26/0.97      ( k1_funct_1(sK6,sK2(X0,sK3,sK6,X1)) = X1
% 3.26/0.97      | r2_hidden(X1,k9_relat_1(sK6,X0)) != iProver_top
% 3.26/0.97      | v1_xboole_0(X0) = iProver_top
% 3.26/0.97      | v1_xboole_0(sK3) = iProver_top ),
% 3.26/0.97      inference(superposition,[status(thm)],[c_3411,c_1631]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_3543,plain,
% 3.26/0.97      ( k1_funct_1(sK6,sK2(sK5,sK3,sK6,sK7)) = sK7
% 3.26/0.97      | v1_xboole_0(sK3) = iProver_top
% 3.26/0.97      | v1_xboole_0(sK5) = iProver_top ),
% 3.26/0.97      inference(superposition,[status(thm)],[c_2659,c_3422]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_20,plain,
% 3.26/0.97      ( v4_relat_1(X0,X1)
% 3.26/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.26/0.97      inference(cnf_transformation,[],[f74]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_9,plain,
% 3.26/0.97      ( ~ v4_relat_1(X0,X1)
% 3.26/0.97      | r1_tarski(k1_relat_1(X0),X1)
% 3.26/0.97      | ~ v1_relat_1(X0) ),
% 3.26/0.97      inference(cnf_transformation,[],[f63]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_371,plain,
% 3.26/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.97      | r1_tarski(k1_relat_1(X0),X1)
% 3.26/0.97      | ~ v1_relat_1(X0) ),
% 3.26/0.97      inference(resolution,[status(thm)],[c_20,c_9]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_375,plain,
% 3.26/0.97      ( r1_tarski(k1_relat_1(X0),X1)
% 3.26/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.26/0.97      inference(global_propositional_subsumption,
% 3.26/0.97                [status(thm)],
% 3.26/0.97                [c_371,c_18]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_376,plain,
% 3.26/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.97      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.26/0.97      inference(renaming,[status(thm)],[c_375]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_1357,plain,
% 3.26/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.26/0.97      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.26/0.97      inference(predicate_to_equality,[status(thm)],[c_376]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_1790,plain,
% 3.26/0.97      ( r1_tarski(k1_relat_1(sK6),sK3) = iProver_top ),
% 3.26/0.97      inference(superposition,[status(thm)],[c_1358,c_1357]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_3,plain,
% 3.26/0.97      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.26/0.97      inference(cnf_transformation,[],[f56]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_1375,plain,
% 3.26/0.97      ( r1_tarski(X0,X1) != iProver_top
% 3.26/0.97      | r2_hidden(X2,X0) != iProver_top
% 3.26/0.97      | r2_hidden(X2,X1) = iProver_top ),
% 3.26/0.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_2593,plain,
% 3.26/0.97      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.26/0.97      | r2_hidden(X0,sK3) = iProver_top ),
% 3.26/0.97      inference(superposition,[status(thm)],[c_1790,c_1375]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_3302,plain,
% 3.26/0.97      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.26/0.97      | r2_hidden(sK1(X0,X1,sK6),sK3) = iProver_top
% 3.26/0.97      | v1_relat_1(sK6) != iProver_top ),
% 3.26/0.97      inference(superposition,[status(thm)],[c_1368,c_2593]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_7063,plain,
% 3.26/0.97      ( r2_hidden(sK1(X0,X1,sK6),sK3) = iProver_top
% 3.26/0.97      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
% 3.26/0.97      inference(global_propositional_subsumption,
% 3.26/0.97                [status(thm)],
% 3.26/0.97                [c_3302,c_32,c_1606]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_7064,plain,
% 3.26/0.97      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.26/0.97      | r2_hidden(sK1(X0,X1,sK6),sK3) = iProver_top ),
% 3.26/0.97      inference(renaming,[status(thm)],[c_7063]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_7072,plain,
% 3.26/0.97      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.26/0.97      | v1_xboole_0(sK3) != iProver_top ),
% 3.26/0.97      inference(superposition,[status(thm)],[c_7064,c_1378]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_7547,plain,
% 3.26/0.97      ( v1_xboole_0(sK3) != iProver_top ),
% 3.26/0.97      inference(superposition,[status(thm)],[c_2659,c_7072]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_7908,plain,
% 3.26/0.97      ( k1_funct_1(sK6,sK2(sK5,sK3,sK6,sK7)) = sK7
% 3.26/0.97      | v1_xboole_0(sK5) = iProver_top ),
% 3.26/0.97      inference(superposition,[status(thm)],[c_3543,c_7547]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_11,plain,
% 3.26/0.97      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.26/0.97      | r2_hidden(sK1(X0,X2,X1),X2)
% 3.26/0.97      | ~ v1_relat_1(X1) ),
% 3.26/0.97      inference(cnf_transformation,[],[f67]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_1370,plain,
% 3.26/0.97      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.26/0.97      | r2_hidden(sK1(X0,X2,X1),X2) = iProver_top
% 3.26/0.97      | v1_relat_1(X1) != iProver_top ),
% 3.26/0.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_3211,plain,
% 3.26/0.97      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.26/0.97      | v1_relat_1(X1) != iProver_top
% 3.26/0.97      | v1_xboole_0(X2) != iProver_top ),
% 3.26/0.97      inference(superposition,[status(thm)],[c_1370,c_1378]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_6127,plain,
% 3.26/0.97      ( v1_relat_1(sK6) != iProver_top
% 3.26/0.97      | v1_xboole_0(sK5) != iProver_top ),
% 3.26/0.97      inference(superposition,[status(thm)],[c_2659,c_3211]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_10580,plain,
% 3.26/0.97      ( k1_funct_1(sK6,sK2(sK5,sK3,sK6,sK7)) = sK7 ),
% 3.26/0.97      inference(global_propositional_subsumption,
% 3.26/0.97                [status(thm)],
% 3.26/0.97                [c_7908,c_32,c_1606,c_3543,c_6127,c_7547]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_27,negated_conjecture,
% 3.26/0.97      ( ~ m1_subset_1(X0,sK3)
% 3.26/0.97      | ~ r2_hidden(X0,sK5)
% 3.26/0.97      | k1_funct_1(sK6,X0) != sK7 ),
% 3.26/0.97      inference(cnf_transformation,[],[f85]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_1360,plain,
% 3.26/0.97      ( k1_funct_1(sK6,X0) != sK7
% 3.26/0.97      | m1_subset_1(X0,sK3) != iProver_top
% 3.26/0.97      | r2_hidden(X0,sK5) != iProver_top ),
% 3.26/0.97      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_10590,plain,
% 3.26/0.97      ( m1_subset_1(sK2(sK5,sK3,sK6,sK7),sK3) != iProver_top
% 3.26/0.97      | r2_hidden(sK2(sK5,sK3,sK6,sK7),sK5) != iProver_top ),
% 3.26/0.97      inference(superposition,[status(thm)],[c_10580,c_1360]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_24,plain,
% 3.26/0.97      ( ~ m1_subset_1(X0,X1)
% 3.26/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 3.26/0.97      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 3.26/0.97      | r2_hidden(sK2(X4,X3,X2,X0),X4)
% 3.26/0.97      | v1_xboole_0(X1)
% 3.26/0.97      | v1_xboole_0(X4)
% 3.26/0.97      | v1_xboole_0(X3) ),
% 3.26/0.97      inference(cnf_transformation,[],[f80]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_1882,plain,
% 3.26/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK4)))
% 3.26/0.97      | ~ m1_subset_1(sK7,sK4)
% 3.26/0.97      | r2_hidden(sK2(X2,X1,X0,sK7),X2)
% 3.26/0.97      | ~ r2_hidden(sK7,k7_relset_1(X1,sK4,X0,X2))
% 3.26/0.97      | v1_xboole_0(X1)
% 3.26/0.97      | v1_xboole_0(X2)
% 3.26/0.97      | v1_xboole_0(sK4) ),
% 3.26/0.97      inference(instantiation,[status(thm)],[c_24]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_3009,plain,
% 3.26/0.97      ( ~ m1_subset_1(sK7,sK4)
% 3.26/0.97      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.26/0.97      | r2_hidden(sK2(X0,sK3,sK6,sK7),X0)
% 3.26/0.97      | ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,X0))
% 3.26/0.97      | v1_xboole_0(X0)
% 3.26/0.97      | v1_xboole_0(sK4)
% 3.26/0.97      | v1_xboole_0(sK3) ),
% 3.26/0.97      inference(instantiation,[status(thm)],[c_1882]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_7664,plain,
% 3.26/0.97      ( ~ m1_subset_1(sK7,sK4)
% 3.26/0.97      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.26/0.97      | r2_hidden(sK2(sK5,sK3,sK6,sK7),sK5)
% 3.26/0.97      | ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
% 3.26/0.97      | v1_xboole_0(sK4)
% 3.26/0.97      | v1_xboole_0(sK3)
% 3.26/0.97      | v1_xboole_0(sK5) ),
% 3.26/0.97      inference(instantiation,[status(thm)],[c_3009]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_7665,plain,
% 3.26/0.97      ( m1_subset_1(sK7,sK4) != iProver_top
% 3.26/0.97      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.26/0.97      | r2_hidden(sK2(sK5,sK3,sK6,sK7),sK5) = iProver_top
% 3.26/0.97      | r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) != iProver_top
% 3.26/0.97      | v1_xboole_0(sK4) = iProver_top
% 3.26/0.97      | v1_xboole_0(sK3) = iProver_top
% 3.26/0.97      | v1_xboole_0(sK5) = iProver_top ),
% 3.26/0.97      inference(predicate_to_equality,[status(thm)],[c_7664]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_12,plain,
% 3.26/0.97      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.26/0.97      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 3.26/0.97      | ~ v1_relat_1(X1) ),
% 3.26/0.97      inference(cnf_transformation,[],[f66]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_1369,plain,
% 3.26/0.97      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.26/0.97      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
% 3.26/0.97      | v1_relat_1(X1) != iProver_top ),
% 3.26/0.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_4129,plain,
% 3.26/0.97      ( k1_funct_1(sK6,sK1(X0,X1,sK6)) = X0
% 3.26/0.97      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.26/0.97      | v1_relat_1(sK6) != iProver_top ),
% 3.26/0.97      inference(superposition,[status(thm)],[c_1369,c_1631]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_4408,plain,
% 3.26/0.97      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.26/0.97      | k1_funct_1(sK6,sK1(X0,X1,sK6)) = X0 ),
% 3.26/0.97      inference(global_propositional_subsumption,
% 3.26/0.97                [status(thm)],
% 3.26/0.97                [c_4129,c_32,c_1606]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_4409,plain,
% 3.26/0.97      ( k1_funct_1(sK6,sK1(X0,X1,sK6)) = X0
% 3.26/0.97      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
% 3.26/0.97      inference(renaming,[status(thm)],[c_4408]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_4419,plain,
% 3.26/0.97      ( k1_funct_1(sK6,sK1(sK7,sK5,sK6)) = sK7 ),
% 3.26/0.97      inference(superposition,[status(thm)],[c_2659,c_4409]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_4448,plain,
% 3.26/0.97      ( r2_hidden(sK1(sK7,sK5,sK6),k1_relat_1(sK6)) != iProver_top
% 3.26/0.97      | r2_hidden(sK7,sK4) = iProver_top ),
% 3.26/0.97      inference(superposition,[status(thm)],[c_4419,c_1702]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_4518,plain,
% 3.26/0.97      ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
% 3.26/0.97      | r2_hidden(sK7,sK4) = iProver_top
% 3.26/0.97      | v1_relat_1(sK6) != iProver_top ),
% 3.26/0.97      inference(superposition,[status(thm)],[c_1368,c_4448]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_3179,plain,
% 3.26/0.97      ( ~ r2_hidden(X0,sK4) | ~ v1_xboole_0(sK4) ),
% 3.26/0.97      inference(instantiation,[status(thm)],[c_0]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_3795,plain,
% 3.26/0.97      ( ~ r2_hidden(sK7,sK4) | ~ v1_xboole_0(sK4) ),
% 3.26/0.97      inference(instantiation,[status(thm)],[c_3179]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_3798,plain,
% 3.26/0.97      ( r2_hidden(sK7,sK4) != iProver_top
% 3.26/0.97      | v1_xboole_0(sK4) != iProver_top ),
% 3.26/0.97      inference(predicate_to_equality,[status(thm)],[c_3795]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_26,plain,
% 3.26/0.97      ( ~ m1_subset_1(X0,X1)
% 3.26/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 3.26/0.97      | m1_subset_1(sK2(X4,X3,X2,X0),X3)
% 3.26/0.97      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 3.26/0.97      | v1_xboole_0(X1)
% 3.26/0.97      | v1_xboole_0(X4)
% 3.26/0.97      | v1_xboole_0(X3) ),
% 3.26/0.97      inference(cnf_transformation,[],[f78]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_1361,plain,
% 3.26/0.97      ( m1_subset_1(X0,X1) != iProver_top
% 3.26/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 3.26/0.97      | m1_subset_1(sK2(X4,X3,X2,X0),X3) = iProver_top
% 3.26/0.97      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 3.26/0.97      | v1_xboole_0(X1) = iProver_top
% 3.26/0.97      | v1_xboole_0(X4) = iProver_top
% 3.26/0.97      | v1_xboole_0(X3) = iProver_top ),
% 3.26/0.97      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_2423,plain,
% 3.26/0.97      ( m1_subset_1(sK2(sK5,sK3,sK6,sK7),sK3) = iProver_top
% 3.26/0.97      | m1_subset_1(sK7,sK4) != iProver_top
% 3.26/0.97      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.26/0.97      | v1_xboole_0(sK4) = iProver_top
% 3.26/0.97      | v1_xboole_0(sK3) = iProver_top
% 3.26/0.97      | v1_xboole_0(sK5) = iProver_top ),
% 3.26/0.97      inference(superposition,[status(thm)],[c_1359,c_1361]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_33,plain,
% 3.26/0.97      ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
% 3.26/0.97      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_1620,plain,
% 3.26/0.97      ( ~ m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(X0))
% 3.26/0.97      | m1_subset_1(sK7,X0)
% 3.26/0.97      | ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
% 3.26/0.97      inference(instantiation,[status(thm)],[c_7]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_1750,plain,
% 3.26/0.97      ( ~ m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(sK4))
% 3.26/0.97      | m1_subset_1(sK7,sK4)
% 3.26/0.97      | ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
% 3.26/0.97      inference(instantiation,[status(thm)],[c_1620]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_1752,plain,
% 3.26/0.97      ( m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(sK4)) != iProver_top
% 3.26/0.97      | m1_subset_1(sK7,sK4) = iProver_top
% 3.26/0.97      | r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) != iProver_top ),
% 3.26/0.97      inference(predicate_to_equality,[status(thm)],[c_1750]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_1638,plain,
% 3.26/0.97      ( m1_subset_1(k7_relset_1(sK3,sK4,sK6,X0),k1_zfmisc_1(sK4))
% 3.26/0.97      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.26/0.97      inference(instantiation,[status(thm)],[c_21]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_1751,plain,
% 3.26/0.97      ( m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(sK4))
% 3.26/0.97      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.26/0.97      inference(instantiation,[status(thm)],[c_1638]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_1754,plain,
% 3.26/0.97      ( m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(sK4)) = iProver_top
% 3.26/0.97      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
% 3.26/0.97      inference(predicate_to_equality,[status(thm)],[c_1751]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_2764,plain,
% 3.26/0.97      ( m1_subset_1(sK2(sK5,sK3,sK6,sK7),sK3) = iProver_top
% 3.26/0.97      | v1_xboole_0(sK4) = iProver_top
% 3.26/0.97      | v1_xboole_0(sK3) = iProver_top
% 3.26/0.97      | v1_xboole_0(sK5) = iProver_top ),
% 3.26/0.97      inference(global_propositional_subsumption,
% 3.26/0.97                [status(thm)],
% 3.26/0.97                [c_2423,c_32,c_33,c_1752,c_1754]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(contradiction,plain,
% 3.26/0.97      ( $false ),
% 3.26/0.97      inference(minisat,
% 3.26/0.97                [status(thm)],
% 3.26/0.97                [c_10590,c_7665,c_7547,c_6127,c_4518,c_3798,c_2764,
% 3.26/0.97                 c_2659,c_1754,c_1752,c_1606,c_33,c_32]) ).
% 3.26/0.97  
% 3.26/0.97  
% 3.26/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.26/0.97  
% 3.26/0.97  ------                               Statistics
% 3.26/0.97  
% 3.26/0.97  ------ General
% 3.26/0.97  
% 3.26/0.97  abstr_ref_over_cycles:                  0
% 3.26/0.97  abstr_ref_under_cycles:                 0
% 3.26/0.97  gc_basic_clause_elim:                   0
% 3.26/0.97  forced_gc_time:                         0
% 3.26/0.97  parsing_time:                           0.012
% 3.26/0.97  unif_index_cands_time:                  0.
% 3.26/0.97  unif_index_add_time:                    0.
% 3.26/0.97  orderings_time:                         0.
% 3.26/0.97  out_proof_time:                         0.011
% 3.26/0.97  total_time:                             0.341
% 3.26/0.97  num_of_symbols:                         54
% 3.26/0.97  num_of_terms:                           11492
% 3.26/0.97  
% 3.26/0.97  ------ Preprocessing
% 3.26/0.97  
% 3.26/0.97  num_of_splits:                          0
% 3.26/0.97  num_of_split_atoms:                     0
% 3.26/0.97  num_of_reused_defs:                     0
% 3.26/0.97  num_eq_ax_congr_red:                    48
% 3.26/0.97  num_of_sem_filtered_clauses:            1
% 3.26/0.97  num_of_subtypes:                        0
% 3.26/0.97  monotx_restored_types:                  0
% 3.26/0.97  sat_num_of_epr_types:                   0
% 3.26/0.97  sat_num_of_non_cyclic_types:            0
% 3.26/0.97  sat_guarded_non_collapsed_types:        0
% 3.26/0.97  num_pure_diseq_elim:                    0
% 3.26/0.97  simp_replaced_by:                       0
% 3.26/0.97  res_preprocessed:                       133
% 3.26/0.97  prep_upred:                             0
% 3.26/0.97  prep_unflattend:                        18
% 3.26/0.97  smt_new_axioms:                         0
% 3.26/0.97  pred_elim_cands:                        5
% 3.26/0.97  pred_elim:                              3
% 3.26/0.97  pred_elim_cl:                           4
% 3.26/0.97  pred_elim_cycles:                       5
% 3.26/0.97  merged_defs:                            0
% 3.26/0.97  merged_defs_ncl:                        0
% 3.26/0.97  bin_hyper_res:                          0
% 3.26/0.97  prep_cycles:                            4
% 3.26/0.97  pred_elim_time:                         0.008
% 3.26/0.97  splitting_time:                         0.
% 3.26/0.97  sem_filter_time:                        0.
% 3.26/0.97  monotx_time:                            0.
% 3.26/0.97  subtype_inf_time:                       0.
% 3.26/0.97  
% 3.26/0.97  ------ Problem properties
% 3.26/0.97  
% 3.26/0.97  clauses:                                26
% 3.26/0.97  conjectures:                            3
% 3.26/0.97  epr:                                    4
% 3.26/0.97  horn:                                   21
% 3.26/0.97  ground:                                 2
% 3.26/0.97  unary:                                  3
% 3.26/0.97  binary:                                 7
% 3.26/0.97  lits:                                   85
% 3.26/0.97  lits_eq:                                4
% 3.26/0.97  fd_pure:                                0
% 3.26/0.97  fd_pseudo:                              0
% 3.26/0.97  fd_cond:                                0
% 3.26/0.97  fd_pseudo_cond:                         2
% 3.26/0.97  ac_symbols:                             0
% 3.26/0.97  
% 3.26/0.97  ------ Propositional Solver
% 3.26/0.97  
% 3.26/0.97  prop_solver_calls:                      29
% 3.26/0.97  prop_fast_solver_calls:                 1377
% 3.26/0.97  smt_solver_calls:                       0
% 3.26/0.97  smt_fast_solver_calls:                  0
% 3.26/0.97  prop_num_of_clauses:                    3738
% 3.26/0.97  prop_preprocess_simplified:             7731
% 3.26/0.97  prop_fo_subsumed:                       51
% 3.26/0.97  prop_solver_time:                       0.
% 3.26/0.97  smt_solver_time:                        0.
% 3.26/0.97  smt_fast_solver_time:                   0.
% 3.26/0.97  prop_fast_solver_time:                  0.
% 3.26/0.97  prop_unsat_core_time:                   0.
% 3.26/0.97  
% 3.26/0.97  ------ QBF
% 3.26/0.97  
% 3.26/0.97  qbf_q_res:                              0
% 3.26/0.97  qbf_num_tautologies:                    0
% 3.26/0.97  qbf_prep_cycles:                        0
% 3.26/0.97  
% 3.26/0.97  ------ BMC1
% 3.26/0.97  
% 3.26/0.97  bmc1_current_bound:                     -1
% 3.26/0.97  bmc1_last_solved_bound:                 -1
% 3.26/0.97  bmc1_unsat_core_size:                   -1
% 3.26/0.97  bmc1_unsat_core_parents_size:           -1
% 3.26/0.97  bmc1_merge_next_fun:                    0
% 3.26/0.97  bmc1_unsat_core_clauses_time:           0.
% 3.26/0.97  
% 3.26/0.97  ------ Instantiation
% 3.26/0.97  
% 3.26/0.97  inst_num_of_clauses:                    937
% 3.26/0.97  inst_num_in_passive:                    266
% 3.26/0.97  inst_num_in_active:                     394
% 3.26/0.97  inst_num_in_unprocessed:                280
% 3.26/0.97  inst_num_of_loops:                      580
% 3.26/0.97  inst_num_of_learning_restarts:          0
% 3.26/0.97  inst_num_moves_active_passive:          181
% 3.26/0.97  inst_lit_activity:                      0
% 3.26/0.97  inst_lit_activity_moves:                0
% 3.26/0.97  inst_num_tautologies:                   0
% 3.26/0.97  inst_num_prop_implied:                  0
% 3.26/0.97  inst_num_existing_simplified:           0
% 3.26/0.97  inst_num_eq_res_simplified:             0
% 3.26/0.97  inst_num_child_elim:                    0
% 3.26/0.97  inst_num_of_dismatching_blockings:      488
% 3.26/0.97  inst_num_of_non_proper_insts:           944
% 3.26/0.97  inst_num_of_duplicates:                 0
% 3.26/0.97  inst_inst_num_from_inst_to_res:         0
% 3.26/0.97  inst_dismatching_checking_time:         0.
% 3.26/0.97  
% 3.26/0.97  ------ Resolution
% 3.26/0.97  
% 3.26/0.97  res_num_of_clauses:                     0
% 3.26/0.97  res_num_in_passive:                     0
% 3.26/0.97  res_num_in_active:                      0
% 3.26/0.97  res_num_of_loops:                       137
% 3.26/0.97  res_forward_subset_subsumed:            111
% 3.26/0.97  res_backward_subset_subsumed:           6
% 3.26/0.97  res_forward_subsumed:                   0
% 3.26/0.97  res_backward_subsumed:                  0
% 3.26/0.97  res_forward_subsumption_resolution:     0
% 3.26/0.97  res_backward_subsumption_resolution:    0
% 3.26/0.97  res_clause_to_clause_subsumption:       1109
% 3.26/0.97  res_orphan_elimination:                 0
% 3.26/0.97  res_tautology_del:                      65
% 3.26/0.97  res_num_eq_res_simplified:              0
% 3.26/0.97  res_num_sel_changes:                    0
% 3.26/0.97  res_moves_from_active_to_pass:          0
% 3.26/0.97  
% 3.26/0.97  ------ Superposition
% 3.26/0.97  
% 3.26/0.97  sup_time_total:                         0.
% 3.26/0.97  sup_time_generating:                    0.
% 3.26/0.97  sup_time_sim_full:                      0.
% 3.26/0.97  sup_time_sim_immed:                     0.
% 3.26/0.97  
% 3.26/0.97  sup_num_of_clauses:                     250
% 3.26/0.97  sup_num_in_active:                      110
% 3.26/0.97  sup_num_in_passive:                     140
% 3.26/0.97  sup_num_of_loops:                       114
% 3.26/0.97  sup_fw_superposition:                   176
% 3.26/0.97  sup_bw_superposition:                   156
% 3.26/0.97  sup_immediate_simplified:               70
% 3.26/0.97  sup_given_eliminated:                   2
% 3.26/0.97  comparisons_done:                       0
% 3.26/0.97  comparisons_avoided:                    0
% 3.26/0.97  
% 3.26/0.97  ------ Simplifications
% 3.26/0.97  
% 3.26/0.97  
% 3.26/0.97  sim_fw_subset_subsumed:                 42
% 3.26/0.97  sim_bw_subset_subsumed:                 4
% 3.26/0.97  sim_fw_subsumed:                        12
% 3.26/0.97  sim_bw_subsumed:                        9
% 3.26/0.97  sim_fw_subsumption_res:                 4
% 3.26/0.97  sim_bw_subsumption_res:                 0
% 3.26/0.97  sim_tautology_del:                      8
% 3.26/0.97  sim_eq_tautology_del:                   10
% 3.26/0.97  sim_eq_res_simp:                        0
% 3.26/0.97  sim_fw_demodulated:                     0
% 3.26/0.97  sim_bw_demodulated:                     2
% 3.26/0.97  sim_light_normalised:                   12
% 3.26/0.97  sim_joinable_taut:                      0
% 3.26/0.97  sim_joinable_simp:                      0
% 3.26/0.97  sim_ac_normalised:                      0
% 3.26/0.97  sim_smt_subsumption:                    0
% 3.26/0.97  
%------------------------------------------------------------------------------
