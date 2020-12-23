%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:51 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :  146 (1218 expanded)
%              Number of clauses        :   80 ( 369 expanded)
%              Number of leaves         :   17 ( 265 expanded)
%              Depth                    :   22
%              Number of atoms          :  564 (5670 expanded)
%              Number of equality atoms :  184 (1160 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f29])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK7
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X5,X0) )
        & r2_hidden(sK7,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK6,X5) != X4
              | ~ r2_hidden(X5,sK5)
              | ~ r2_hidden(X5,sK3) )
          & r2_hidden(X4,k7_relset_1(sK3,sK4,sK6,sK5)) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ! [X5] :
        ( k1_funct_1(sK6,X5) != sK7
        | ~ r2_hidden(X5,sK5)
        | ~ r2_hidden(X5,sK3) )
    & r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f30,f47,f46])).

fof(f74,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X4,X3,X2,X1] :
      ( ? [X6] :
          ( r2_hidden(X6,X1)
          & r2_hidden(k4_tarski(X6,X4),X3)
          & m1_subset_1(X6,X2) )
     => ( r2_hidden(sK2(X1,X2,X3,X4),X1)
        & r2_hidden(k4_tarski(sK2(X1,X2,X3,X4),X4),X3)
        & m1_subset_1(sK2(X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK2(X1,X2,X3,X4),X1)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f77,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f63])).

fof(f73,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f49,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
    r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
    inference(cnf_transformation,[],[f48])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK2(X1,X2,X3,X4),X4),X3)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f76,plain,(
    ! [X5] :
      ( k1_funct_1(sK6,X5) != sK7
      | ~ r2_hidden(X5,sK5)
      | ~ r2_hidden(X5,sK3) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK2(X1,X2,X3,X4),X2)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1239,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1246,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2324,plain,
    ( k7_relset_1(sK3,sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_1239,c_1246])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | r2_hidden(sK2(X4,X3,X2,X0),X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1244,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | r2_hidden(sK2(X4,X3,X2,X0),X4) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3160,plain,
    ( m1_subset_1(X0,sK4) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(X1,sK3,sK6,X0),X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_1244])).

cnf(c_29,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1510,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1511,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1510])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1248,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3201,plain,
    ( v1_xboole_0(sK4) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1239,c_1248])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1249,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3327,plain,
    ( v1_xboole_0(sK3) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1239,c_1249])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1247,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2556,plain,
    ( m1_subset_1(k9_relat_1(sK6,X0),k1_zfmisc_1(sK4)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_1247])).

cnf(c_3032,plain,
    ( m1_subset_1(k9_relat_1(sK6,X0),k1_zfmisc_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2556,c_29])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1255,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3347,plain,
    ( m1_subset_1(X0,sK4) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3032,c_1255])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1251,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_328,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_329,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6)
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_328])).

cnf(c_1237,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_329])).

cnf(c_330,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_329])).

cnf(c_1567,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1237,c_29,c_330,c_1511])).

cnf(c_1568,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_1567])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1260,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1790,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1568,c_1260])).

cnf(c_4095,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1251,c_1790])).

cnf(c_5410,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(X1,sK3,sK6,X0),X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3160,c_29,c_1511,c_3201,c_3327,c_3347,c_4095])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1240,plain,
    ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2546,plain,
    ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2324,c_1240])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | r2_hidden(k4_tarski(sK2(X4,X3,X2,X0),X0),X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1243,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X4,X3,X2,X0),X0),X2) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2557,plain,
    ( m1_subset_1(X0,sK4) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X1,sK3,sK6,X0),X0),sK6) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_1243])).

cnf(c_5502,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X1,sK3,sK6,X0),X0),sK6) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2557,c_29,c_1511,c_3201,c_3327,c_3347,c_4095])).

cnf(c_13,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_343,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_27])).

cnf(c_344,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK6)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(c_1236,plain,
    ( k1_funct_1(sK6,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_344])).

cnf(c_345,plain,
    ( k1_funct_1(sK6,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_344])).

cnf(c_1523,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | k1_funct_1(sK6,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1236,c_29,c_345,c_1511])).

cnf(c_1524,plain,
    ( k1_funct_1(sK6,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_1523])).

cnf(c_5515,plain,
    ( k1_funct_1(sK6,sK2(X0,sK3,sK6,X1)) = X1
    | r2_hidden(X1,k9_relat_1(sK6,X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5502,c_1524])).

cnf(c_6957,plain,
    ( k1_funct_1(sK6,sK2(sK5,sK3,sK6,sK7)) = sK7
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_5515])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1253,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK1(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3500,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1253,c_1260])).

cnf(c_9715,plain,
    ( v1_relat_1(sK6) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_3500])).

cnf(c_9965,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9715,c_29,c_1511])).

cnf(c_9970,plain,
    ( k1_funct_1(sK6,sK2(sK5,sK3,sK6,sK7)) = sK7 ),
    inference(superposition,[status(thm)],[c_6957,c_9965])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK5)
    | k1_funct_1(sK6,X0) != sK7 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1241,plain,
    ( k1_funct_1(sK6,X0) != sK7
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_11015,plain,
    ( r2_hidden(sK2(sK5,sK3,sK6,sK7),sK3) != iProver_top
    | r2_hidden(sK2(sK5,sK3,sK6,sK7),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_9970,c_1241])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | m1_subset_1(sK2(X4,X3,X2,X0),X3)
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1242,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(sK2(X4,X3,X2,X0),X3) = iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1694,plain,
    ( m1_subset_1(sK2(sK5,sK3,sK6,sK7),sK3) = iProver_top
    | m1_subset_1(sK7,sK4) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1240,c_1242])).

cnf(c_1977,plain,
    ( m1_subset_1(sK7,sK4) != iProver_top
    | m1_subset_1(sK2(sK5,sK3,sK6,sK7),sK3) = iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1694,c_29])).

cnf(c_1978,plain,
    ( m1_subset_1(sK2(sK5,sK3,sK6,sK7),sK3) = iProver_top
    | m1_subset_1(sK7,sK4) != iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_1977])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1257,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1986,plain,
    ( m1_subset_1(sK7,sK4) != iProver_top
    | r2_hidden(sK2(sK5,sK3,sK6,sK7),sK3) = iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1978,c_1257])).

cnf(c_6072,plain,
    ( m1_subset_1(sK7,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_3347])).

cnf(c_5511,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5502,c_1260])).

cnf(c_8171,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5511,c_29,c_1511,c_4095])).

cnf(c_8182,plain,
    ( v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_8171])).

cnf(c_11125,plain,
    ( r2_hidden(sK2(sK5,sK3,sK6,sK7),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11015,c_29,c_1511,c_1986,c_3201,c_3327,c_6072,c_8182,c_9715])).

cnf(c_11130,plain,
    ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_5410,c_11125])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11130,c_9715,c_2546,c_1511,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:16:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.72/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/0.99  
% 2.72/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.72/0.99  
% 2.72/0.99  ------  iProver source info
% 2.72/0.99  
% 2.72/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.72/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.72/0.99  git: non_committed_changes: false
% 2.72/0.99  git: last_make_outside_of_git: false
% 2.72/0.99  
% 2.72/0.99  ------ 
% 2.72/0.99  
% 2.72/0.99  ------ Input Options
% 2.72/0.99  
% 2.72/0.99  --out_options                           all
% 2.72/0.99  --tptp_safe_out                         true
% 2.72/0.99  --problem_path                          ""
% 2.72/0.99  --include_path                          ""
% 2.72/0.99  --clausifier                            res/vclausify_rel
% 2.72/0.99  --clausifier_options                    --mode clausify
% 2.72/0.99  --stdin                                 false
% 2.72/0.99  --stats_out                             all
% 2.72/0.99  
% 2.72/0.99  ------ General Options
% 2.72/0.99  
% 2.72/0.99  --fof                                   false
% 2.72/0.99  --time_out_real                         305.
% 2.72/0.99  --time_out_virtual                      -1.
% 2.72/0.99  --symbol_type_check                     false
% 2.72/0.99  --clausify_out                          false
% 2.72/0.99  --sig_cnt_out                           false
% 2.72/0.99  --trig_cnt_out                          false
% 2.72/0.99  --trig_cnt_out_tolerance                1.
% 2.72/0.99  --trig_cnt_out_sk_spl                   false
% 2.72/0.99  --abstr_cl_out                          false
% 2.72/0.99  
% 2.72/0.99  ------ Global Options
% 2.72/0.99  
% 2.72/0.99  --schedule                              default
% 2.72/0.99  --add_important_lit                     false
% 2.72/0.99  --prop_solver_per_cl                    1000
% 2.72/0.99  --min_unsat_core                        false
% 2.72/0.99  --soft_assumptions                      false
% 2.72/0.99  --soft_lemma_size                       3
% 2.72/0.99  --prop_impl_unit_size                   0
% 2.72/0.99  --prop_impl_unit                        []
% 2.72/0.99  --share_sel_clauses                     true
% 2.72/0.99  --reset_solvers                         false
% 2.72/0.99  --bc_imp_inh                            [conj_cone]
% 2.72/0.99  --conj_cone_tolerance                   3.
% 2.72/0.99  --extra_neg_conj                        none
% 2.72/0.99  --large_theory_mode                     true
% 2.72/0.99  --prolific_symb_bound                   200
% 2.72/0.99  --lt_threshold                          2000
% 2.72/0.99  --clause_weak_htbl                      true
% 2.72/0.99  --gc_record_bc_elim                     false
% 2.72/0.99  
% 2.72/0.99  ------ Preprocessing Options
% 2.72/0.99  
% 2.72/0.99  --preprocessing_flag                    true
% 2.72/0.99  --time_out_prep_mult                    0.1
% 2.72/0.99  --splitting_mode                        input
% 2.72/0.99  --splitting_grd                         true
% 2.72/0.99  --splitting_cvd                         false
% 2.72/0.99  --splitting_cvd_svl                     false
% 2.72/0.99  --splitting_nvd                         32
% 2.72/0.99  --sub_typing                            true
% 2.72/0.99  --prep_gs_sim                           true
% 2.72/0.99  --prep_unflatten                        true
% 2.72/0.99  --prep_res_sim                          true
% 2.72/0.99  --prep_upred                            true
% 2.72/0.99  --prep_sem_filter                       exhaustive
% 2.72/0.99  --prep_sem_filter_out                   false
% 2.72/0.99  --pred_elim                             true
% 2.72/0.99  --res_sim_input                         true
% 2.72/0.99  --eq_ax_congr_red                       true
% 2.72/0.99  --pure_diseq_elim                       true
% 2.72/0.99  --brand_transform                       false
% 2.72/0.99  --non_eq_to_eq                          false
% 2.72/0.99  --prep_def_merge                        true
% 2.72/0.99  --prep_def_merge_prop_impl              false
% 2.72/0.99  --prep_def_merge_mbd                    true
% 2.72/0.99  --prep_def_merge_tr_red                 false
% 2.72/0.99  --prep_def_merge_tr_cl                  false
% 2.72/0.99  --smt_preprocessing                     true
% 2.72/0.99  --smt_ac_axioms                         fast
% 2.72/0.99  --preprocessed_out                      false
% 2.72/0.99  --preprocessed_stats                    false
% 2.72/0.99  
% 2.72/0.99  ------ Abstraction refinement Options
% 2.72/0.99  
% 2.72/0.99  --abstr_ref                             []
% 2.72/0.99  --abstr_ref_prep                        false
% 2.72/0.99  --abstr_ref_until_sat                   false
% 2.72/0.99  --abstr_ref_sig_restrict                funpre
% 2.72/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.72/0.99  --abstr_ref_under                       []
% 2.72/0.99  
% 2.72/0.99  ------ SAT Options
% 2.72/0.99  
% 2.72/0.99  --sat_mode                              false
% 2.72/0.99  --sat_fm_restart_options                ""
% 2.72/0.99  --sat_gr_def                            false
% 2.72/0.99  --sat_epr_types                         true
% 2.72/0.99  --sat_non_cyclic_types                  false
% 2.72/0.99  --sat_finite_models                     false
% 2.72/0.99  --sat_fm_lemmas                         false
% 2.72/0.99  --sat_fm_prep                           false
% 2.72/0.99  --sat_fm_uc_incr                        true
% 2.72/0.99  --sat_out_model                         small
% 2.72/0.99  --sat_out_clauses                       false
% 2.72/0.99  
% 2.72/0.99  ------ QBF Options
% 2.72/0.99  
% 2.72/0.99  --qbf_mode                              false
% 2.72/0.99  --qbf_elim_univ                         false
% 2.72/0.99  --qbf_dom_inst                          none
% 2.72/0.99  --qbf_dom_pre_inst                      false
% 2.72/0.99  --qbf_sk_in                             false
% 2.72/0.99  --qbf_pred_elim                         true
% 2.72/0.99  --qbf_split                             512
% 2.72/0.99  
% 2.72/0.99  ------ BMC1 Options
% 2.72/0.99  
% 2.72/0.99  --bmc1_incremental                      false
% 2.72/0.99  --bmc1_axioms                           reachable_all
% 2.72/0.99  --bmc1_min_bound                        0
% 2.72/0.99  --bmc1_max_bound                        -1
% 2.72/0.99  --bmc1_max_bound_default                -1
% 2.72/0.99  --bmc1_symbol_reachability              true
% 2.72/0.99  --bmc1_property_lemmas                  false
% 2.72/0.99  --bmc1_k_induction                      false
% 2.72/0.99  --bmc1_non_equiv_states                 false
% 2.72/0.99  --bmc1_deadlock                         false
% 2.72/0.99  --bmc1_ucm                              false
% 2.72/0.99  --bmc1_add_unsat_core                   none
% 2.72/0.99  --bmc1_unsat_core_children              false
% 2.72/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.72/0.99  --bmc1_out_stat                         full
% 2.72/0.99  --bmc1_ground_init                      false
% 2.72/0.99  --bmc1_pre_inst_next_state              false
% 2.72/0.99  --bmc1_pre_inst_state                   false
% 2.72/0.99  --bmc1_pre_inst_reach_state             false
% 2.72/0.99  --bmc1_out_unsat_core                   false
% 2.72/0.99  --bmc1_aig_witness_out                  false
% 2.72/0.99  --bmc1_verbose                          false
% 2.72/0.99  --bmc1_dump_clauses_tptp                false
% 2.72/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.72/0.99  --bmc1_dump_file                        -
% 2.72/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.72/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.72/0.99  --bmc1_ucm_extend_mode                  1
% 2.72/0.99  --bmc1_ucm_init_mode                    2
% 2.72/0.99  --bmc1_ucm_cone_mode                    none
% 2.72/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.72/0.99  --bmc1_ucm_relax_model                  4
% 2.72/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.72/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.72/0.99  --bmc1_ucm_layered_model                none
% 2.72/0.99  --bmc1_ucm_max_lemma_size               10
% 2.72/0.99  
% 2.72/0.99  ------ AIG Options
% 2.72/0.99  
% 2.72/0.99  --aig_mode                              false
% 2.72/0.99  
% 2.72/0.99  ------ Instantiation Options
% 2.72/0.99  
% 2.72/0.99  --instantiation_flag                    true
% 2.72/0.99  --inst_sos_flag                         false
% 2.72/0.99  --inst_sos_phase                        true
% 2.72/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.72/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.72/0.99  --inst_lit_sel_side                     num_symb
% 2.72/0.99  --inst_solver_per_active                1400
% 2.72/0.99  --inst_solver_calls_frac                1.
% 2.72/0.99  --inst_passive_queue_type               priority_queues
% 2.72/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.72/0.99  --inst_passive_queues_freq              [25;2]
% 2.72/0.99  --inst_dismatching                      true
% 2.72/0.99  --inst_eager_unprocessed_to_passive     true
% 2.72/0.99  --inst_prop_sim_given                   true
% 2.72/0.99  --inst_prop_sim_new                     false
% 2.72/0.99  --inst_subs_new                         false
% 2.72/0.99  --inst_eq_res_simp                      false
% 2.72/0.99  --inst_subs_given                       false
% 2.72/0.99  --inst_orphan_elimination               true
% 2.72/0.99  --inst_learning_loop_flag               true
% 2.72/0.99  --inst_learning_start                   3000
% 2.72/0.99  --inst_learning_factor                  2
% 2.72/0.99  --inst_start_prop_sim_after_learn       3
% 2.72/0.99  --inst_sel_renew                        solver
% 2.72/0.99  --inst_lit_activity_flag                true
% 2.72/0.99  --inst_restr_to_given                   false
% 2.72/0.99  --inst_activity_threshold               500
% 2.72/0.99  --inst_out_proof                        true
% 2.72/0.99  
% 2.72/0.99  ------ Resolution Options
% 2.72/0.99  
% 2.72/0.99  --resolution_flag                       true
% 2.72/0.99  --res_lit_sel                           adaptive
% 2.72/0.99  --res_lit_sel_side                      none
% 2.72/0.99  --res_ordering                          kbo
% 2.72/0.99  --res_to_prop_solver                    active
% 2.72/0.99  --res_prop_simpl_new                    false
% 2.72/0.99  --res_prop_simpl_given                  true
% 2.72/0.99  --res_passive_queue_type                priority_queues
% 2.72/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.72/0.99  --res_passive_queues_freq               [15;5]
% 2.72/0.99  --res_forward_subs                      full
% 2.72/0.99  --res_backward_subs                     full
% 2.72/0.99  --res_forward_subs_resolution           true
% 2.72/0.99  --res_backward_subs_resolution          true
% 2.72/0.99  --res_orphan_elimination                true
% 2.72/0.99  --res_time_limit                        2.
% 2.72/0.99  --res_out_proof                         true
% 2.72/0.99  
% 2.72/0.99  ------ Superposition Options
% 2.72/0.99  
% 2.72/0.99  --superposition_flag                    true
% 2.72/0.99  --sup_passive_queue_type                priority_queues
% 2.72/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.72/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.72/0.99  --demod_completeness_check              fast
% 2.72/0.99  --demod_use_ground                      true
% 2.72/0.99  --sup_to_prop_solver                    passive
% 2.72/0.99  --sup_prop_simpl_new                    true
% 2.72/0.99  --sup_prop_simpl_given                  true
% 2.72/0.99  --sup_fun_splitting                     false
% 2.72/0.99  --sup_smt_interval                      50000
% 2.72/0.99  
% 2.72/0.99  ------ Superposition Simplification Setup
% 2.72/0.99  
% 2.72/0.99  --sup_indices_passive                   []
% 2.72/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.72/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.99  --sup_full_bw                           [BwDemod]
% 2.72/0.99  --sup_immed_triv                        [TrivRules]
% 2.72/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.72/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.99  --sup_immed_bw_main                     []
% 2.72/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.72/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/0.99  
% 2.72/0.99  ------ Combination Options
% 2.72/0.99  
% 2.72/0.99  --comb_res_mult                         3
% 2.72/0.99  --comb_sup_mult                         2
% 2.72/0.99  --comb_inst_mult                        10
% 2.72/0.99  
% 2.72/0.99  ------ Debug Options
% 2.72/0.99  
% 2.72/0.99  --dbg_backtrace                         false
% 2.72/0.99  --dbg_dump_prop_clauses                 false
% 2.72/0.99  --dbg_dump_prop_clauses_file            -
% 2.72/0.99  --dbg_out_stat                          false
% 2.72/0.99  ------ Parsing...
% 2.72/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.72/0.99  
% 2.72/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.72/0.99  
% 2.72/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.72/0.99  
% 2.72/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.72/0.99  ------ Proving...
% 2.72/0.99  ------ Problem Properties 
% 2.72/0.99  
% 2.72/0.99  
% 2.72/0.99  clauses                                 26
% 2.72/0.99  conjectures                             3
% 2.72/0.99  EPR                                     5
% 2.72/0.99  Horn                                    20
% 2.72/0.99  unary                                   2
% 2.72/0.99  binary                                  6
% 2.72/0.99  lits                                    88
% 2.72/0.99  lits eq                                 3
% 2.72/0.99  fd_pure                                 0
% 2.72/0.99  fd_pseudo                               0
% 2.72/0.99  fd_cond                                 0
% 2.72/0.99  fd_pseudo_cond                          1
% 2.72/0.99  AC symbols                              0
% 2.72/0.99  
% 2.72/0.99  ------ Schedule dynamic 5 is on 
% 2.72/0.99  
% 2.72/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.72/0.99  
% 2.72/0.99  
% 2.72/0.99  ------ 
% 2.72/0.99  Current options:
% 2.72/0.99  ------ 
% 2.72/0.99  
% 2.72/0.99  ------ Input Options
% 2.72/0.99  
% 2.72/0.99  --out_options                           all
% 2.72/0.99  --tptp_safe_out                         true
% 2.72/0.99  --problem_path                          ""
% 2.72/0.99  --include_path                          ""
% 2.72/0.99  --clausifier                            res/vclausify_rel
% 2.72/0.99  --clausifier_options                    --mode clausify
% 2.72/0.99  --stdin                                 false
% 2.72/0.99  --stats_out                             all
% 2.72/0.99  
% 2.72/0.99  ------ General Options
% 2.72/0.99  
% 2.72/0.99  --fof                                   false
% 2.72/0.99  --time_out_real                         305.
% 2.72/0.99  --time_out_virtual                      -1.
% 2.72/0.99  --symbol_type_check                     false
% 2.72/0.99  --clausify_out                          false
% 2.72/0.99  --sig_cnt_out                           false
% 2.72/0.99  --trig_cnt_out                          false
% 2.72/0.99  --trig_cnt_out_tolerance                1.
% 2.72/0.99  --trig_cnt_out_sk_spl                   false
% 2.72/0.99  --abstr_cl_out                          false
% 2.72/0.99  
% 2.72/0.99  ------ Global Options
% 2.72/0.99  
% 2.72/0.99  --schedule                              default
% 2.72/0.99  --add_important_lit                     false
% 2.72/0.99  --prop_solver_per_cl                    1000
% 2.72/0.99  --min_unsat_core                        false
% 2.72/0.99  --soft_assumptions                      false
% 2.72/0.99  --soft_lemma_size                       3
% 2.72/0.99  --prop_impl_unit_size                   0
% 2.72/0.99  --prop_impl_unit                        []
% 2.72/0.99  --share_sel_clauses                     true
% 2.72/0.99  --reset_solvers                         false
% 2.72/0.99  --bc_imp_inh                            [conj_cone]
% 2.72/0.99  --conj_cone_tolerance                   3.
% 2.72/0.99  --extra_neg_conj                        none
% 2.72/0.99  --large_theory_mode                     true
% 2.72/0.99  --prolific_symb_bound                   200
% 2.72/0.99  --lt_threshold                          2000
% 2.72/0.99  --clause_weak_htbl                      true
% 2.72/0.99  --gc_record_bc_elim                     false
% 2.72/0.99  
% 2.72/0.99  ------ Preprocessing Options
% 2.72/0.99  
% 2.72/0.99  --preprocessing_flag                    true
% 2.72/0.99  --time_out_prep_mult                    0.1
% 2.72/0.99  --splitting_mode                        input
% 2.72/0.99  --splitting_grd                         true
% 2.72/0.99  --splitting_cvd                         false
% 2.72/0.99  --splitting_cvd_svl                     false
% 2.72/0.99  --splitting_nvd                         32
% 2.72/0.99  --sub_typing                            true
% 2.72/0.99  --prep_gs_sim                           true
% 2.72/0.99  --prep_unflatten                        true
% 2.72/0.99  --prep_res_sim                          true
% 2.72/0.99  --prep_upred                            true
% 2.72/0.99  --prep_sem_filter                       exhaustive
% 2.72/0.99  --prep_sem_filter_out                   false
% 2.72/0.99  --pred_elim                             true
% 2.72/0.99  --res_sim_input                         true
% 2.72/0.99  --eq_ax_congr_red                       true
% 2.72/0.99  --pure_diseq_elim                       true
% 2.72/0.99  --brand_transform                       false
% 2.72/0.99  --non_eq_to_eq                          false
% 2.72/0.99  --prep_def_merge                        true
% 2.72/0.99  --prep_def_merge_prop_impl              false
% 2.72/0.99  --prep_def_merge_mbd                    true
% 2.72/0.99  --prep_def_merge_tr_red                 false
% 2.72/0.99  --prep_def_merge_tr_cl                  false
% 2.72/0.99  --smt_preprocessing                     true
% 2.72/0.99  --smt_ac_axioms                         fast
% 2.72/0.99  --preprocessed_out                      false
% 2.72/0.99  --preprocessed_stats                    false
% 2.72/0.99  
% 2.72/0.99  ------ Abstraction refinement Options
% 2.72/0.99  
% 2.72/0.99  --abstr_ref                             []
% 2.72/0.99  --abstr_ref_prep                        false
% 2.72/0.99  --abstr_ref_until_sat                   false
% 2.72/0.99  --abstr_ref_sig_restrict                funpre
% 2.72/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.72/0.99  --abstr_ref_under                       []
% 2.72/0.99  
% 2.72/0.99  ------ SAT Options
% 2.72/0.99  
% 2.72/0.99  --sat_mode                              false
% 2.72/0.99  --sat_fm_restart_options                ""
% 2.72/0.99  --sat_gr_def                            false
% 2.72/0.99  --sat_epr_types                         true
% 2.72/0.99  --sat_non_cyclic_types                  false
% 2.72/0.99  --sat_finite_models                     false
% 2.72/0.99  --sat_fm_lemmas                         false
% 2.72/0.99  --sat_fm_prep                           false
% 2.72/0.99  --sat_fm_uc_incr                        true
% 2.72/0.99  --sat_out_model                         small
% 2.72/0.99  --sat_out_clauses                       false
% 2.72/0.99  
% 2.72/0.99  ------ QBF Options
% 2.72/0.99  
% 2.72/0.99  --qbf_mode                              false
% 2.72/0.99  --qbf_elim_univ                         false
% 2.72/0.99  --qbf_dom_inst                          none
% 2.72/0.99  --qbf_dom_pre_inst                      false
% 2.72/0.99  --qbf_sk_in                             false
% 2.72/0.99  --qbf_pred_elim                         true
% 2.72/0.99  --qbf_split                             512
% 2.72/0.99  
% 2.72/0.99  ------ BMC1 Options
% 2.72/0.99  
% 2.72/0.99  --bmc1_incremental                      false
% 2.72/0.99  --bmc1_axioms                           reachable_all
% 2.72/0.99  --bmc1_min_bound                        0
% 2.72/0.99  --bmc1_max_bound                        -1
% 2.72/0.99  --bmc1_max_bound_default                -1
% 2.72/0.99  --bmc1_symbol_reachability              true
% 2.72/0.99  --bmc1_property_lemmas                  false
% 2.72/0.99  --bmc1_k_induction                      false
% 2.72/0.99  --bmc1_non_equiv_states                 false
% 2.72/0.99  --bmc1_deadlock                         false
% 2.72/0.99  --bmc1_ucm                              false
% 2.72/0.99  --bmc1_add_unsat_core                   none
% 2.72/0.99  --bmc1_unsat_core_children              false
% 2.72/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.72/0.99  --bmc1_out_stat                         full
% 2.72/0.99  --bmc1_ground_init                      false
% 2.72/0.99  --bmc1_pre_inst_next_state              false
% 2.72/0.99  --bmc1_pre_inst_state                   false
% 2.72/0.99  --bmc1_pre_inst_reach_state             false
% 2.72/0.99  --bmc1_out_unsat_core                   false
% 2.72/0.99  --bmc1_aig_witness_out                  false
% 2.72/0.99  --bmc1_verbose                          false
% 2.72/0.99  --bmc1_dump_clauses_tptp                false
% 2.72/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.72/0.99  --bmc1_dump_file                        -
% 2.72/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.72/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.72/0.99  --bmc1_ucm_extend_mode                  1
% 2.72/0.99  --bmc1_ucm_init_mode                    2
% 2.72/0.99  --bmc1_ucm_cone_mode                    none
% 2.72/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.72/0.99  --bmc1_ucm_relax_model                  4
% 2.72/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.72/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.72/0.99  --bmc1_ucm_layered_model                none
% 2.72/0.99  --bmc1_ucm_max_lemma_size               10
% 2.72/0.99  
% 2.72/0.99  ------ AIG Options
% 2.72/0.99  
% 2.72/0.99  --aig_mode                              false
% 2.72/0.99  
% 2.72/0.99  ------ Instantiation Options
% 2.72/0.99  
% 2.72/0.99  --instantiation_flag                    true
% 2.72/0.99  --inst_sos_flag                         false
% 2.72/0.99  --inst_sos_phase                        true
% 2.72/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.72/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.72/0.99  --inst_lit_sel_side                     none
% 2.72/0.99  --inst_solver_per_active                1400
% 2.72/0.99  --inst_solver_calls_frac                1.
% 2.72/0.99  --inst_passive_queue_type               priority_queues
% 2.72/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.72/0.99  --inst_passive_queues_freq              [25;2]
% 2.72/0.99  --inst_dismatching                      true
% 2.72/0.99  --inst_eager_unprocessed_to_passive     true
% 2.72/0.99  --inst_prop_sim_given                   true
% 2.72/0.99  --inst_prop_sim_new                     false
% 2.72/0.99  --inst_subs_new                         false
% 2.72/0.99  --inst_eq_res_simp                      false
% 2.72/0.99  --inst_subs_given                       false
% 2.72/0.99  --inst_orphan_elimination               true
% 2.72/0.99  --inst_learning_loop_flag               true
% 2.72/0.99  --inst_learning_start                   3000
% 2.72/0.99  --inst_learning_factor                  2
% 2.72/0.99  --inst_start_prop_sim_after_learn       3
% 2.72/0.99  --inst_sel_renew                        solver
% 2.72/0.99  --inst_lit_activity_flag                true
% 2.72/0.99  --inst_restr_to_given                   false
% 2.72/0.99  --inst_activity_threshold               500
% 2.72/0.99  --inst_out_proof                        true
% 2.72/0.99  
% 2.72/0.99  ------ Resolution Options
% 2.72/0.99  
% 2.72/0.99  --resolution_flag                       false
% 2.72/0.99  --res_lit_sel                           adaptive
% 2.72/0.99  --res_lit_sel_side                      none
% 2.72/0.99  --res_ordering                          kbo
% 2.72/0.99  --res_to_prop_solver                    active
% 2.72/0.99  --res_prop_simpl_new                    false
% 2.72/0.99  --res_prop_simpl_given                  true
% 2.72/0.99  --res_passive_queue_type                priority_queues
% 2.72/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.72/0.99  --res_passive_queues_freq               [15;5]
% 2.72/0.99  --res_forward_subs                      full
% 2.72/0.99  --res_backward_subs                     full
% 2.72/0.99  --res_forward_subs_resolution           true
% 2.72/0.99  --res_backward_subs_resolution          true
% 2.72/0.99  --res_orphan_elimination                true
% 2.72/0.99  --res_time_limit                        2.
% 2.72/0.99  --res_out_proof                         true
% 2.72/0.99  
% 2.72/0.99  ------ Superposition Options
% 2.72/0.99  
% 2.72/0.99  --superposition_flag                    true
% 2.72/0.99  --sup_passive_queue_type                priority_queues
% 2.72/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.72/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.72/0.99  --demod_completeness_check              fast
% 2.72/0.99  --demod_use_ground                      true
% 2.72/0.99  --sup_to_prop_solver                    passive
% 2.72/0.99  --sup_prop_simpl_new                    true
% 2.72/0.99  --sup_prop_simpl_given                  true
% 2.72/0.99  --sup_fun_splitting                     false
% 2.72/0.99  --sup_smt_interval                      50000
% 2.72/0.99  
% 2.72/0.99  ------ Superposition Simplification Setup
% 2.72/0.99  
% 2.72/0.99  --sup_indices_passive                   []
% 2.72/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.72/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.99  --sup_full_bw                           [BwDemod]
% 2.72/0.99  --sup_immed_triv                        [TrivRules]
% 2.72/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.72/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.99  --sup_immed_bw_main                     []
% 2.72/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.72/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/0.99  
% 2.72/0.99  ------ Combination Options
% 2.72/0.99  
% 2.72/0.99  --comb_res_mult                         3
% 2.72/0.99  --comb_sup_mult                         2
% 2.72/0.99  --comb_inst_mult                        10
% 2.72/0.99  
% 2.72/0.99  ------ Debug Options
% 2.72/0.99  
% 2.72/0.99  --dbg_backtrace                         false
% 2.72/0.99  --dbg_dump_prop_clauses                 false
% 2.72/0.99  --dbg_dump_prop_clauses_file            -
% 2.72/0.99  --dbg_out_stat                          false
% 2.72/0.99  
% 2.72/0.99  
% 2.72/0.99  
% 2.72/0.99  
% 2.72/0.99  ------ Proving...
% 2.72/0.99  
% 2.72/0.99  
% 2.72/0.99  % SZS status Theorem for theBenchmark.p
% 2.72/0.99  
% 2.72/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.72/0.99  
% 2.72/0.99  fof(f13,conjecture,(
% 2.72/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f14,negated_conjecture,(
% 2.72/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.72/0.99    inference(negated_conjecture,[],[f13])).
% 2.72/0.99  
% 2.72/0.99  fof(f15,plain,(
% 2.72/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.72/0.99    inference(pure_predicate_removal,[],[f14])).
% 2.72/0.99  
% 2.72/0.99  fof(f29,plain,(
% 2.72/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 2.72/0.99    inference(ennf_transformation,[],[f15])).
% 2.72/0.99  
% 2.72/0.99  fof(f30,plain,(
% 2.72/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 2.72/0.99    inference(flattening,[],[f29])).
% 2.72/0.99  
% 2.72/0.99  fof(f47,plain,(
% 2.72/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK7 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(sK7,k7_relset_1(X0,X1,X3,X2)))) )),
% 2.72/0.99    introduced(choice_axiom,[])).
% 2.72/0.99  
% 2.72/0.99  fof(f46,plain,(
% 2.72/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK6,X5) != X4 | ~r2_hidden(X5,sK5) | ~r2_hidden(X5,sK3)) & r2_hidden(X4,k7_relset_1(sK3,sK4,sK6,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK6))),
% 2.72/0.99    introduced(choice_axiom,[])).
% 2.72/0.99  
% 2.72/0.99  fof(f48,plain,(
% 2.72/0.99    (! [X5] : (k1_funct_1(sK6,X5) != sK7 | ~r2_hidden(X5,sK5) | ~r2_hidden(X5,sK3)) & r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK6)),
% 2.72/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f30,f47,f46])).
% 2.72/0.99  
% 2.72/0.99  fof(f74,plain,(
% 2.72/0.99    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 2.72/0.99    inference(cnf_transformation,[],[f48])).
% 2.72/0.99  
% 2.72/0.99  fof(f11,axiom,(
% 2.72/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f27,plain,(
% 2.72/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.72/0.99    inference(ennf_transformation,[],[f11])).
% 2.72/0.99  
% 2.72/0.99  fof(f68,plain,(
% 2.72/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.72/0.99    inference(cnf_transformation,[],[f27])).
% 2.72/0.99  
% 2.72/0.99  fof(f12,axiom,(
% 2.72/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f28,plain,(
% 2.72/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.72/0.99    inference(ennf_transformation,[],[f12])).
% 2.72/0.99  
% 2.72/0.99  fof(f42,plain,(
% 2.72/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.72/0.99    inference(nnf_transformation,[],[f28])).
% 2.72/0.99  
% 2.72/0.99  fof(f43,plain,(
% 2.72/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.72/0.99    inference(rectify,[],[f42])).
% 2.72/0.99  
% 2.72/0.99  fof(f44,plain,(
% 2.72/0.99    ! [X4,X3,X2,X1] : (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) => (r2_hidden(sK2(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK2(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK2(X1,X2,X3,X4),X2)))),
% 2.72/0.99    introduced(choice_axiom,[])).
% 2.72/0.99  
% 2.72/0.99  fof(f45,plain,(
% 2.72/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & ((r2_hidden(sK2(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK2(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK2(X1,X2,X3,X4),X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.72/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).
% 2.72/0.99  
% 2.72/0.99  fof(f71,plain,(
% 2.72/0.99    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK2(X1,X2,X3,X4),X1) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.72/0.99    inference(cnf_transformation,[],[f45])).
% 2.72/0.99  
% 2.72/0.99  fof(f7,axiom,(
% 2.72/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f23,plain,(
% 2.72/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.72/0.99    inference(ennf_transformation,[],[f7])).
% 2.72/0.99  
% 2.72/0.99  fof(f64,plain,(
% 2.72/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.72/0.99    inference(cnf_transformation,[],[f23])).
% 2.72/0.99  
% 2.72/0.99  fof(f9,axiom,(
% 2.72/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f25,plain,(
% 2.72/0.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.72/0.99    inference(ennf_transformation,[],[f9])).
% 2.72/0.99  
% 2.72/0.99  fof(f66,plain,(
% 2.72/0.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 2.72/0.99    inference(cnf_transformation,[],[f25])).
% 2.72/0.99  
% 2.72/0.99  fof(f8,axiom,(
% 2.72/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f24,plain,(
% 2.72/0.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.72/0.99    inference(ennf_transformation,[],[f8])).
% 2.72/0.99  
% 2.72/0.99  fof(f65,plain,(
% 2.72/0.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.72/0.99    inference(cnf_transformation,[],[f24])).
% 2.72/0.99  
% 2.72/0.99  fof(f10,axiom,(
% 2.72/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f26,plain,(
% 2.72/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.72/0.99    inference(ennf_transformation,[],[f10])).
% 2.72/0.99  
% 2.72/0.99  fof(f67,plain,(
% 2.72/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.72/0.99    inference(cnf_transformation,[],[f26])).
% 2.72/0.99  
% 2.72/0.99  fof(f4,axiom,(
% 2.72/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f18,plain,(
% 2.72/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.72/0.99    inference(ennf_transformation,[],[f4])).
% 2.72/0.99  
% 2.72/0.99  fof(f19,plain,(
% 2.72/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.72/0.99    inference(flattening,[],[f18])).
% 2.72/0.99  
% 2.72/0.99  fof(f56,plain,(
% 2.72/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.72/0.99    inference(cnf_transformation,[],[f19])).
% 2.72/0.99  
% 2.72/0.99  fof(f5,axiom,(
% 2.72/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f20,plain,(
% 2.72/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 2.72/0.99    inference(ennf_transformation,[],[f5])).
% 2.72/0.99  
% 2.72/0.99  fof(f36,plain,(
% 2.72/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.72/0.99    inference(nnf_transformation,[],[f20])).
% 2.72/0.99  
% 2.72/0.99  fof(f37,plain,(
% 2.72/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.72/0.99    inference(rectify,[],[f36])).
% 2.72/0.99  
% 2.72/0.99  fof(f38,plain,(
% 2.72/0.99    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 2.72/0.99    introduced(choice_axiom,[])).
% 2.72/0.99  
% 2.72/0.99  fof(f39,plain,(
% 2.72/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.72/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 2.72/0.99  
% 2.72/0.99  fof(f57,plain,(
% 2.72/0.99    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.72/0.99    inference(cnf_transformation,[],[f39])).
% 2.72/0.99  
% 2.72/0.99  fof(f6,axiom,(
% 2.72/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f21,plain,(
% 2.72/0.99    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.72/0.99    inference(ennf_transformation,[],[f6])).
% 2.72/0.99  
% 2.72/0.99  fof(f22,plain,(
% 2.72/0.99    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.72/0.99    inference(flattening,[],[f21])).
% 2.72/0.99  
% 2.72/0.99  fof(f40,plain,(
% 2.72/0.99    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.72/0.99    inference(nnf_transformation,[],[f22])).
% 2.72/0.99  
% 2.72/0.99  fof(f41,plain,(
% 2.72/0.99    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.72/0.99    inference(flattening,[],[f40])).
% 2.72/0.99  
% 2.72/0.99  fof(f63,plain,(
% 2.72/0.99    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.72/0.99    inference(cnf_transformation,[],[f41])).
% 2.72/0.99  
% 2.72/0.99  fof(f77,plain,(
% 2.72/0.99    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.72/0.99    inference(equality_resolution,[],[f63])).
% 2.72/0.99  
% 2.72/0.99  fof(f73,plain,(
% 2.72/0.99    v1_funct_1(sK6)),
% 2.72/0.99    inference(cnf_transformation,[],[f48])).
% 2.72/0.99  
% 2.72/0.99  fof(f1,axiom,(
% 2.72/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f31,plain,(
% 2.72/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.72/0.99    inference(nnf_transformation,[],[f1])).
% 2.72/0.99  
% 2.72/0.99  fof(f32,plain,(
% 2.72/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.72/0.99    inference(rectify,[],[f31])).
% 2.72/0.99  
% 2.72/0.99  fof(f33,plain,(
% 2.72/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.72/0.99    introduced(choice_axiom,[])).
% 2.72/0.99  
% 2.72/0.99  fof(f34,plain,(
% 2.72/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.72/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 2.72/0.99  
% 2.72/0.99  fof(f49,plain,(
% 2.72/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.72/0.99    inference(cnf_transformation,[],[f34])).
% 2.72/0.99  
% 2.72/0.99  fof(f75,plain,(
% 2.72/0.99    r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))),
% 2.72/0.99    inference(cnf_transformation,[],[f48])).
% 2.72/0.99  
% 2.72/0.99  fof(f70,plain,(
% 2.72/0.99    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK2(X1,X2,X3,X4),X4),X3) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.72/0.99    inference(cnf_transformation,[],[f45])).
% 2.72/0.99  
% 2.72/0.99  fof(f62,plain,(
% 2.72/0.99    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.72/0.99    inference(cnf_transformation,[],[f41])).
% 2.72/0.99  
% 2.72/0.99  fof(f59,plain,(
% 2.72/0.99    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.72/0.99    inference(cnf_transformation,[],[f39])).
% 2.72/0.99  
% 2.72/0.99  fof(f76,plain,(
% 2.72/0.99    ( ! [X5] : (k1_funct_1(sK6,X5) != sK7 | ~r2_hidden(X5,sK5) | ~r2_hidden(X5,sK3)) )),
% 2.72/0.99    inference(cnf_transformation,[],[f48])).
% 2.72/0.99  
% 2.72/0.99  fof(f69,plain,(
% 2.72/0.99    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK2(X1,X2,X3,X4),X2) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.72/0.99    inference(cnf_transformation,[],[f45])).
% 2.72/0.99  
% 2.72/0.99  fof(f2,axiom,(
% 2.72/0.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f16,plain,(
% 2.72/0.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.72/0.99    inference(ennf_transformation,[],[f2])).
% 2.72/0.99  
% 2.72/0.99  fof(f35,plain,(
% 2.72/0.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.72/0.99    inference(nnf_transformation,[],[f16])).
% 2.72/0.99  
% 2.72/0.99  fof(f51,plain,(
% 2.72/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.72/0.99    inference(cnf_transformation,[],[f35])).
% 2.72/0.99  
% 2.72/0.99  cnf(c_26,negated_conjecture,
% 2.72/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 2.72/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1239,plain,
% 2.72/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_19,plain,
% 2.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.72/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.72/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1246,plain,
% 2.72/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.72/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_2324,plain,
% 2.72/0.99      ( k7_relset_1(sK3,sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
% 2.72/0.99      inference(superposition,[status(thm)],[c_1239,c_1246]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_21,plain,
% 2.72/0.99      ( ~ m1_subset_1(X0,X1)
% 2.72/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 2.72/0.99      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 2.72/0.99      | r2_hidden(sK2(X4,X3,X2,X0),X4)
% 2.72/0.99      | v1_xboole_0(X1)
% 2.72/0.99      | v1_xboole_0(X3)
% 2.72/0.99      | v1_xboole_0(X4) ),
% 2.72/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1244,plain,
% 2.72/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 2.72/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 2.72/0.99      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 2.72/0.99      | r2_hidden(sK2(X4,X3,X2,X0),X4) = iProver_top
% 2.72/0.99      | v1_xboole_0(X1) = iProver_top
% 2.72/0.99      | v1_xboole_0(X3) = iProver_top
% 2.72/0.99      | v1_xboole_0(X4) = iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_3160,plain,
% 2.72/0.99      ( m1_subset_1(X0,sK4) != iProver_top
% 2.72/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 2.72/0.99      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 2.72/0.99      | r2_hidden(sK2(X1,sK3,sK6,X0),X1) = iProver_top
% 2.72/0.99      | v1_xboole_0(X1) = iProver_top
% 2.72/0.99      | v1_xboole_0(sK4) = iProver_top
% 2.72/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 2.72/0.99      inference(superposition,[status(thm)],[c_2324,c_1244]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_29,plain,
% 2.72/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_15,plain,
% 2.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.72/0.99      | v1_relat_1(X0) ),
% 2.72/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1510,plain,
% 2.72/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.72/0.99      | v1_relat_1(sK6) ),
% 2.72/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1511,plain,
% 2.72/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 2.72/0.99      | v1_relat_1(sK6) = iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_1510]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_17,plain,
% 2.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.72/0.99      | ~ v1_xboole_0(X2)
% 2.72/0.99      | v1_xboole_0(X0) ),
% 2.72/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1248,plain,
% 2.72/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.72/0.99      | v1_xboole_0(X2) != iProver_top
% 2.72/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_3201,plain,
% 2.72/0.99      ( v1_xboole_0(sK4) != iProver_top
% 2.72/0.99      | v1_xboole_0(sK6) = iProver_top ),
% 2.72/0.99      inference(superposition,[status(thm)],[c_1239,c_1248]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_16,plain,
% 2.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.72/0.99      | ~ v1_xboole_0(X1)
% 2.72/0.99      | v1_xboole_0(X0) ),
% 2.72/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1249,plain,
% 2.72/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.72/0.99      | v1_xboole_0(X1) != iProver_top
% 2.72/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_3327,plain,
% 2.72/0.99      ( v1_xboole_0(sK3) != iProver_top
% 2.72/0.99      | v1_xboole_0(sK6) = iProver_top ),
% 2.72/0.99      inference(superposition,[status(thm)],[c_1239,c_1249]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_18,plain,
% 2.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.72/0.99      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
% 2.72/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1247,plain,
% 2.72/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.72/0.99      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_2556,plain,
% 2.72/0.99      ( m1_subset_1(k9_relat_1(sK6,X0),k1_zfmisc_1(sK4)) = iProver_top
% 2.72/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
% 2.72/0.99      inference(superposition,[status(thm)],[c_2324,c_1247]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_3032,plain,
% 2.72/0.99      ( m1_subset_1(k9_relat_1(sK6,X0),k1_zfmisc_1(sK4)) = iProver_top ),
% 2.72/0.99      inference(global_propositional_subsumption,
% 2.72/0.99                [status(thm)],
% 2.72/0.99                [c_2556,c_29]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_7,plain,
% 2.72/0.99      ( m1_subset_1(X0,X1)
% 2.72/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.72/0.99      | ~ r2_hidden(X0,X2) ),
% 2.72/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1255,plain,
% 2.72/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 2.72/0.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.72/0.99      | r2_hidden(X0,X2) != iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_3347,plain,
% 2.72/0.99      ( m1_subset_1(X0,sK4) = iProver_top
% 2.72/0.99      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
% 2.72/0.99      inference(superposition,[status(thm)],[c_3032,c_1255]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_11,plain,
% 2.72/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.72/0.99      | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
% 2.72/0.99      | ~ v1_relat_1(X1) ),
% 2.72/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1251,plain,
% 2.72/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.72/0.99      | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 2.72/0.99      | v1_relat_1(X1) != iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_12,plain,
% 2.72/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.72/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 2.72/0.99      | ~ v1_funct_1(X1)
% 2.72/0.99      | ~ v1_relat_1(X1) ),
% 2.72/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_27,negated_conjecture,
% 2.72/0.99      ( v1_funct_1(sK6) ),
% 2.72/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_328,plain,
% 2.72/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.72/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 2.72/0.99      | ~ v1_relat_1(X1)
% 2.72/0.99      | sK6 != X1 ),
% 2.72/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_329,plain,
% 2.72/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 2.72/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6)
% 2.72/0.99      | ~ v1_relat_1(sK6) ),
% 2.72/0.99      inference(unflattening,[status(thm)],[c_328]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1237,plain,
% 2.72/0.99      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 2.72/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
% 2.72/0.99      | v1_relat_1(sK6) != iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_329]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_330,plain,
% 2.72/0.99      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 2.72/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
% 2.72/0.99      | v1_relat_1(sK6) != iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_329]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1567,plain,
% 2.72/0.99      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
% 2.72/0.99      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 2.72/0.99      inference(global_propositional_subsumption,
% 2.72/0.99                [status(thm)],
% 2.72/0.99                [c_1237,c_29,c_330,c_1511]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1568,plain,
% 2.72/0.99      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 2.72/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top ),
% 2.72/0.99      inference(renaming,[status(thm)],[c_1567]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1,plain,
% 2.72/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.72/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1260,plain,
% 2.72/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.72/0.99      | v1_xboole_0(X1) != iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1790,plain,
% 2.72/0.99      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 2.72/0.99      | v1_xboole_0(sK6) != iProver_top ),
% 2.72/0.99      inference(superposition,[status(thm)],[c_1568,c_1260]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_4095,plain,
% 2.72/0.99      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 2.72/0.99      | v1_relat_1(sK6) != iProver_top
% 2.72/0.99      | v1_xboole_0(sK6) != iProver_top ),
% 2.72/0.99      inference(superposition,[status(thm)],[c_1251,c_1790]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_5410,plain,
% 2.72/0.99      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 2.72/0.99      | r2_hidden(sK2(X1,sK3,sK6,X0),X1) = iProver_top
% 2.72/0.99      | v1_xboole_0(X1) = iProver_top ),
% 2.72/0.99      inference(global_propositional_subsumption,
% 2.72/0.99                [status(thm)],
% 2.72/0.99                [c_3160,c_29,c_1511,c_3201,c_3327,c_3347,c_4095]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_25,negated_conjecture,
% 2.72/0.99      ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
% 2.72/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1240,plain,
% 2.72/0.99      ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_2546,plain,
% 2.72/0.99      ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) = iProver_top ),
% 2.72/0.99      inference(demodulation,[status(thm)],[c_2324,c_1240]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_22,plain,
% 2.72/0.99      ( ~ m1_subset_1(X0,X1)
% 2.72/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 2.72/0.99      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 2.72/0.99      | r2_hidden(k4_tarski(sK2(X4,X3,X2,X0),X0),X2)
% 2.72/0.99      | v1_xboole_0(X1)
% 2.72/0.99      | v1_xboole_0(X3)
% 2.72/0.99      | v1_xboole_0(X4) ),
% 2.72/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1243,plain,
% 2.72/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 2.72/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 2.72/0.99      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 2.72/0.99      | r2_hidden(k4_tarski(sK2(X4,X3,X2,X0),X0),X2) = iProver_top
% 2.72/0.99      | v1_xboole_0(X1) = iProver_top
% 2.72/0.99      | v1_xboole_0(X3) = iProver_top
% 2.72/0.99      | v1_xboole_0(X4) = iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_2557,plain,
% 2.72/0.99      ( m1_subset_1(X0,sK4) != iProver_top
% 2.72/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 2.72/0.99      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 2.72/0.99      | r2_hidden(k4_tarski(sK2(X1,sK3,sK6,X0),X0),sK6) = iProver_top
% 2.72/0.99      | v1_xboole_0(X1) = iProver_top
% 2.72/0.99      | v1_xboole_0(sK4) = iProver_top
% 2.72/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 2.72/0.99      inference(superposition,[status(thm)],[c_2324,c_1243]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_5502,plain,
% 2.72/0.99      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 2.72/0.99      | r2_hidden(k4_tarski(sK2(X1,sK3,sK6,X0),X0),sK6) = iProver_top
% 2.72/0.99      | v1_xboole_0(X1) = iProver_top ),
% 2.72/0.99      inference(global_propositional_subsumption,
% 2.72/0.99                [status(thm)],
% 2.72/0.99                [c_2557,c_29,c_1511,c_3201,c_3327,c_3347,c_4095]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_13,plain,
% 2.72/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 2.72/0.99      | ~ v1_funct_1(X2)
% 2.72/0.99      | ~ v1_relat_1(X2)
% 2.72/0.99      | k1_funct_1(X2,X0) = X1 ),
% 2.72/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_343,plain,
% 2.72/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 2.72/0.99      | ~ v1_relat_1(X2)
% 2.72/0.99      | k1_funct_1(X2,X0) = X1
% 2.72/0.99      | sK6 != X2 ),
% 2.72/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_27]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_344,plain,
% 2.72/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),sK6)
% 2.72/0.99      | ~ v1_relat_1(sK6)
% 2.72/0.99      | k1_funct_1(sK6,X0) = X1 ),
% 2.72/0.99      inference(unflattening,[status(thm)],[c_343]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1236,plain,
% 2.72/0.99      ( k1_funct_1(sK6,X0) = X1
% 2.72/0.99      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
% 2.72/0.99      | v1_relat_1(sK6) != iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_344]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_345,plain,
% 2.72/0.99      ( k1_funct_1(sK6,X0) = X1
% 2.72/0.99      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
% 2.72/0.99      | v1_relat_1(sK6) != iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_344]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1523,plain,
% 2.72/0.99      ( r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
% 2.72/0.99      | k1_funct_1(sK6,X0) = X1 ),
% 2.72/0.99      inference(global_propositional_subsumption,
% 2.72/0.99                [status(thm)],
% 2.72/0.99                [c_1236,c_29,c_345,c_1511]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1524,plain,
% 2.72/0.99      ( k1_funct_1(sK6,X0) = X1
% 2.72/0.99      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top ),
% 2.72/0.99      inference(renaming,[status(thm)],[c_1523]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_5515,plain,
% 2.72/0.99      ( k1_funct_1(sK6,sK2(X0,sK3,sK6,X1)) = X1
% 2.72/0.99      | r2_hidden(X1,k9_relat_1(sK6,X0)) != iProver_top
% 2.72/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.72/0.99      inference(superposition,[status(thm)],[c_5502,c_1524]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_6957,plain,
% 2.72/0.99      ( k1_funct_1(sK6,sK2(sK5,sK3,sK6,sK7)) = sK7
% 2.72/0.99      | v1_xboole_0(sK5) = iProver_top ),
% 2.72/0.99      inference(superposition,[status(thm)],[c_2546,c_5515]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_9,plain,
% 2.72/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.72/0.99      | r2_hidden(sK1(X0,X2,X1),X2)
% 2.72/0.99      | ~ v1_relat_1(X1) ),
% 2.72/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1253,plain,
% 2.72/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.72/1.00      | r2_hidden(sK1(X0,X2,X1),X2) = iProver_top
% 2.72/1.00      | v1_relat_1(X1) != iProver_top ),
% 2.72/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.72/1.00  
% 2.72/1.00  cnf(c_3500,plain,
% 2.72/1.00      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.72/1.00      | v1_relat_1(X1) != iProver_top
% 2.72/1.00      | v1_xboole_0(X2) != iProver_top ),
% 2.72/1.00      inference(superposition,[status(thm)],[c_1253,c_1260]) ).
% 2.72/1.00  
% 2.72/1.00  cnf(c_9715,plain,
% 2.72/1.00      ( v1_relat_1(sK6) != iProver_top
% 2.72/1.00      | v1_xboole_0(sK5) != iProver_top ),
% 2.72/1.00      inference(superposition,[status(thm)],[c_2546,c_3500]) ).
% 2.72/1.00  
% 2.72/1.00  cnf(c_9965,plain,
% 2.72/1.00      ( v1_xboole_0(sK5) != iProver_top ),
% 2.72/1.00      inference(global_propositional_subsumption,
% 2.72/1.00                [status(thm)],
% 2.72/1.00                [c_9715,c_29,c_1511]) ).
% 2.72/1.00  
% 2.72/1.00  cnf(c_9970,plain,
% 2.72/1.00      ( k1_funct_1(sK6,sK2(sK5,sK3,sK6,sK7)) = sK7 ),
% 2.72/1.00      inference(superposition,[status(thm)],[c_6957,c_9965]) ).
% 2.72/1.00  
% 2.72/1.00  cnf(c_24,negated_conjecture,
% 2.72/1.00      ( ~ r2_hidden(X0,sK3)
% 2.72/1.00      | ~ r2_hidden(X0,sK5)
% 2.72/1.00      | k1_funct_1(sK6,X0) != sK7 ),
% 2.72/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.72/1.00  
% 2.72/1.00  cnf(c_1241,plain,
% 2.72/1.00      ( k1_funct_1(sK6,X0) != sK7
% 2.72/1.00      | r2_hidden(X0,sK3) != iProver_top
% 2.72/1.00      | r2_hidden(X0,sK5) != iProver_top ),
% 2.72/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.72/1.00  
% 2.72/1.00  cnf(c_11015,plain,
% 2.72/1.00      ( r2_hidden(sK2(sK5,sK3,sK6,sK7),sK3) != iProver_top
% 2.72/1.00      | r2_hidden(sK2(sK5,sK3,sK6,sK7),sK5) != iProver_top ),
% 2.72/1.00      inference(superposition,[status(thm)],[c_9970,c_1241]) ).
% 2.72/1.00  
% 2.72/1.00  cnf(c_23,plain,
% 2.72/1.00      ( ~ m1_subset_1(X0,X1)
% 2.72/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 2.72/1.00      | m1_subset_1(sK2(X4,X3,X2,X0),X3)
% 2.72/1.00      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 2.72/1.00      | v1_xboole_0(X1)
% 2.72/1.00      | v1_xboole_0(X3)
% 2.72/1.00      | v1_xboole_0(X4) ),
% 2.72/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.72/1.00  
% 2.72/1.00  cnf(c_1242,plain,
% 2.72/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 2.72/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 2.72/1.00      | m1_subset_1(sK2(X4,X3,X2,X0),X3) = iProver_top
% 2.72/1.00      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 2.72/1.00      | v1_xboole_0(X1) = iProver_top
% 2.72/1.00      | v1_xboole_0(X3) = iProver_top
% 2.72/1.00      | v1_xboole_0(X4) = iProver_top ),
% 2.72/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.72/1.00  
% 2.72/1.00  cnf(c_1694,plain,
% 2.72/1.00      ( m1_subset_1(sK2(sK5,sK3,sK6,sK7),sK3) = iProver_top
% 2.72/1.00      | m1_subset_1(sK7,sK4) != iProver_top
% 2.72/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 2.72/1.00      | v1_xboole_0(sK4) = iProver_top
% 2.72/1.00      | v1_xboole_0(sK3) = iProver_top
% 2.72/1.00      | v1_xboole_0(sK5) = iProver_top ),
% 2.72/1.00      inference(superposition,[status(thm)],[c_1240,c_1242]) ).
% 2.72/1.00  
% 2.72/1.00  cnf(c_1977,plain,
% 2.72/1.00      ( m1_subset_1(sK7,sK4) != iProver_top
% 2.72/1.00      | m1_subset_1(sK2(sK5,sK3,sK6,sK7),sK3) = iProver_top
% 2.72/1.00      | v1_xboole_0(sK4) = iProver_top
% 2.72/1.00      | v1_xboole_0(sK3) = iProver_top
% 2.72/1.00      | v1_xboole_0(sK5) = iProver_top ),
% 2.72/1.00      inference(global_propositional_subsumption,
% 2.72/1.00                [status(thm)],
% 2.72/1.00                [c_1694,c_29]) ).
% 2.72/1.00  
% 2.72/1.00  cnf(c_1978,plain,
% 2.72/1.00      ( m1_subset_1(sK2(sK5,sK3,sK6,sK7),sK3) = iProver_top
% 2.72/1.00      | m1_subset_1(sK7,sK4) != iProver_top
% 2.72/1.00      | v1_xboole_0(sK4) = iProver_top
% 2.72/1.00      | v1_xboole_0(sK3) = iProver_top
% 2.72/1.00      | v1_xboole_0(sK5) = iProver_top ),
% 2.72/1.00      inference(renaming,[status(thm)],[c_1977]) ).
% 2.72/1.00  
% 2.72/1.00  cnf(c_5,plain,
% 2.72/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.72/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.72/1.00  
% 2.72/1.00  cnf(c_1257,plain,
% 2.72/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 2.72/1.00      | r2_hidden(X0,X1) = iProver_top
% 2.72/1.00      | v1_xboole_0(X1) = iProver_top ),
% 2.72/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.72/1.00  
% 2.72/1.00  cnf(c_1986,plain,
% 2.72/1.00      ( m1_subset_1(sK7,sK4) != iProver_top
% 2.72/1.00      | r2_hidden(sK2(sK5,sK3,sK6,sK7),sK3) = iProver_top
% 2.72/1.00      | v1_xboole_0(sK4) = iProver_top
% 2.72/1.00      | v1_xboole_0(sK3) = iProver_top
% 2.72/1.00      | v1_xboole_0(sK5) = iProver_top ),
% 2.72/1.00      inference(superposition,[status(thm)],[c_1978,c_1257]) ).
% 2.72/1.00  
% 2.72/1.00  cnf(c_6072,plain,
% 2.72/1.00      ( m1_subset_1(sK7,sK4) = iProver_top ),
% 2.72/1.00      inference(superposition,[status(thm)],[c_2546,c_3347]) ).
% 2.72/1.00  
% 2.72/1.00  cnf(c_5511,plain,
% 2.72/1.00      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 2.72/1.00      | v1_xboole_0(X1) = iProver_top
% 2.72/1.00      | v1_xboole_0(sK6) != iProver_top ),
% 2.72/1.00      inference(superposition,[status(thm)],[c_5502,c_1260]) ).
% 2.72/1.00  
% 2.72/1.00  cnf(c_8171,plain,
% 2.72/1.00      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 2.72/1.00      | v1_xboole_0(sK6) != iProver_top ),
% 2.72/1.00      inference(global_propositional_subsumption,
% 2.72/1.00                [status(thm)],
% 2.72/1.00                [c_5511,c_29,c_1511,c_4095]) ).
% 2.72/1.00  
% 2.72/1.00  cnf(c_8182,plain,
% 2.72/1.00      ( v1_xboole_0(sK6) != iProver_top ),
% 2.72/1.00      inference(superposition,[status(thm)],[c_2546,c_8171]) ).
% 2.72/1.00  
% 2.72/1.00  cnf(c_11125,plain,
% 2.72/1.00      ( r2_hidden(sK2(sK5,sK3,sK6,sK7),sK5) != iProver_top ),
% 2.72/1.00      inference(global_propositional_subsumption,
% 2.72/1.00                [status(thm)],
% 2.72/1.00                [c_11015,c_29,c_1511,c_1986,c_3201,c_3327,c_6072,c_8182,
% 2.72/1.00                 c_9715]) ).
% 2.72/1.00  
% 2.72/1.00  cnf(c_11130,plain,
% 2.72/1.00      ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
% 2.72/1.00      | v1_xboole_0(sK5) = iProver_top ),
% 2.72/1.00      inference(superposition,[status(thm)],[c_5410,c_11125]) ).
% 2.72/1.00  
% 2.72/1.00  cnf(contradiction,plain,
% 2.72/1.00      ( $false ),
% 2.72/1.00      inference(minisat,[status(thm)],[c_11130,c_9715,c_2546,c_1511,c_29]) ).
% 2.72/1.00  
% 2.72/1.00  
% 2.72/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.72/1.00  
% 2.72/1.00  ------                               Statistics
% 2.72/1.00  
% 2.72/1.00  ------ General
% 2.72/1.00  
% 2.72/1.00  abstr_ref_over_cycles:                  0
% 2.72/1.00  abstr_ref_under_cycles:                 0
% 2.72/1.00  gc_basic_clause_elim:                   0
% 2.72/1.00  forced_gc_time:                         0
% 2.72/1.00  parsing_time:                           0.008
% 2.72/1.00  unif_index_cands_time:                  0.
% 2.72/1.00  unif_index_add_time:                    0.
% 2.72/1.00  orderings_time:                         0.
% 2.72/1.00  out_proof_time:                         0.009
% 2.72/1.00  total_time:                             0.34
% 2.72/1.00  num_of_symbols:                         51
% 2.72/1.00  num_of_terms:                           10944
% 2.72/1.00  
% 2.72/1.00  ------ Preprocessing
% 2.72/1.00  
% 2.72/1.00  num_of_splits:                          0
% 2.72/1.00  num_of_split_atoms:                     0
% 2.72/1.00  num_of_reused_defs:                     0
% 2.72/1.00  num_eq_ax_congr_red:                    38
% 2.72/1.00  num_of_sem_filtered_clauses:            1
% 2.72/1.00  num_of_subtypes:                        0
% 2.72/1.00  monotx_restored_types:                  0
% 2.72/1.00  sat_num_of_epr_types:                   0
% 2.72/1.00  sat_num_of_non_cyclic_types:            0
% 2.72/1.00  sat_guarded_non_collapsed_types:        0
% 2.72/1.00  num_pure_diseq_elim:                    0
% 2.72/1.00  simp_replaced_by:                       0
% 2.72/1.00  res_preprocessed:                       128
% 2.72/1.00  prep_upred:                             0
% 2.72/1.00  prep_unflattend:                        17
% 2.72/1.00  smt_new_axioms:                         0
% 2.72/1.00  pred_elim_cands:                        4
% 2.72/1.00  pred_elim:                              1
% 2.72/1.00  pred_elim_cl:                           1
% 2.72/1.00  pred_elim_cycles:                       3
% 2.72/1.00  merged_defs:                            0
% 2.72/1.00  merged_defs_ncl:                        0
% 2.72/1.00  bin_hyper_res:                          0
% 2.72/1.00  prep_cycles:                            4
% 2.72/1.00  pred_elim_time:                         0.005
% 2.72/1.00  splitting_time:                         0.
% 2.72/1.00  sem_filter_time:                        0.
% 2.72/1.00  monotx_time:                            0.
% 2.72/1.00  subtype_inf_time:                       0.
% 2.72/1.00  
% 2.72/1.00  ------ Problem properties
% 2.72/1.00  
% 2.72/1.00  clauses:                                26
% 2.72/1.00  conjectures:                            3
% 2.72/1.00  epr:                                    5
% 2.72/1.00  horn:                                   20
% 2.72/1.00  ground:                                 2
% 2.72/1.00  unary:                                  2
% 2.72/1.00  binary:                                 6
% 2.72/1.00  lits:                                   88
% 2.72/1.00  lits_eq:                                3
% 2.72/1.00  fd_pure:                                0
% 2.72/1.00  fd_pseudo:                              0
% 2.72/1.00  fd_cond:                                0
% 2.72/1.00  fd_pseudo_cond:                         1
% 2.72/1.00  ac_symbols:                             0
% 2.72/1.00  
% 2.72/1.00  ------ Propositional Solver
% 2.72/1.00  
% 2.72/1.00  prop_solver_calls:                      29
% 2.72/1.00  prop_fast_solver_calls:                 1366
% 2.72/1.00  smt_solver_calls:                       0
% 2.72/1.00  smt_fast_solver_calls:                  0
% 2.72/1.00  prop_num_of_clauses:                    4002
% 2.72/1.00  prop_preprocess_simplified:             9205
% 2.72/1.00  prop_fo_subsumed:                       52
% 2.72/1.00  prop_solver_time:                       0.
% 2.72/1.00  smt_solver_time:                        0.
% 2.72/1.00  smt_fast_solver_time:                   0.
% 2.72/1.00  prop_fast_solver_time:                  0.
% 2.72/1.00  prop_unsat_core_time:                   0.
% 2.72/1.00  
% 2.72/1.00  ------ QBF
% 2.72/1.00  
% 2.72/1.00  qbf_q_res:                              0
% 2.72/1.00  qbf_num_tautologies:                    0
% 2.72/1.00  qbf_prep_cycles:                        0
% 2.72/1.00  
% 2.72/1.00  ------ BMC1
% 2.72/1.00  
% 2.72/1.00  bmc1_current_bound:                     -1
% 2.72/1.00  bmc1_last_solved_bound:                 -1
% 2.72/1.00  bmc1_unsat_core_size:                   -1
% 2.72/1.00  bmc1_unsat_core_parents_size:           -1
% 2.72/1.00  bmc1_merge_next_fun:                    0
% 2.72/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.72/1.00  
% 2.72/1.00  ------ Instantiation
% 2.72/1.00  
% 2.72/1.00  inst_num_of_clauses:                    960
% 2.72/1.00  inst_num_in_passive:                    250
% 2.72/1.00  inst_num_in_active:                     404
% 2.72/1.00  inst_num_in_unprocessed:                306
% 2.72/1.00  inst_num_of_loops:                      520
% 2.72/1.00  inst_num_of_learning_restarts:          0
% 2.72/1.00  inst_num_moves_active_passive:          112
% 2.72/1.00  inst_lit_activity:                      0
% 2.72/1.00  inst_lit_activity_moves:                0
% 2.72/1.00  inst_num_tautologies:                   0
% 2.72/1.00  inst_num_prop_implied:                  0
% 2.72/1.00  inst_num_existing_simplified:           0
% 2.72/1.00  inst_num_eq_res_simplified:             0
% 2.72/1.00  inst_num_child_elim:                    0
% 2.72/1.00  inst_num_of_dismatching_blockings:      548
% 2.72/1.00  inst_num_of_non_proper_insts:           997
% 2.72/1.00  inst_num_of_duplicates:                 0
% 2.72/1.00  inst_inst_num_from_inst_to_res:         0
% 2.72/1.00  inst_dismatching_checking_time:         0.
% 2.72/1.00  
% 2.72/1.00  ------ Resolution
% 2.72/1.00  
% 2.72/1.00  res_num_of_clauses:                     0
% 2.72/1.00  res_num_in_passive:                     0
% 2.72/1.00  res_num_in_active:                      0
% 2.72/1.00  res_num_of_loops:                       132
% 2.72/1.00  res_forward_subset_subsumed:            38
% 2.72/1.00  res_backward_subset_subsumed:           0
% 2.72/1.00  res_forward_subsumed:                   0
% 2.72/1.00  res_backward_subsumed:                  0
% 2.72/1.00  res_forward_subsumption_resolution:     0
% 2.72/1.00  res_backward_subsumption_resolution:    0
% 2.72/1.00  res_clause_to_clause_subsumption:       1092
% 2.72/1.00  res_orphan_elimination:                 0
% 2.72/1.00  res_tautology_del:                      58
% 2.72/1.00  res_num_eq_res_simplified:              0
% 2.72/1.00  res_num_sel_changes:                    0
% 2.72/1.00  res_moves_from_active_to_pass:          0
% 2.72/1.00  
% 2.72/1.00  ------ Superposition
% 2.72/1.00  
% 2.72/1.00  sup_time_total:                         0.
% 2.72/1.00  sup_time_generating:                    0.
% 2.72/1.00  sup_time_sim_full:                      0.
% 2.72/1.00  sup_time_sim_immed:                     0.
% 2.72/1.00  
% 2.72/1.00  sup_num_of_clauses:                     216
% 2.72/1.00  sup_num_in_active:                      95
% 2.72/1.00  sup_num_in_passive:                     121
% 2.72/1.00  sup_num_of_loops:                       102
% 2.72/1.00  sup_fw_superposition:                   120
% 2.72/1.00  sup_bw_superposition:                   156
% 2.72/1.00  sup_immediate_simplified:               42
% 2.72/1.00  sup_given_eliminated:                   1
% 2.72/1.00  comparisons_done:                       0
% 2.72/1.00  comparisons_avoided:                    0
% 2.72/1.00  
% 2.72/1.00  ------ Simplifications
% 2.72/1.00  
% 2.72/1.00  
% 2.72/1.00  sim_fw_subset_subsumed:                 25
% 2.72/1.00  sim_bw_subset_subsumed:                 8
% 2.72/1.00  sim_fw_subsumed:                        10
% 2.72/1.00  sim_bw_subsumed:                        3
% 2.72/1.00  sim_fw_subsumption_res:                 3
% 2.72/1.00  sim_bw_subsumption_res:                 0
% 2.72/1.00  sim_tautology_del:                      20
% 2.72/1.00  sim_eq_tautology_del:                   1
% 2.72/1.00  sim_eq_res_simp:                        0
% 2.72/1.00  sim_fw_demodulated:                     0
% 2.72/1.00  sim_bw_demodulated:                     3
% 2.72/1.00  sim_light_normalised:                   6
% 2.72/1.00  sim_joinable_taut:                      0
% 2.72/1.00  sim_joinable_simp:                      0
% 2.72/1.00  sim_ac_normalised:                      0
% 2.72/1.00  sim_smt_subsumption:                    0
% 2.72/1.00  
%------------------------------------------------------------------------------
