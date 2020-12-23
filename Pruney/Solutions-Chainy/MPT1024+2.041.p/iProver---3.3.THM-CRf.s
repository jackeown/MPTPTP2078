%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:55 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :  183 (1279 expanded)
%              Number of clauses        :  104 ( 398 expanded)
%              Number of leaves         :   21 ( 282 expanded)
%              Depth                    :   21
%              Number of atoms          :  673 (6059 expanded)
%              Number of equality atoms :  219 (1132 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f16,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK9
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X5,X0) )
        & r2_hidden(sK9,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
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
              ( k1_funct_1(sK8,X5) != X4
              | ~ r2_hidden(X5,sK7)
              | ~ r2_hidden(X5,sK5) )
          & r2_hidden(X4,k7_relset_1(sK5,sK6,sK8,sK7)) )
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ! [X5] :
        ( k1_funct_1(sK8,X5) != sK9
        | ~ r2_hidden(X5,sK7)
        | ~ r2_hidden(X5,sK5) )
    & r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f32,f53,f52])).

fof(f80,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f54])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f56,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f36])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f30])).

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
     => ( r2_hidden(sK4(X1,X2,X3,X4),X1)
        & r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3)
        & m1_subset_1(sK4(X1,X2,X3,X4),X2) ) ) ),
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
                        & ( ( r2_hidden(sK4(X1,X2,X3,X4),X1)
                            & r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3)
                            & m1_subset_1(sK4(X1,X2,X3,X4),X2) )
                          | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f49,f50])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK4(X1,X2,X3,X4),X2)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(cnf_transformation,[],[f54])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f55,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK4(X1,X2,X3,X4),X1)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

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
    inference(nnf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f79,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f54])).

fof(f82,plain,(
    ! [X5] :
      ( k1_funct_1(sK8,X5) != sK9
      | ~ r2_hidden(X5,sK7)
      | ~ r2_hidden(X5,sK5) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X5] :
              ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
              & r2_hidden(X5,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(rectify,[],[f43])).

fof(f46,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK3(X1,X2),X6),X2)
        & r2_hidden(sK3(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK3(X1,X2),X6),X2)
            & r2_hidden(sK3(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f44,f46,f45])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X1,X0,X2) = X1
      | r2_hidden(sK3(X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f83,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f67])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1034,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1044,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2084,plain,
    ( k7_relset_1(sK5,sK6,sK8,X0) = k9_relat_1(sK8,X0) ),
    inference(superposition,[status(thm)],[c_1034,c_1044])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1057,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | m1_subset_1(sK4(X4,X3,X2,X0),X3)
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1037,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(sK4(X4,X3,X2,X0),X3) = iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1569,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(sK4(X3,X1,X0,sK0(k7_relset_1(X1,X2,X0,X3))),X1) = iProver_top
    | m1_subset_1(sK0(k7_relset_1(X1,X2,X0,X3)),X2) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k7_relset_1(X1,X2,X0,X3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1057,c_1037])).

cnf(c_6836,plain,
    ( m1_subset_1(sK4(X0,sK5,sK8,sK0(k7_relset_1(sK5,sK6,sK8,X0))),sK5) = iProver_top
    | m1_subset_1(sK0(k9_relat_1(sK8,X0)),sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k7_relset_1(sK5,sK6,sK8,X0)) = iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2084,c_1569])).

cnf(c_6844,plain,
    ( m1_subset_1(sK4(X0,sK5,sK8,sK0(k9_relat_1(sK8,X0))),sK5) = iProver_top
    | m1_subset_1(sK0(k9_relat_1(sK8,X0)),sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k9_relat_1(sK8,X0)) = iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6836,c_2084])).

cnf(c_29,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_30,plain,
    ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1513,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK5,sK6))
    | v1_relat_1(sK8) ),
    inference(resolution,[status(thm)],[c_4,c_26])).

cnf(c_1514,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) != iProver_top
    | v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1513])).

cnf(c_5,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1608,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1609,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1608])).

cnf(c_3,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1520,plain,
    ( m1_subset_1(X0,sK6)
    | ~ m1_subset_1(k7_relset_1(sK5,sK6,sK8,X1),k1_zfmisc_1(sK6))
    | ~ r2_hidden(X0,k7_relset_1(sK5,sK6,sK8,X1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1721,plain,
    ( ~ m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6))
    | m1_subset_1(sK9,sK6)
    | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_1520])).

cnf(c_1722,plain,
    ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6)) != iProver_top
    | m1_subset_1(sK9,sK6) = iProver_top
    | r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1721])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1382,plain,
    ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,X0),k1_zfmisc_1(sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1926,plain,
    ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_1382])).

cnf(c_1927,plain,
    ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6)) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1926])).

cnf(c_1035,plain,
    ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1563,plain,
    ( m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
    | m1_subset_1(sK9,sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1035,c_1037])).

cnf(c_1886,plain,
    ( m1_subset_1(sK9,sK6) != iProver_top
    | m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1563,c_29])).

cnf(c_1887,plain,
    ( m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
    | m1_subset_1(sK9,sK6) != iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_1886])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1055,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1895,plain,
    ( m1_subset_1(sK9,sK6) != iProver_top
    | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1887,c_1055])).

cnf(c_1958,plain,
    ( r2_hidden(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1895,c_29,c_30,c_1722,c_1927])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1047,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2208,plain,
    ( v1_xboole_0(sK6) != iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1034,c_1047])).

cnf(c_2324,plain,
    ( r2_hidden(sK9,k9_relat_1(sK8,sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2084,c_1035])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2676,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),sK7)
    | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2677,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),sK7) = iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2676])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2674,plain,
    ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8)
    | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2681,plain,
    ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2674])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3585,plain,
    ( ~ r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8)
    | ~ v1_xboole_0(sK8) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3586,plain,
    ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) != iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3585])).

cnf(c_3715,plain,
    ( ~ r2_hidden(sK1(sK9,sK7,sK8),sK7)
    | ~ v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3716,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),sK7) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3715])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | r2_hidden(sK4(X4,X3,X2,X0),X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3887,plain,
    ( ~ m1_subset_1(sK9,sK6)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7)
    | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
    | v1_xboole_0(sK6)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_3888,plain,
    ( m1_subset_1(sK9,sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7) = iProver_top
    | r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3887])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | r2_hidden(k4_tarski(sK4(X4,X3,X2,X0),X0),X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1038,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | r2_hidden(k4_tarski(sK4(X4,X3,X2,X0),X0),X2) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2050,plain,
    ( m1_subset_1(sK9,sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | r2_hidden(k4_tarski(sK4(sK7,sK5,sK8,sK9),sK9),sK8) = iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1035,c_1038])).

cnf(c_2585,plain,
    ( r2_hidden(k4_tarski(sK4(sK7,sK5,sK8,sK9),sK9),sK8) = iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2050,c_29,c_30,c_1722,c_1927])).

cnf(c_11,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_345,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_27])).

cnf(c_346,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK8)
    | ~ v1_relat_1(sK8)
    | k1_funct_1(sK8,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_1031,plain,
    ( k1_funct_1(sK8,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_346])).

cnf(c_2595,plain,
    ( k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) = sK9
    | v1_relat_1(sK8) != iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2585,c_1031])).

cnf(c_4065,plain,
    ( v1_xboole_0(sK5) = iProver_top
    | k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) = sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2595,c_1514,c_1609,c_2208,c_2324,c_2677,c_2681,c_3586,c_3716])).

cnf(c_4066,plain,
    ( k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) = sK9
    | v1_xboole_0(sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_4065])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | ~ r2_hidden(X0,sK7)
    | k1_funct_1(sK8,X0) != sK9 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_7418,plain,
    ( ~ r2_hidden(sK4(sK7,sK5,sK8,sK9),sK5)
    | ~ r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7)
    | k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) != sK9 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_7419,plain,
    ( k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) != sK9
    | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK5) != iProver_top
    | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7418])).

cnf(c_7461,plain,
    ( v1_xboole_0(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6844,c_29,c_30,c_1514,c_1609,c_1722,c_1927,c_1958,c_2208,c_2324,c_2677,c_2681,c_3586,c_3716,c_3888,c_4066,c_7419])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(sK3(X1,X0),X1)
    | k1_relset_1(X1,X2,X0) = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1041,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(sK3(X0,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3111,plain,
    ( k1_relset_1(sK5,sK6,sK8) = sK5
    | r2_hidden(sK3(sK5,sK8),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1034,c_1041])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1045,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1673,plain,
    ( k1_relset_1(sK5,sK6,sK8) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_1034,c_1045])).

cnf(c_3114,plain,
    ( k1_relat_1(sK8) = sK5
    | r2_hidden(sK3(sK5,sK8),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3111,c_1673])).

cnf(c_1056,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3917,plain,
    ( k1_relat_1(sK8) = sK5
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3114,c_1056])).

cnf(c_7466,plain,
    ( k1_relat_1(sK8) = sK5 ),
    inference(superposition,[status(thm)],[c_7461,c_3917])).

cnf(c_1049,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3279,plain,
    ( k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0
    | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1049,c_1031])).

cnf(c_3612,plain,
    ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3279,c_1514,c_1609])).

cnf(c_3613,plain,
    ( k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0
    | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3612])).

cnf(c_3623,plain,
    ( k1_funct_1(sK8,sK1(sK9,sK7,sK8)) = sK9 ),
    inference(superposition,[status(thm)],[c_2324,c_3613])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_330,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_27])).

cnf(c_331,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8)
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_330])).

cnf(c_1032,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_331])).

cnf(c_3652,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3623,c_1032])).

cnf(c_3773,plain,
    ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3652,c_1514,c_1609,c_2324,c_2681])).

cnf(c_12,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_315,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_316,plain,
    ( r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(k4_tarski(X0,X1),sK8)
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_1033,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_316])).

cnf(c_3779,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3773,c_1033])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2675,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8))
    | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2679,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) = iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2675])).

cnf(c_3904,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3779,c_1514,c_1609,c_2324,c_2679])).

cnf(c_3909,plain,
    ( v1_xboole_0(k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3904,c_1056])).

cnf(c_7720,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7466,c_3909])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7720,c_7461])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:27:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.50/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/0.99  
% 3.50/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.50/0.99  
% 3.50/0.99  ------  iProver source info
% 3.50/0.99  
% 3.50/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.50/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.50/0.99  git: non_committed_changes: false
% 3.50/0.99  git: last_make_outside_of_git: false
% 3.50/0.99  
% 3.50/0.99  ------ 
% 3.50/0.99  ------ Parsing...
% 3.50/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.50/0.99  
% 3.50/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.50/0.99  
% 3.50/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.50/0.99  
% 3.50/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.50/0.99  ------ Proving...
% 3.50/0.99  ------ Problem Properties 
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  clauses                                 27
% 3.50/0.99  conjectures                             3
% 3.50/0.99  EPR                                     2
% 3.50/0.99  Horn                                    20
% 3.50/0.99  unary                                   3
% 3.50/0.99  binary                                  5
% 3.50/0.99  lits                                    91
% 3.50/0.99  lits eq                                 7
% 3.50/0.99  fd_pure                                 0
% 3.50/0.99  fd_pseudo                               0
% 3.50/0.99  fd_cond                                 0
% 3.50/0.99  fd_pseudo_cond                          1
% 3.50/0.99  AC symbols                              0
% 3.50/0.99  
% 3.50/0.99  ------ Input Options Time Limit: Unbounded
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  ------ 
% 3.50/0.99  Current options:
% 3.50/0.99  ------ 
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  ------ Proving...
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  % SZS status Theorem for theBenchmark.p
% 3.50/0.99  
% 3.50/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.50/0.99  
% 3.50/0.99  fof(f14,conjecture,(
% 3.50/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f15,negated_conjecture,(
% 3.50/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.50/0.99    inference(negated_conjecture,[],[f14])).
% 3.50/0.99  
% 3.50/0.99  fof(f16,plain,(
% 3.50/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.50/0.99    inference(pure_predicate_removal,[],[f15])).
% 3.50/0.99  
% 3.50/0.99  fof(f31,plain,(
% 3.50/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 3.50/0.99    inference(ennf_transformation,[],[f16])).
% 3.50/0.99  
% 3.50/0.99  fof(f32,plain,(
% 3.50/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 3.50/0.99    inference(flattening,[],[f31])).
% 3.50/0.99  
% 3.50/0.99  fof(f53,plain,(
% 3.50/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK9 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(sK9,k7_relset_1(X0,X1,X3,X2)))) )),
% 3.50/0.99    introduced(choice_axiom,[])).
% 3.50/0.99  
% 3.50/0.99  fof(f52,plain,(
% 3.50/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK8,X5) != X4 | ~r2_hidden(X5,sK7) | ~r2_hidden(X5,sK5)) & r2_hidden(X4,k7_relset_1(sK5,sK6,sK8,sK7))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_1(sK8))),
% 3.50/0.99    introduced(choice_axiom,[])).
% 3.50/0.99  
% 3.50/0.99  fof(f54,plain,(
% 3.50/0.99    (! [X5] : (k1_funct_1(sK8,X5) != sK9 | ~r2_hidden(X5,sK7) | ~r2_hidden(X5,sK5)) & r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_1(sK8)),
% 3.50/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f32,f53,f52])).
% 3.50/0.99  
% 3.50/0.99  fof(f80,plain,(
% 3.50/0.99    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 3.50/0.99    inference(cnf_transformation,[],[f54])).
% 3.50/0.99  
% 3.50/0.99  fof(f11,axiom,(
% 3.50/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f28,plain,(
% 3.50/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.50/0.99    inference(ennf_transformation,[],[f11])).
% 3.50/0.99  
% 3.50/0.99  fof(f71,plain,(
% 3.50/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f28])).
% 3.50/0.99  
% 3.50/0.99  fof(f1,axiom,(
% 3.50/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f33,plain,(
% 3.50/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.50/0.99    inference(nnf_transformation,[],[f1])).
% 3.50/0.99  
% 3.50/0.99  fof(f34,plain,(
% 3.50/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.50/0.99    inference(rectify,[],[f33])).
% 3.50/0.99  
% 3.50/0.99  fof(f35,plain,(
% 3.50/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.50/0.99    introduced(choice_axiom,[])).
% 3.50/0.99  
% 3.50/0.99  fof(f36,plain,(
% 3.50/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.50/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 3.50/0.99  
% 3.50/0.99  fof(f56,plain,(
% 3.50/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f36])).
% 3.50/0.99  
% 3.50/0.99  fof(f13,axiom,(
% 3.50/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f30,plain,(
% 3.50/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.50/0.99    inference(ennf_transformation,[],[f13])).
% 3.50/0.99  
% 3.50/0.99  fof(f48,plain,(
% 3.50/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.50/0.99    inference(nnf_transformation,[],[f30])).
% 3.50/0.99  
% 3.50/0.99  fof(f49,plain,(
% 3.50/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.50/0.99    inference(rectify,[],[f48])).
% 3.50/0.99  
% 3.50/0.99  fof(f50,plain,(
% 3.50/0.99    ! [X4,X3,X2,X1] : (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) => (r2_hidden(sK4(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK4(X1,X2,X3,X4),X2)))),
% 3.50/0.99    introduced(choice_axiom,[])).
% 3.50/0.99  
% 3.50/0.99  fof(f51,plain,(
% 3.50/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & ((r2_hidden(sK4(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK4(X1,X2,X3,X4),X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.50/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f49,f50])).
% 3.50/0.99  
% 3.50/0.99  fof(f75,plain,(
% 3.50/0.99    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK4(X1,X2,X3,X4),X2) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f51])).
% 3.50/0.99  
% 3.50/0.99  fof(f81,plain,(
% 3.50/0.99    r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))),
% 3.50/0.99    inference(cnf_transformation,[],[f54])).
% 3.50/0.99  
% 3.50/0.99  fof(f4,axiom,(
% 3.50/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f21,plain,(
% 3.50/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.50/0.99    inference(ennf_transformation,[],[f4])).
% 3.50/0.99  
% 3.50/0.99  fof(f59,plain,(
% 3.50/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f21])).
% 3.50/0.99  
% 3.50/0.99  fof(f5,axiom,(
% 3.50/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f60,plain,(
% 3.50/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f5])).
% 3.50/0.99  
% 3.50/0.99  fof(f3,axiom,(
% 3.50/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f19,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.50/0.99    inference(ennf_transformation,[],[f3])).
% 3.50/0.99  
% 3.50/0.99  fof(f20,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.50/0.99    inference(flattening,[],[f19])).
% 3.50/0.99  
% 3.50/0.99  fof(f58,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f20])).
% 3.50/0.99  
% 3.50/0.99  fof(f9,axiom,(
% 3.50/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f26,plain,(
% 3.50/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.50/0.99    inference(ennf_transformation,[],[f9])).
% 3.50/0.99  
% 3.50/0.99  fof(f69,plain,(
% 3.50/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f26])).
% 3.50/0.99  
% 3.50/0.99  fof(f2,axiom,(
% 3.50/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f17,plain,(
% 3.50/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.50/0.99    inference(ennf_transformation,[],[f2])).
% 3.50/0.99  
% 3.50/0.99  fof(f18,plain,(
% 3.50/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.50/0.99    inference(flattening,[],[f17])).
% 3.50/0.99  
% 3.50/0.99  fof(f57,plain,(
% 3.50/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f18])).
% 3.50/0.99  
% 3.50/0.99  fof(f8,axiom,(
% 3.50/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f25,plain,(
% 3.50/0.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.50/0.99    inference(ennf_transformation,[],[f8])).
% 3.50/0.99  
% 3.50/0.99  fof(f68,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f25])).
% 3.50/0.99  
% 3.50/0.99  fof(f6,axiom,(
% 3.50/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f22,plain,(
% 3.50/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.50/0.99    inference(ennf_transformation,[],[f6])).
% 3.50/0.99  
% 3.50/0.99  fof(f37,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.50/0.99    inference(nnf_transformation,[],[f22])).
% 3.50/0.99  
% 3.50/0.99  fof(f38,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.50/0.99    inference(rectify,[],[f37])).
% 3.50/0.99  
% 3.50/0.99  fof(f39,plain,(
% 3.50/0.99    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 3.50/0.99    introduced(choice_axiom,[])).
% 3.50/0.99  
% 3.50/0.99  fof(f40,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.50/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).
% 3.50/0.99  
% 3.50/0.99  fof(f63,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f40])).
% 3.50/0.99  
% 3.50/0.99  fof(f62,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f40])).
% 3.50/0.99  
% 3.50/0.99  fof(f55,plain,(
% 3.50/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f36])).
% 3.50/0.99  
% 3.50/0.99  fof(f77,plain,(
% 3.50/0.99    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK4(X1,X2,X3,X4),X1) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f51])).
% 3.50/0.99  
% 3.50/0.99  fof(f76,plain,(
% 3.50/0.99    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f51])).
% 3.50/0.99  
% 3.50/0.99  fof(f7,axiom,(
% 3.50/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f23,plain,(
% 3.50/0.99    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.50/0.99    inference(ennf_transformation,[],[f7])).
% 3.50/0.99  
% 3.50/0.99  fof(f24,plain,(
% 3.50/0.99    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.50/0.99    inference(flattening,[],[f23])).
% 3.50/0.99  
% 3.50/0.99  fof(f41,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.50/0.99    inference(nnf_transformation,[],[f24])).
% 3.50/0.99  
% 3.50/0.99  fof(f42,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.50/0.99    inference(flattening,[],[f41])).
% 3.50/0.99  
% 3.50/0.99  fof(f66,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f42])).
% 3.50/0.99  
% 3.50/0.99  fof(f79,plain,(
% 3.50/0.99    v1_funct_1(sK8)),
% 3.50/0.99    inference(cnf_transformation,[],[f54])).
% 3.50/0.99  
% 3.50/0.99  fof(f82,plain,(
% 3.50/0.99    ( ! [X5] : (k1_funct_1(sK8,X5) != sK9 | ~r2_hidden(X5,sK7) | ~r2_hidden(X5,sK5)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f54])).
% 3.50/0.99  
% 3.50/0.99  fof(f12,axiom,(
% 3.50/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f29,plain,(
% 3.50/0.99    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.50/0.99    inference(ennf_transformation,[],[f12])).
% 3.50/0.99  
% 3.50/0.99  fof(f43,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.50/0.99    inference(nnf_transformation,[],[f29])).
% 3.50/0.99  
% 3.50/0.99  fof(f44,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.50/0.99    inference(rectify,[],[f43])).
% 3.50/0.99  
% 3.50/0.99  fof(f46,plain,(
% 3.50/0.99    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK3(X1,X2),X6),X2) & r2_hidden(sK3(X1,X2),X1)))),
% 3.50/0.99    introduced(choice_axiom,[])).
% 3.50/0.99  
% 3.50/0.99  fof(f45,plain,(
% 3.50/0.99    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2))),
% 3.50/0.99    introduced(choice_axiom,[])).
% 3.50/0.99  
% 3.50/0.99  fof(f47,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK3(X1,X2),X6),X2) & r2_hidden(sK3(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.50/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f44,f46,f45])).
% 3.50/0.99  
% 3.50/0.99  fof(f72,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X1,X0,X2) = X1 | r2_hidden(sK3(X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f47])).
% 3.50/0.99  
% 3.50/0.99  fof(f10,axiom,(
% 3.50/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f27,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.50/0.99    inference(ennf_transformation,[],[f10])).
% 3.50/0.99  
% 3.50/0.99  fof(f70,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f27])).
% 3.50/0.99  
% 3.50/0.99  fof(f67,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f42])).
% 3.50/0.99  
% 3.50/0.99  fof(f83,plain,(
% 3.50/0.99    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.50/0.99    inference(equality_resolution,[],[f67])).
% 3.50/0.99  
% 3.50/0.99  fof(f65,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f42])).
% 3.50/0.99  
% 3.50/0.99  fof(f61,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f40])).
% 3.50/0.99  
% 3.50/0.99  cnf(c_26,negated_conjecture,
% 3.50/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.50/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1034,plain,
% 3.50/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_16,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.50/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1044,plain,
% 3.50/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.50/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2084,plain,
% 3.50/0.99      ( k7_relset_1(sK5,sK6,sK8,X0) = k9_relat_1(sK8,X0) ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1034,c_1044]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_0,plain,
% 3.50/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1057,plain,
% 3.50/0.99      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.50/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_23,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,X1)
% 3.50/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 3.50/0.99      | m1_subset_1(sK4(X4,X3,X2,X0),X3)
% 3.50/0.99      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 3.50/0.99      | v1_xboole_0(X1)
% 3.50/0.99      | v1_xboole_0(X3)
% 3.50/0.99      | v1_xboole_0(X4) ),
% 3.50/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1037,plain,
% 3.50/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 3.50/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 3.50/0.99      | m1_subset_1(sK4(X4,X3,X2,X0),X3) = iProver_top
% 3.50/0.99      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 3.50/0.99      | v1_xboole_0(X1) = iProver_top
% 3.50/0.99      | v1_xboole_0(X3) = iProver_top
% 3.50/0.99      | v1_xboole_0(X4) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1569,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.50/0.99      | m1_subset_1(sK4(X3,X1,X0,sK0(k7_relset_1(X1,X2,X0,X3))),X1) = iProver_top
% 3.50/0.99      | m1_subset_1(sK0(k7_relset_1(X1,X2,X0,X3)),X2) != iProver_top
% 3.50/0.99      | v1_xboole_0(X2) = iProver_top
% 3.50/0.99      | v1_xboole_0(X3) = iProver_top
% 3.50/0.99      | v1_xboole_0(X1) = iProver_top
% 3.50/0.99      | v1_xboole_0(k7_relset_1(X1,X2,X0,X3)) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1057,c_1037]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6836,plain,
% 3.50/0.99      ( m1_subset_1(sK4(X0,sK5,sK8,sK0(k7_relset_1(sK5,sK6,sK8,X0))),sK5) = iProver_top
% 3.50/0.99      | m1_subset_1(sK0(k9_relat_1(sK8,X0)),sK6) != iProver_top
% 3.50/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.50/0.99      | v1_xboole_0(X0) = iProver_top
% 3.50/0.99      | v1_xboole_0(k7_relset_1(sK5,sK6,sK8,X0)) = iProver_top
% 3.50/0.99      | v1_xboole_0(sK6) = iProver_top
% 3.50/0.99      | v1_xboole_0(sK5) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_2084,c_1569]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6844,plain,
% 3.50/0.99      ( m1_subset_1(sK4(X0,sK5,sK8,sK0(k9_relat_1(sK8,X0))),sK5) = iProver_top
% 3.50/0.99      | m1_subset_1(sK0(k9_relat_1(sK8,X0)),sK6) != iProver_top
% 3.50/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.50/0.99      | v1_xboole_0(X0) = iProver_top
% 3.50/0.99      | v1_xboole_0(k9_relat_1(sK8,X0)) = iProver_top
% 3.50/0.99      | v1_xboole_0(sK6) = iProver_top
% 3.50/0.99      | v1_xboole_0(sK5) = iProver_top ),
% 3.50/0.99      inference(light_normalisation,[status(thm)],[c_6836,c_2084]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_29,plain,
% 3.50/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_25,negated_conjecture,
% 3.50/0.99      ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
% 3.50/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_30,plain,
% 3.50/0.99      ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.50/0.99      | ~ v1_relat_1(X1)
% 3.50/0.99      | v1_relat_1(X0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1513,plain,
% 3.50/0.99      ( ~ v1_relat_1(k2_zfmisc_1(sK5,sK6)) | v1_relat_1(sK8) ),
% 3.50/0.99      inference(resolution,[status(thm)],[c_4,c_26]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1514,plain,
% 3.50/0.99      ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) != iProver_top
% 3.50/0.99      | v1_relat_1(sK8) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1513]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_5,plain,
% 3.50/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.50/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1608,plain,
% 3.50/0.99      ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1609,plain,
% 3.50/0.99      ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1608]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3,plain,
% 3.50/0.99      ( m1_subset_1(X0,X1)
% 3.50/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.50/0.99      | ~ r2_hidden(X0,X2) ),
% 3.50/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1520,plain,
% 3.50/0.99      ( m1_subset_1(X0,sK6)
% 3.50/0.99      | ~ m1_subset_1(k7_relset_1(sK5,sK6,sK8,X1),k1_zfmisc_1(sK6))
% 3.50/0.99      | ~ r2_hidden(X0,k7_relset_1(sK5,sK6,sK8,X1)) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1721,plain,
% 3.50/0.99      ( ~ m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6))
% 3.50/0.99      | m1_subset_1(sK9,sK6)
% 3.50/0.99      | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_1520]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1722,plain,
% 3.50/0.99      ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6)) != iProver_top
% 3.50/0.99      | m1_subset_1(sK9,sK6) = iProver_top
% 3.50/0.99      | r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1721]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_14,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/0.99      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
% 3.50/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1382,plain,
% 3.50/0.99      ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,X0),k1_zfmisc_1(sK6))
% 3.50/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1926,plain,
% 3.50/0.99      ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6))
% 3.50/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_1382]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1927,plain,
% 3.50/0.99      ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6)) = iProver_top
% 3.50/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1926]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1035,plain,
% 3.50/0.99      ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1563,plain,
% 3.50/0.99      ( m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
% 3.50/0.99      | m1_subset_1(sK9,sK6) != iProver_top
% 3.50/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.50/0.99      | v1_xboole_0(sK6) = iProver_top
% 3.50/0.99      | v1_xboole_0(sK5) = iProver_top
% 3.50/0.99      | v1_xboole_0(sK7) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1035,c_1037]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1886,plain,
% 3.50/0.99      ( m1_subset_1(sK9,sK6) != iProver_top
% 3.50/0.99      | m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
% 3.50/0.99      | v1_xboole_0(sK6) = iProver_top
% 3.50/0.99      | v1_xboole_0(sK5) = iProver_top
% 3.50/0.99      | v1_xboole_0(sK7) = iProver_top ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_1563,c_29]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1887,plain,
% 3.50/0.99      ( m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
% 3.50/0.99      | m1_subset_1(sK9,sK6) != iProver_top
% 3.50/0.99      | v1_xboole_0(sK6) = iProver_top
% 3.50/0.99      | v1_xboole_0(sK5) = iProver_top
% 3.50/0.99      | v1_xboole_0(sK7) = iProver_top ),
% 3.50/0.99      inference(renaming,[status(thm)],[c_1886]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.50/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1055,plain,
% 3.50/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 3.50/0.99      | r2_hidden(X0,X1) = iProver_top
% 3.50/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1895,plain,
% 3.50/0.99      ( m1_subset_1(sK9,sK6) != iProver_top
% 3.50/0.99      | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
% 3.50/0.99      | v1_xboole_0(sK6) = iProver_top
% 3.50/0.99      | v1_xboole_0(sK5) = iProver_top
% 3.50/0.99      | v1_xboole_0(sK7) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1887,c_1055]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1958,plain,
% 3.50/0.99      ( r2_hidden(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
% 3.50/0.99      | v1_xboole_0(sK6) = iProver_top
% 3.50/0.99      | v1_xboole_0(sK5) = iProver_top
% 3.50/0.99      | v1_xboole_0(sK7) = iProver_top ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_1895,c_29,c_30,c_1722,c_1927]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_13,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/0.99      | ~ v1_xboole_0(X2)
% 3.50/0.99      | v1_xboole_0(X0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1047,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.50/0.99      | v1_xboole_0(X2) != iProver_top
% 3.50/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2208,plain,
% 3.50/0.99      ( v1_xboole_0(sK6) != iProver_top
% 3.50/0.99      | v1_xboole_0(sK8) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1034,c_1047]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2324,plain,
% 3.50/0.99      ( r2_hidden(sK9,k9_relat_1(sK8,sK7)) = iProver_top ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_2084,c_1035]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7,plain,
% 3.50/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.50/0.99      | r2_hidden(sK1(X0,X2,X1),X2)
% 3.50/0.99      | ~ v1_relat_1(X1) ),
% 3.50/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2676,plain,
% 3.50/0.99      ( r2_hidden(sK1(sK9,sK7,sK8),sK7)
% 3.50/0.99      | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
% 3.50/0.99      | ~ v1_relat_1(sK8) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2677,plain,
% 3.50/0.99      ( r2_hidden(sK1(sK9,sK7,sK8),sK7) = iProver_top
% 3.50/0.99      | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
% 3.50/0.99      | v1_relat_1(sK8) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_2676]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_8,plain,
% 3.50/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.50/0.99      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 3.50/0.99      | ~ v1_relat_1(X1) ),
% 3.50/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2674,plain,
% 3.50/0.99      ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8)
% 3.50/0.99      | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
% 3.50/0.99      | ~ v1_relat_1(sK8) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2681,plain,
% 3.50/0.99      ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top
% 3.50/0.99      | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
% 3.50/0.99      | v1_relat_1(sK8) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_2674]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1,plain,
% 3.50/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.50/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3585,plain,
% 3.50/0.99      ( ~ r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8)
% 3.50/0.99      | ~ v1_xboole_0(sK8) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3586,plain,
% 3.50/0.99      ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) != iProver_top
% 3.50/0.99      | v1_xboole_0(sK8) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_3585]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3715,plain,
% 3.50/0.99      ( ~ r2_hidden(sK1(sK9,sK7,sK8),sK7) | ~ v1_xboole_0(sK7) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3716,plain,
% 3.50/0.99      ( r2_hidden(sK1(sK9,sK7,sK8),sK7) != iProver_top
% 3.50/0.99      | v1_xboole_0(sK7) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_3715]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_21,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,X1)
% 3.50/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 3.50/0.99      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 3.50/0.99      | r2_hidden(sK4(X4,X3,X2,X0),X4)
% 3.50/0.99      | v1_xboole_0(X1)
% 3.50/0.99      | v1_xboole_0(X3)
% 3.50/0.99      | v1_xboole_0(X4) ),
% 3.50/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3887,plain,
% 3.50/0.99      ( ~ m1_subset_1(sK9,sK6)
% 3.50/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.50/0.99      | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7)
% 3.50/0.99      | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
% 3.50/0.99      | v1_xboole_0(sK6)
% 3.50/0.99      | v1_xboole_0(sK5)
% 3.50/0.99      | v1_xboole_0(sK7) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3888,plain,
% 3.50/0.99      ( m1_subset_1(sK9,sK6) != iProver_top
% 3.50/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.50/0.99      | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7) = iProver_top
% 3.50/0.99      | r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top
% 3.50/0.99      | v1_xboole_0(sK6) = iProver_top
% 3.50/0.99      | v1_xboole_0(sK5) = iProver_top
% 3.50/0.99      | v1_xboole_0(sK7) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_3887]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_22,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,X1)
% 3.50/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 3.50/0.99      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 3.50/0.99      | r2_hidden(k4_tarski(sK4(X4,X3,X2,X0),X0),X2)
% 3.50/0.99      | v1_xboole_0(X1)
% 3.50/0.99      | v1_xboole_0(X3)
% 3.50/0.99      | v1_xboole_0(X4) ),
% 3.50/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1038,plain,
% 3.50/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 3.50/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 3.50/0.99      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 3.50/0.99      | r2_hidden(k4_tarski(sK4(X4,X3,X2,X0),X0),X2) = iProver_top
% 3.50/0.99      | v1_xboole_0(X1) = iProver_top
% 3.50/0.99      | v1_xboole_0(X3) = iProver_top
% 3.50/0.99      | v1_xboole_0(X4) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2050,plain,
% 3.50/0.99      ( m1_subset_1(sK9,sK6) != iProver_top
% 3.50/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.50/0.99      | r2_hidden(k4_tarski(sK4(sK7,sK5,sK8,sK9),sK9),sK8) = iProver_top
% 3.50/0.99      | v1_xboole_0(sK6) = iProver_top
% 3.50/0.99      | v1_xboole_0(sK5) = iProver_top
% 3.50/0.99      | v1_xboole_0(sK7) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1035,c_1038]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2585,plain,
% 3.50/0.99      ( r2_hidden(k4_tarski(sK4(sK7,sK5,sK8,sK9),sK9),sK8) = iProver_top
% 3.50/0.99      | v1_xboole_0(sK6) = iProver_top
% 3.50/0.99      | v1_xboole_0(sK5) = iProver_top
% 3.50/0.99      | v1_xboole_0(sK7) = iProver_top ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_2050,c_29,c_30,c_1722,c_1927]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11,plain,
% 3.50/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.50/0.99      | ~ v1_funct_1(X2)
% 3.50/0.99      | ~ v1_relat_1(X2)
% 3.50/0.99      | k1_funct_1(X2,X0) = X1 ),
% 3.50/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_27,negated_conjecture,
% 3.50/0.99      ( v1_funct_1(sK8) ),
% 3.50/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_345,plain,
% 3.50/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.50/0.99      | ~ v1_relat_1(X2)
% 3.50/0.99      | k1_funct_1(X2,X0) = X1
% 3.50/0.99      | sK8 != X2 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_27]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_346,plain,
% 3.50/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),sK8)
% 3.50/0.99      | ~ v1_relat_1(sK8)
% 3.50/0.99      | k1_funct_1(sK8,X0) = X1 ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_345]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1031,plain,
% 3.50/0.99      ( k1_funct_1(sK8,X0) = X1
% 3.50/0.99      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
% 3.50/0.99      | v1_relat_1(sK8) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_346]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2595,plain,
% 3.50/0.99      ( k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) = sK9
% 3.50/0.99      | v1_relat_1(sK8) != iProver_top
% 3.50/0.99      | v1_xboole_0(sK6) = iProver_top
% 3.50/0.99      | v1_xboole_0(sK5) = iProver_top
% 3.50/0.99      | v1_xboole_0(sK7) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_2585,c_1031]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4065,plain,
% 3.50/0.99      ( v1_xboole_0(sK5) = iProver_top
% 3.50/0.99      | k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) = sK9 ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_2595,c_1514,c_1609,c_2208,c_2324,c_2677,c_2681,c_3586,
% 3.50/0.99                 c_3716]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4066,plain,
% 3.50/0.99      ( k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) = sK9
% 3.50/0.99      | v1_xboole_0(sK5) = iProver_top ),
% 3.50/0.99      inference(renaming,[status(thm)],[c_4065]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_24,negated_conjecture,
% 3.50/0.99      ( ~ r2_hidden(X0,sK5)
% 3.50/0.99      | ~ r2_hidden(X0,sK7)
% 3.50/0.99      | k1_funct_1(sK8,X0) != sK9 ),
% 3.50/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7418,plain,
% 3.50/0.99      ( ~ r2_hidden(sK4(sK7,sK5,sK8,sK9),sK5)
% 3.50/0.99      | ~ r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7)
% 3.50/0.99      | k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) != sK9 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_24]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7419,plain,
% 3.50/0.99      ( k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) != sK9
% 3.50/0.99      | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK5) != iProver_top
% 3.50/0.99      | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_7418]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7461,plain,
% 3.50/0.99      ( v1_xboole_0(sK5) = iProver_top ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_6844,c_29,c_30,c_1514,c_1609,c_1722,c_1927,c_1958,
% 3.50/0.99                 c_2208,c_2324,c_2677,c_2681,c_3586,c_3716,c_3888,c_4066,
% 3.50/0.99                 c_7419]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_19,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/0.99      | r2_hidden(sK3(X1,X0),X1)
% 3.50/0.99      | k1_relset_1(X1,X2,X0) = X1 ),
% 3.50/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1041,plain,
% 3.50/1.00      ( k1_relset_1(X0,X1,X2) = X0
% 3.50/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.50/1.00      | r2_hidden(sK3(X0,X2),X0) = iProver_top ),
% 3.50/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_3111,plain,
% 3.50/1.00      ( k1_relset_1(sK5,sK6,sK8) = sK5
% 3.50/1.00      | r2_hidden(sK3(sK5,sK8),sK5) = iProver_top ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_1034,c_1041]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_15,plain,
% 3.50/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.50/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1045,plain,
% 3.50/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.50/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.50/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1673,plain,
% 3.50/1.00      ( k1_relset_1(sK5,sK6,sK8) = k1_relat_1(sK8) ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_1034,c_1045]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_3114,plain,
% 3.50/1.00      ( k1_relat_1(sK8) = sK5
% 3.50/1.00      | r2_hidden(sK3(sK5,sK8),sK5) = iProver_top ),
% 3.50/1.00      inference(demodulation,[status(thm)],[c_3111,c_1673]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1056,plain,
% 3.50/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.50/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.50/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_3917,plain,
% 3.50/1.00      ( k1_relat_1(sK8) = sK5 | v1_xboole_0(sK5) != iProver_top ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_3114,c_1056]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_7466,plain,
% 3.50/1.00      ( k1_relat_1(sK8) = sK5 ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_7461,c_3917]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1049,plain,
% 3.50/1.00      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.50/1.00      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
% 3.50/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.50/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_3279,plain,
% 3.50/1.00      ( k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0
% 3.50/1.00      | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 3.50/1.00      | v1_relat_1(sK8) != iProver_top ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_1049,c_1031]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_3612,plain,
% 3.50/1.00      ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 3.50/1.00      | k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0 ),
% 3.50/1.00      inference(global_propositional_subsumption,
% 3.50/1.00                [status(thm)],
% 3.50/1.00                [c_3279,c_1514,c_1609]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_3613,plain,
% 3.50/1.00      ( k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0
% 3.50/1.00      | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top ),
% 3.50/1.00      inference(renaming,[status(thm)],[c_3612]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_3623,plain,
% 3.50/1.00      ( k1_funct_1(sK8,sK1(sK9,sK7,sK8)) = sK9 ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_2324,c_3613]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_10,plain,
% 3.50/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.50/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.50/1.00      | ~ v1_funct_1(X1)
% 3.50/1.00      | ~ v1_relat_1(X1) ),
% 3.50/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_330,plain,
% 3.50/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.50/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.50/1.00      | ~ v1_relat_1(X1)
% 3.50/1.00      | sK8 != X1 ),
% 3.50/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_27]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_331,plain,
% 3.50/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK8))
% 3.50/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8)
% 3.50/1.00      | ~ v1_relat_1(sK8) ),
% 3.50/1.00      inference(unflattening,[status(thm)],[c_330]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1032,plain,
% 3.50/1.00      ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 3.50/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top
% 3.50/1.00      | v1_relat_1(sK8) != iProver_top ),
% 3.50/1.00      inference(predicate_to_equality,[status(thm)],[c_331]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_3652,plain,
% 3.50/1.00      ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) != iProver_top
% 3.50/1.00      | r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top
% 3.50/1.00      | v1_relat_1(sK8) != iProver_top ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_3623,c_1032]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_3773,plain,
% 3.50/1.00      ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top ),
% 3.50/1.00      inference(global_propositional_subsumption,
% 3.50/1.00                [status(thm)],
% 3.50/1.00                [c_3652,c_1514,c_1609,c_2324,c_2681]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_12,plain,
% 3.50/1.00      ( r2_hidden(X0,k1_relat_1(X1))
% 3.50/1.00      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.50/1.00      | ~ v1_funct_1(X1)
% 3.50/1.00      | ~ v1_relat_1(X1) ),
% 3.50/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_315,plain,
% 3.50/1.00      ( r2_hidden(X0,k1_relat_1(X1))
% 3.50/1.00      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.50/1.00      | ~ v1_relat_1(X1)
% 3.50/1.00      | sK8 != X1 ),
% 3.50/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_316,plain,
% 3.50/1.00      ( r2_hidden(X0,k1_relat_1(sK8))
% 3.50/1.00      | ~ r2_hidden(k4_tarski(X0,X1),sK8)
% 3.50/1.00      | ~ v1_relat_1(sK8) ),
% 3.50/1.00      inference(unflattening,[status(thm)],[c_315]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1033,plain,
% 3.50/1.00      ( r2_hidden(X0,k1_relat_1(sK8)) = iProver_top
% 3.50/1.00      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
% 3.50/1.00      | v1_relat_1(sK8) != iProver_top ),
% 3.50/1.00      inference(predicate_to_equality,[status(thm)],[c_316]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_3779,plain,
% 3.50/1.00      ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) = iProver_top
% 3.50/1.00      | v1_relat_1(sK8) != iProver_top ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_3773,c_1033]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_9,plain,
% 3.50/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.50/1.00      | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
% 3.50/1.00      | ~ v1_relat_1(X1) ),
% 3.50/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_2675,plain,
% 3.50/1.00      ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8))
% 3.50/1.00      | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
% 3.50/1.00      | ~ v1_relat_1(sK8) ),
% 3.50/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_2679,plain,
% 3.50/1.00      ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) = iProver_top
% 3.50/1.00      | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
% 3.50/1.00      | v1_relat_1(sK8) != iProver_top ),
% 3.50/1.00      inference(predicate_to_equality,[status(thm)],[c_2675]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_3904,plain,
% 3.50/1.00      ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) = iProver_top ),
% 3.50/1.00      inference(global_propositional_subsumption,
% 3.50/1.00                [status(thm)],
% 3.50/1.00                [c_3779,c_1514,c_1609,c_2324,c_2679]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_3909,plain,
% 3.50/1.00      ( v1_xboole_0(k1_relat_1(sK8)) != iProver_top ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_3904,c_1056]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_7720,plain,
% 3.50/1.00      ( v1_xboole_0(sK5) != iProver_top ),
% 3.50/1.00      inference(demodulation,[status(thm)],[c_7466,c_3909]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(contradiction,plain,
% 3.50/1.00      ( $false ),
% 3.50/1.00      inference(minisat,[status(thm)],[c_7720,c_7461]) ).
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.50/1.00  
% 3.50/1.00  ------                               Statistics
% 3.50/1.00  
% 3.50/1.00  ------ Selected
% 3.50/1.00  
% 3.50/1.00  total_time:                             0.32
% 3.50/1.00  
%------------------------------------------------------------------------------
