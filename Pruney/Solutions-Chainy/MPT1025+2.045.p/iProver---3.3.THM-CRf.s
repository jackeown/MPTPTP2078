%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:09 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :  174 (1182 expanded)
%              Number of clauses        :   99 ( 359 expanded)
%              Number of leaves         :   20 ( 264 expanded)
%              Depth                    :   21
%              Number of atoms          :  644 (5671 expanded)
%              Number of equality atoms :  205 (1040 expanded)
%              Maximal formula depth    :   17 (   6 average)
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

fof(f16,plain,(
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

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
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
              | ~ m1_subset_1(X5,X0) )
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
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK9
            | ~ r2_hidden(X5,X2)
            | ~ m1_subset_1(X5,X0) )
        & r2_hidden(sK9,k7_relset_1(X0,X1,X3,X2)) ) ) ),
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
              ( k1_funct_1(sK8,X5) != X4
              | ~ r2_hidden(X5,sK7)
              | ~ m1_subset_1(X5,sK5) )
          & r2_hidden(X4,k7_relset_1(sK5,sK6,sK8,sK7)) )
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ! [X5] :
        ( k1_funct_1(sK8,X5) != sK9
        | ~ r2_hidden(X5,sK7)
        | ~ m1_subset_1(X5,sK5) )
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
      | ~ m1_subset_1(X5,sK5) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

cnf(c_6910,plain,
    ( m1_subset_1(sK4(X0,sK5,sK8,sK0(k7_relset_1(sK5,sK6,sK8,X0))),sK5) = iProver_top
    | m1_subset_1(sK0(k9_relat_1(sK8,X0)),sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k7_relset_1(sK5,sK6,sK8,X0)) = iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2084,c_1569])).

cnf(c_6918,plain,
    ( m1_subset_1(sK4(X0,sK5,sK8,sK0(k9_relat_1(sK8,X0))),sK5) = iProver_top
    | m1_subset_1(sK0(k9_relat_1(sK8,X0)),sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k9_relat_1(sK8,X0)) = iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6910,c_2084])).

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

cnf(c_1506,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK5,sK6))
    | v1_relat_1(sK8) ),
    inference(resolution,[status(thm)],[c_4,c_26])).

cnf(c_5,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1511,plain,
    ( v1_relat_1(sK8) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1506,c_5])).

cnf(c_1512,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1511])).

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

cnf(c_1722,plain,
    ( ~ m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6))
    | m1_subset_1(sK9,sK6)
    | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_1520])).

cnf(c_1723,plain,
    ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6)) != iProver_top
    | m1_subset_1(sK9,sK6) = iProver_top
    | r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1722])).

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

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1382,plain,
    ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,X0),k1_zfmisc_1(sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1922,plain,
    ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_1382])).

cnf(c_1923,plain,
    ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6)) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1922])).

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

cnf(c_2200,plain,
    ( v1_xboole_0(sK6) != iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1034,c_1047])).

cnf(c_2316,plain,
    ( r2_hidden(sK9,k9_relat_1(sK8,sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2084,c_1035])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2707,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),sK7)
    | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2708,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),sK7) = iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2707])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2705,plain,
    ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8)
    | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2712,plain,
    ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2705])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3602,plain,
    ( ~ r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8)
    | ~ v1_xboole_0(sK8) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3603,plain,
    ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) != iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3602])).

cnf(c_3732,plain,
    ( ~ r2_hidden(sK1(sK9,sK7,sK8),sK7)
    | ~ v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3733,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),sK7) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3732])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | r2_hidden(sK4(X4,X3,X2,X0),X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3952,plain,
    ( ~ m1_subset_1(sK9,sK6)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7)
    | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
    | v1_xboole_0(sK6)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_3953,plain,
    ( m1_subset_1(sK9,sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7) = iProver_top
    | r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3952])).

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

cnf(c_2583,plain,
    ( r2_hidden(k4_tarski(sK4(sK7,sK5,sK8,sK9),sK9),sK8) = iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2050,c_29,c_30,c_1723,c_1923])).

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

cnf(c_2593,plain,
    ( k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) = sK9
    | v1_relat_1(sK8) != iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2583,c_1031])).

cnf(c_4081,plain,
    ( v1_xboole_0(sK5) = iProver_top
    | k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) = sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2593,c_1512,c_2200,c_2316,c_2708,c_2712,c_3603,c_3733])).

cnf(c_4082,plain,
    ( k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) = sK9
    | v1_xboole_0(sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_4081])).

cnf(c_24,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | ~ r2_hidden(X0,sK7)
    | k1_funct_1(sK8,X0) != sK9 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_7521,plain,
    ( ~ m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5)
    | ~ r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7)
    | k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) != sK9 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_7522,plain,
    ( k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) != sK9
    | m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) != iProver_top
    | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7521])).

cnf(c_7564,plain,
    ( v1_xboole_0(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6918,c_29,c_30,c_1512,c_1723,c_1887,c_1923,c_2200,c_2316,c_2708,c_2712,c_3603,c_3733,c_3953,c_4082,c_7522])).

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

cnf(c_3148,plain,
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

cnf(c_3151,plain,
    ( k1_relat_1(sK8) = sK5
    | r2_hidden(sK3(sK5,sK8),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3148,c_1673])).

cnf(c_1056,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3982,plain,
    ( k1_relat_1(sK8) = sK5
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3151,c_1056])).

cnf(c_7569,plain,
    ( k1_relat_1(sK8) = sK5 ),
    inference(superposition,[status(thm)],[c_7564,c_3982])).

cnf(c_1049,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3288,plain,
    ( k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0
    | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1049,c_1031])).

cnf(c_3629,plain,
    ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3288,c_1512])).

cnf(c_3630,plain,
    ( k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0
    | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3629])).

cnf(c_3640,plain,
    ( k1_funct_1(sK8,sK1(sK9,sK7,sK8)) = sK9 ),
    inference(superposition,[status(thm)],[c_2316,c_3630])).

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

cnf(c_3669,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3640,c_1032])).

cnf(c_3790,plain,
    ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3669,c_1512,c_2316,c_2712])).

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

cnf(c_3796,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3790,c_1033])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2706,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8))
    | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2710,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) = iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2706])).

cnf(c_3969,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3796,c_1512,c_2316,c_2710])).

cnf(c_3974,plain,
    ( v1_xboole_0(k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3969,c_1056])).

cnf(c_7823,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7569,c_3974])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7823,c_7564])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:00:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.45/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/0.98  
% 3.45/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.45/0.98  
% 3.45/0.98  ------  iProver source info
% 3.45/0.98  
% 3.45/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.45/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.45/0.98  git: non_committed_changes: false
% 3.45/0.98  git: last_make_outside_of_git: false
% 3.45/0.98  
% 3.45/0.98  ------ 
% 3.45/0.98  ------ Parsing...
% 3.45/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.45/0.98  
% 3.45/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.45/0.98  
% 3.45/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.45/0.98  
% 3.45/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.45/0.98  ------ Proving...
% 3.45/0.98  ------ Problem Properties 
% 3.45/0.98  
% 3.45/0.98  
% 3.45/0.98  clauses                                 27
% 3.45/0.98  conjectures                             3
% 3.45/0.98  EPR                                     2
% 3.45/0.98  Horn                                    20
% 3.45/0.98  unary                                   3
% 3.45/0.98  binary                                  5
% 3.45/0.98  lits                                    91
% 3.45/0.98  lits eq                                 7
% 3.45/0.98  fd_pure                                 0
% 3.45/0.98  fd_pseudo                               0
% 3.45/0.98  fd_cond                                 0
% 3.45/0.98  fd_pseudo_cond                          1
% 3.45/0.98  AC symbols                              0
% 3.45/0.98  
% 3.45/0.98  ------ Input Options Time Limit: Unbounded
% 3.45/0.98  
% 3.45/0.98  
% 3.45/0.98  ------ 
% 3.45/0.98  Current options:
% 3.45/0.98  ------ 
% 3.45/0.98  
% 3.45/0.98  
% 3.45/0.98  
% 3.45/0.98  
% 3.45/0.98  ------ Proving...
% 3.45/0.98  
% 3.45/0.98  
% 3.45/0.98  % SZS status Theorem for theBenchmark.p
% 3.45/0.98  
% 3.45/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.45/0.98  
% 3.45/0.98  fof(f14,conjecture,(
% 3.45/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.98  
% 3.45/0.98  fof(f15,negated_conjecture,(
% 3.45/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.45/0.98    inference(negated_conjecture,[],[f14])).
% 3.45/0.98  
% 3.45/0.98  fof(f16,plain,(
% 3.45/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.45/0.98    inference(pure_predicate_removal,[],[f15])).
% 3.45/0.98  
% 3.45/0.98  fof(f31,plain,(
% 3.45/0.98    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 3.45/0.98    inference(ennf_transformation,[],[f16])).
% 3.45/0.98  
% 3.45/0.98  fof(f32,plain,(
% 3.45/0.98    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 3.45/0.98    inference(flattening,[],[f31])).
% 3.45/0.98  
% 3.45/0.98  fof(f53,plain,(
% 3.45/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK9 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(sK9,k7_relset_1(X0,X1,X3,X2)))) )),
% 3.45/0.98    introduced(choice_axiom,[])).
% 3.45/0.98  
% 3.45/0.98  fof(f52,plain,(
% 3.45/0.98    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK8,X5) != X4 | ~r2_hidden(X5,sK7) | ~m1_subset_1(X5,sK5)) & r2_hidden(X4,k7_relset_1(sK5,sK6,sK8,sK7))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_1(sK8))),
% 3.45/0.98    introduced(choice_axiom,[])).
% 3.45/0.98  
% 3.45/0.98  fof(f54,plain,(
% 3.45/0.98    (! [X5] : (k1_funct_1(sK8,X5) != sK9 | ~r2_hidden(X5,sK7) | ~m1_subset_1(X5,sK5)) & r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_1(sK8)),
% 3.45/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f32,f53,f52])).
% 3.45/0.98  
% 3.45/0.98  fof(f80,plain,(
% 3.45/0.98    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 3.45/0.98    inference(cnf_transformation,[],[f54])).
% 3.45/0.98  
% 3.45/0.98  fof(f11,axiom,(
% 3.45/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.98  
% 3.45/0.98  fof(f28,plain,(
% 3.45/0.98    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/0.98    inference(ennf_transformation,[],[f11])).
% 3.45/0.98  
% 3.45/0.98  fof(f71,plain,(
% 3.45/0.98    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/0.98    inference(cnf_transformation,[],[f28])).
% 3.45/0.98  
% 3.45/0.98  fof(f1,axiom,(
% 3.45/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.98  
% 3.45/0.98  fof(f33,plain,(
% 3.45/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.45/0.98    inference(nnf_transformation,[],[f1])).
% 3.45/0.98  
% 3.45/0.98  fof(f34,plain,(
% 3.45/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.45/0.98    inference(rectify,[],[f33])).
% 3.45/0.98  
% 3.45/0.98  fof(f35,plain,(
% 3.45/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.45/0.98    introduced(choice_axiom,[])).
% 3.45/0.98  
% 3.45/0.98  fof(f36,plain,(
% 3.45/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.45/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 3.45/0.98  
% 3.45/0.98  fof(f56,plain,(
% 3.45/0.98    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.45/0.98    inference(cnf_transformation,[],[f36])).
% 3.45/0.98  
% 3.45/0.98  fof(f13,axiom,(
% 3.45/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 3.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.98  
% 3.45/0.98  fof(f30,plain,(
% 3.45/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.45/0.98    inference(ennf_transformation,[],[f13])).
% 3.45/0.98  
% 3.45/0.98  fof(f48,plain,(
% 3.45/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.45/0.98    inference(nnf_transformation,[],[f30])).
% 3.45/0.98  
% 3.45/0.98  fof(f49,plain,(
% 3.45/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.45/0.98    inference(rectify,[],[f48])).
% 3.45/0.98  
% 3.45/0.98  fof(f50,plain,(
% 3.45/0.98    ! [X4,X3,X2,X1] : (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) => (r2_hidden(sK4(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK4(X1,X2,X3,X4),X2)))),
% 3.45/0.98    introduced(choice_axiom,[])).
% 3.45/0.98  
% 3.45/0.98  fof(f51,plain,(
% 3.45/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & ((r2_hidden(sK4(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK4(X1,X2,X3,X4),X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.45/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f49,f50])).
% 3.45/0.98  
% 3.45/0.98  fof(f75,plain,(
% 3.45/0.98    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK4(X1,X2,X3,X4),X2) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.45/0.98    inference(cnf_transformation,[],[f51])).
% 3.45/0.98  
% 3.45/0.98  fof(f81,plain,(
% 3.45/0.98    r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))),
% 3.45/0.98    inference(cnf_transformation,[],[f54])).
% 3.45/0.98  
% 3.45/0.98  fof(f4,axiom,(
% 3.45/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.98  
% 3.45/0.98  fof(f21,plain,(
% 3.45/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.45/0.98    inference(ennf_transformation,[],[f4])).
% 3.45/0.98  
% 3.45/0.98  fof(f59,plain,(
% 3.45/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.45/0.98    inference(cnf_transformation,[],[f21])).
% 3.45/0.98  
% 3.45/0.98  fof(f5,axiom,(
% 3.45/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.98  
% 3.45/0.98  fof(f60,plain,(
% 3.45/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.45/0.98    inference(cnf_transformation,[],[f5])).
% 3.45/0.98  
% 3.45/0.98  fof(f3,axiom,(
% 3.45/0.98    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.98  
% 3.45/0.98  fof(f19,plain,(
% 3.45/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.45/0.98    inference(ennf_transformation,[],[f3])).
% 3.45/0.98  
% 3.45/0.98  fof(f20,plain,(
% 3.45/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.45/0.98    inference(flattening,[],[f19])).
% 3.45/0.98  
% 3.45/0.98  fof(f58,plain,(
% 3.45/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.45/0.98    inference(cnf_transformation,[],[f20])).
% 3.45/0.98  
% 3.45/0.98  fof(f9,axiom,(
% 3.45/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 3.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.98  
% 3.45/0.98  fof(f26,plain,(
% 3.45/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/0.98    inference(ennf_transformation,[],[f9])).
% 3.45/0.98  
% 3.45/0.98  fof(f69,plain,(
% 3.45/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/0.98    inference(cnf_transformation,[],[f26])).
% 3.45/0.98  
% 3.45/0.98  fof(f8,axiom,(
% 3.45/0.98    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.98  
% 3.45/0.98  fof(f25,plain,(
% 3.45/0.98    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.45/0.98    inference(ennf_transformation,[],[f8])).
% 3.45/0.98  
% 3.45/0.98  fof(f68,plain,(
% 3.45/0.98    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 3.45/0.98    inference(cnf_transformation,[],[f25])).
% 3.45/0.98  
% 3.45/0.98  fof(f6,axiom,(
% 3.45/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.98  
% 3.45/0.98  fof(f22,plain,(
% 3.45/0.98    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.45/0.98    inference(ennf_transformation,[],[f6])).
% 3.45/0.98  
% 3.45/0.98  fof(f37,plain,(
% 3.45/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.45/0.98    inference(nnf_transformation,[],[f22])).
% 3.45/0.98  
% 3.45/0.98  fof(f38,plain,(
% 3.45/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.45/0.98    inference(rectify,[],[f37])).
% 3.45/0.98  
% 3.45/0.98  fof(f39,plain,(
% 3.45/0.98    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 3.45/0.98    introduced(choice_axiom,[])).
% 3.45/0.98  
% 3.45/0.98  fof(f40,plain,(
% 3.45/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.45/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).
% 3.45/0.98  
% 3.45/0.98  fof(f63,plain,(
% 3.45/0.98    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.45/0.98    inference(cnf_transformation,[],[f40])).
% 3.45/0.98  
% 3.45/0.98  fof(f62,plain,(
% 3.45/0.98    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.45/0.98    inference(cnf_transformation,[],[f40])).
% 3.45/0.98  
% 3.45/0.98  fof(f55,plain,(
% 3.45/0.98    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.45/0.98    inference(cnf_transformation,[],[f36])).
% 3.45/0.98  
% 3.45/0.98  fof(f77,plain,(
% 3.45/0.98    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK4(X1,X2,X3,X4),X1) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.45/0.98    inference(cnf_transformation,[],[f51])).
% 3.45/0.98  
% 3.45/0.98  fof(f76,plain,(
% 3.45/0.98    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.45/0.98    inference(cnf_transformation,[],[f51])).
% 3.45/0.98  
% 3.45/0.98  fof(f7,axiom,(
% 3.45/0.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.98  
% 3.45/0.98  fof(f23,plain,(
% 3.45/0.98    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.45/0.98    inference(ennf_transformation,[],[f7])).
% 3.45/0.98  
% 3.45/0.98  fof(f24,plain,(
% 3.45/0.98    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.45/0.98    inference(flattening,[],[f23])).
% 3.45/0.98  
% 3.45/0.98  fof(f41,plain,(
% 3.45/0.98    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.45/0.98    inference(nnf_transformation,[],[f24])).
% 3.45/0.98  
% 3.45/0.98  fof(f42,plain,(
% 3.45/0.98    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.45/0.98    inference(flattening,[],[f41])).
% 3.45/0.98  
% 3.45/0.98  fof(f66,plain,(
% 3.45/0.98    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.45/0.98    inference(cnf_transformation,[],[f42])).
% 3.45/0.98  
% 3.45/0.98  fof(f79,plain,(
% 3.45/0.98    v1_funct_1(sK8)),
% 3.45/0.98    inference(cnf_transformation,[],[f54])).
% 3.45/0.98  
% 3.45/0.98  fof(f82,plain,(
% 3.45/0.98    ( ! [X5] : (k1_funct_1(sK8,X5) != sK9 | ~r2_hidden(X5,sK7) | ~m1_subset_1(X5,sK5)) )),
% 3.45/0.98    inference(cnf_transformation,[],[f54])).
% 3.45/0.98  
% 3.45/0.98  fof(f12,axiom,(
% 3.45/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 3.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.98  
% 3.45/0.98  fof(f29,plain,(
% 3.45/0.98    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.45/0.98    inference(ennf_transformation,[],[f12])).
% 3.45/0.98  
% 3.45/0.98  fof(f43,plain,(
% 3.45/0.98    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.45/0.98    inference(nnf_transformation,[],[f29])).
% 3.45/0.98  
% 3.45/0.98  fof(f44,plain,(
% 3.45/0.98    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.45/0.98    inference(rectify,[],[f43])).
% 3.45/0.98  
% 3.45/0.98  fof(f46,plain,(
% 3.45/0.98    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK3(X1,X2),X6),X2) & r2_hidden(sK3(X1,X2),X1)))),
% 3.45/0.98    introduced(choice_axiom,[])).
% 3.45/0.98  
% 3.45/0.98  fof(f45,plain,(
% 3.45/0.98    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2))),
% 3.45/0.98    introduced(choice_axiom,[])).
% 3.45/0.98  
% 3.45/0.98  fof(f47,plain,(
% 3.45/0.98    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK3(X1,X2),X6),X2) & r2_hidden(sK3(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.45/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f44,f46,f45])).
% 3.45/0.98  
% 3.45/0.98  fof(f72,plain,(
% 3.45/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X1,X0,X2) = X1 | r2_hidden(sK3(X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 3.45/0.98    inference(cnf_transformation,[],[f47])).
% 3.45/0.98  
% 3.45/0.98  fof(f10,axiom,(
% 3.45/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.98  
% 3.45/0.98  fof(f27,plain,(
% 3.45/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/0.98    inference(ennf_transformation,[],[f10])).
% 3.45/0.98  
% 3.45/0.98  fof(f70,plain,(
% 3.45/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/0.98    inference(cnf_transformation,[],[f27])).
% 3.45/0.98  
% 3.45/0.98  fof(f67,plain,(
% 3.45/0.98    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.45/0.98    inference(cnf_transformation,[],[f42])).
% 3.45/0.98  
% 3.45/0.98  fof(f83,plain,(
% 3.45/0.98    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.45/0.98    inference(equality_resolution,[],[f67])).
% 3.45/0.98  
% 3.45/0.98  fof(f65,plain,(
% 3.45/0.98    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.45/0.98    inference(cnf_transformation,[],[f42])).
% 3.45/0.98  
% 3.45/0.98  fof(f61,plain,(
% 3.45/0.98    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.45/0.98    inference(cnf_transformation,[],[f40])).
% 3.45/0.98  
% 3.45/0.98  cnf(c_26,negated_conjecture,
% 3.45/0.98      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.45/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1034,plain,
% 3.45/0.98      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_16,plain,
% 3.45/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/0.98      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.45/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1044,plain,
% 3.45/0.98      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.45/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_2084,plain,
% 3.45/0.98      ( k7_relset_1(sK5,sK6,sK8,X0) = k9_relat_1(sK8,X0) ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_1034,c_1044]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_0,plain,
% 3.45/0.98      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.45/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1057,plain,
% 3.45/0.98      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.45/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_23,plain,
% 3.45/0.98      ( ~ m1_subset_1(X0,X1)
% 3.45/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 3.45/0.98      | m1_subset_1(sK4(X4,X3,X2,X0),X3)
% 3.45/0.98      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 3.45/0.98      | v1_xboole_0(X1)
% 3.45/0.98      | v1_xboole_0(X3)
% 3.45/0.98      | v1_xboole_0(X4) ),
% 3.45/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1037,plain,
% 3.45/0.98      ( m1_subset_1(X0,X1) != iProver_top
% 3.45/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 3.45/0.98      | m1_subset_1(sK4(X4,X3,X2,X0),X3) = iProver_top
% 3.45/0.98      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 3.45/0.98      | v1_xboole_0(X1) = iProver_top
% 3.45/0.98      | v1_xboole_0(X3) = iProver_top
% 3.45/0.98      | v1_xboole_0(X4) = iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1569,plain,
% 3.45/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.45/0.98      | m1_subset_1(sK4(X3,X1,X0,sK0(k7_relset_1(X1,X2,X0,X3))),X1) = iProver_top
% 3.45/0.98      | m1_subset_1(sK0(k7_relset_1(X1,X2,X0,X3)),X2) != iProver_top
% 3.45/0.98      | v1_xboole_0(X2) = iProver_top
% 3.45/0.98      | v1_xboole_0(X3) = iProver_top
% 3.45/0.98      | v1_xboole_0(X1) = iProver_top
% 3.45/0.98      | v1_xboole_0(k7_relset_1(X1,X2,X0,X3)) = iProver_top ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_1057,c_1037]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_6910,plain,
% 3.45/0.98      ( m1_subset_1(sK4(X0,sK5,sK8,sK0(k7_relset_1(sK5,sK6,sK8,X0))),sK5) = iProver_top
% 3.45/0.98      | m1_subset_1(sK0(k9_relat_1(sK8,X0)),sK6) != iProver_top
% 3.45/0.98      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.45/0.98      | v1_xboole_0(X0) = iProver_top
% 3.45/0.98      | v1_xboole_0(k7_relset_1(sK5,sK6,sK8,X0)) = iProver_top
% 3.45/0.98      | v1_xboole_0(sK6) = iProver_top
% 3.45/0.98      | v1_xboole_0(sK5) = iProver_top ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_2084,c_1569]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_6918,plain,
% 3.45/0.98      ( m1_subset_1(sK4(X0,sK5,sK8,sK0(k9_relat_1(sK8,X0))),sK5) = iProver_top
% 3.45/0.98      | m1_subset_1(sK0(k9_relat_1(sK8,X0)),sK6) != iProver_top
% 3.45/0.98      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.45/0.98      | v1_xboole_0(X0) = iProver_top
% 3.45/0.98      | v1_xboole_0(k9_relat_1(sK8,X0)) = iProver_top
% 3.45/0.98      | v1_xboole_0(sK6) = iProver_top
% 3.45/0.98      | v1_xboole_0(sK5) = iProver_top ),
% 3.45/0.98      inference(light_normalisation,[status(thm)],[c_6910,c_2084]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_29,plain,
% 3.45/0.98      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_25,negated_conjecture,
% 3.45/0.98      ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
% 3.45/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_30,plain,
% 3.45/0.98      ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_4,plain,
% 3.45/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.45/0.98      | ~ v1_relat_1(X1)
% 3.45/0.98      | v1_relat_1(X0) ),
% 3.45/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1506,plain,
% 3.45/0.98      ( ~ v1_relat_1(k2_zfmisc_1(sK5,sK6)) | v1_relat_1(sK8) ),
% 3.45/0.98      inference(resolution,[status(thm)],[c_4,c_26]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_5,plain,
% 3.45/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.45/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1511,plain,
% 3.45/0.98      ( v1_relat_1(sK8) ),
% 3.45/0.98      inference(forward_subsumption_resolution,
% 3.45/0.98                [status(thm)],
% 3.45/0.98                [c_1506,c_5]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1512,plain,
% 3.45/0.98      ( v1_relat_1(sK8) = iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_1511]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_3,plain,
% 3.45/0.98      ( m1_subset_1(X0,X1)
% 3.45/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.45/0.98      | ~ r2_hidden(X0,X2) ),
% 3.45/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1520,plain,
% 3.45/0.98      ( m1_subset_1(X0,sK6)
% 3.45/0.98      | ~ m1_subset_1(k7_relset_1(sK5,sK6,sK8,X1),k1_zfmisc_1(sK6))
% 3.45/0.98      | ~ r2_hidden(X0,k7_relset_1(sK5,sK6,sK8,X1)) ),
% 3.45/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1722,plain,
% 3.45/0.98      ( ~ m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6))
% 3.45/0.98      | m1_subset_1(sK9,sK6)
% 3.45/0.98      | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
% 3.45/0.98      inference(instantiation,[status(thm)],[c_1520]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1723,plain,
% 3.45/0.98      ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6)) != iProver_top
% 3.45/0.98      | m1_subset_1(sK9,sK6) = iProver_top
% 3.45/0.98      | r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_1722]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1035,plain,
% 3.45/0.98      ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1563,plain,
% 3.45/0.98      ( m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
% 3.45/0.98      | m1_subset_1(sK9,sK6) != iProver_top
% 3.45/0.98      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.45/0.98      | v1_xboole_0(sK6) = iProver_top
% 3.45/0.98      | v1_xboole_0(sK5) = iProver_top
% 3.45/0.98      | v1_xboole_0(sK7) = iProver_top ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_1035,c_1037]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1886,plain,
% 3.45/0.98      ( m1_subset_1(sK9,sK6) != iProver_top
% 3.45/0.98      | m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
% 3.45/0.98      | v1_xboole_0(sK6) = iProver_top
% 3.45/0.98      | v1_xboole_0(sK5) = iProver_top
% 3.45/0.98      | v1_xboole_0(sK7) = iProver_top ),
% 3.45/0.98      inference(global_propositional_subsumption,
% 3.45/0.98                [status(thm)],
% 3.45/0.98                [c_1563,c_29]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1887,plain,
% 3.45/0.98      ( m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
% 3.45/0.98      | m1_subset_1(sK9,sK6) != iProver_top
% 3.45/0.98      | v1_xboole_0(sK6) = iProver_top
% 3.45/0.98      | v1_xboole_0(sK5) = iProver_top
% 3.45/0.98      | v1_xboole_0(sK7) = iProver_top ),
% 3.45/0.98      inference(renaming,[status(thm)],[c_1886]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_14,plain,
% 3.45/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/0.98      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
% 3.45/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1382,plain,
% 3.45/0.98      ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,X0),k1_zfmisc_1(sK6))
% 3.45/0.98      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.45/0.98      inference(instantiation,[status(thm)],[c_14]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1922,plain,
% 3.45/0.98      ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6))
% 3.45/0.98      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.45/0.98      inference(instantiation,[status(thm)],[c_1382]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1923,plain,
% 3.45/0.98      ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6)) = iProver_top
% 3.45/0.98      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_1922]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_13,plain,
% 3.45/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/0.98      | ~ v1_xboole_0(X2)
% 3.45/0.98      | v1_xboole_0(X0) ),
% 3.45/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1047,plain,
% 3.45/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.45/0.98      | v1_xboole_0(X2) != iProver_top
% 3.45/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_2200,plain,
% 3.45/0.98      ( v1_xboole_0(sK6) != iProver_top
% 3.45/0.98      | v1_xboole_0(sK8) = iProver_top ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_1034,c_1047]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_2316,plain,
% 3.45/0.98      ( r2_hidden(sK9,k9_relat_1(sK8,sK7)) = iProver_top ),
% 3.45/0.98      inference(demodulation,[status(thm)],[c_2084,c_1035]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_7,plain,
% 3.45/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.45/0.98      | r2_hidden(sK1(X0,X2,X1),X2)
% 3.45/0.98      | ~ v1_relat_1(X1) ),
% 3.45/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_2707,plain,
% 3.45/0.98      ( r2_hidden(sK1(sK9,sK7,sK8),sK7)
% 3.45/0.98      | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
% 3.45/0.98      | ~ v1_relat_1(sK8) ),
% 3.45/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_2708,plain,
% 3.45/0.98      ( r2_hidden(sK1(sK9,sK7,sK8),sK7) = iProver_top
% 3.45/0.98      | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
% 3.45/0.98      | v1_relat_1(sK8) != iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_2707]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_8,plain,
% 3.45/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.45/0.98      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 3.45/0.98      | ~ v1_relat_1(X1) ),
% 3.45/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_2705,plain,
% 3.45/0.98      ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8)
% 3.45/0.98      | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
% 3.45/0.98      | ~ v1_relat_1(sK8) ),
% 3.45/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_2712,plain,
% 3.45/0.98      ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top
% 3.45/0.98      | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
% 3.45/0.98      | v1_relat_1(sK8) != iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_2705]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1,plain,
% 3.45/0.98      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.45/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_3602,plain,
% 3.45/0.98      ( ~ r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8)
% 3.45/0.98      | ~ v1_xboole_0(sK8) ),
% 3.45/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_3603,plain,
% 3.45/0.98      ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) != iProver_top
% 3.45/0.98      | v1_xboole_0(sK8) != iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_3602]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_3732,plain,
% 3.45/0.98      ( ~ r2_hidden(sK1(sK9,sK7,sK8),sK7) | ~ v1_xboole_0(sK7) ),
% 3.45/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_3733,plain,
% 3.45/0.98      ( r2_hidden(sK1(sK9,sK7,sK8),sK7) != iProver_top
% 3.45/0.98      | v1_xboole_0(sK7) != iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_3732]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_21,plain,
% 3.45/0.98      ( ~ m1_subset_1(X0,X1)
% 3.45/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 3.45/0.98      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 3.45/0.98      | r2_hidden(sK4(X4,X3,X2,X0),X4)
% 3.45/0.98      | v1_xboole_0(X1)
% 3.45/0.98      | v1_xboole_0(X3)
% 3.45/0.98      | v1_xboole_0(X4) ),
% 3.45/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_3952,plain,
% 3.45/0.98      ( ~ m1_subset_1(sK9,sK6)
% 3.45/0.98      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.45/0.98      | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7)
% 3.45/0.98      | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
% 3.45/0.98      | v1_xboole_0(sK6)
% 3.45/0.98      | v1_xboole_0(sK5)
% 3.45/0.98      | v1_xboole_0(sK7) ),
% 3.45/0.98      inference(instantiation,[status(thm)],[c_21]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_3953,plain,
% 3.45/0.98      ( m1_subset_1(sK9,sK6) != iProver_top
% 3.45/0.98      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.45/0.98      | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7) = iProver_top
% 3.45/0.98      | r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top
% 3.45/0.98      | v1_xboole_0(sK6) = iProver_top
% 3.45/0.98      | v1_xboole_0(sK5) = iProver_top
% 3.45/0.98      | v1_xboole_0(sK7) = iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_3952]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_22,plain,
% 3.45/0.98      ( ~ m1_subset_1(X0,X1)
% 3.45/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 3.45/0.98      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 3.45/0.98      | r2_hidden(k4_tarski(sK4(X4,X3,X2,X0),X0),X2)
% 3.45/0.98      | v1_xboole_0(X1)
% 3.45/0.98      | v1_xboole_0(X3)
% 3.45/0.98      | v1_xboole_0(X4) ),
% 3.45/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1038,plain,
% 3.45/0.98      ( m1_subset_1(X0,X1) != iProver_top
% 3.45/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 3.45/0.98      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 3.45/0.98      | r2_hidden(k4_tarski(sK4(X4,X3,X2,X0),X0),X2) = iProver_top
% 3.45/0.98      | v1_xboole_0(X1) = iProver_top
% 3.45/0.98      | v1_xboole_0(X3) = iProver_top
% 3.45/0.98      | v1_xboole_0(X4) = iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_2050,plain,
% 3.45/0.98      ( m1_subset_1(sK9,sK6) != iProver_top
% 3.45/0.98      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.45/0.98      | r2_hidden(k4_tarski(sK4(sK7,sK5,sK8,sK9),sK9),sK8) = iProver_top
% 3.45/0.98      | v1_xboole_0(sK6) = iProver_top
% 3.45/0.98      | v1_xboole_0(sK5) = iProver_top
% 3.45/0.98      | v1_xboole_0(sK7) = iProver_top ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_1035,c_1038]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_2583,plain,
% 3.45/0.98      ( r2_hidden(k4_tarski(sK4(sK7,sK5,sK8,sK9),sK9),sK8) = iProver_top
% 3.45/0.98      | v1_xboole_0(sK6) = iProver_top
% 3.45/0.98      | v1_xboole_0(sK5) = iProver_top
% 3.45/0.98      | v1_xboole_0(sK7) = iProver_top ),
% 3.45/0.98      inference(global_propositional_subsumption,
% 3.45/0.98                [status(thm)],
% 3.45/0.98                [c_2050,c_29,c_30,c_1723,c_1923]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_11,plain,
% 3.45/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.45/0.98      | ~ v1_funct_1(X2)
% 3.45/0.98      | ~ v1_relat_1(X2)
% 3.45/0.98      | k1_funct_1(X2,X0) = X1 ),
% 3.45/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_27,negated_conjecture,
% 3.45/0.98      ( v1_funct_1(sK8) ),
% 3.45/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_345,plain,
% 3.45/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.45/0.98      | ~ v1_relat_1(X2)
% 3.45/0.98      | k1_funct_1(X2,X0) = X1
% 3.45/0.98      | sK8 != X2 ),
% 3.45/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_27]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_346,plain,
% 3.45/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),sK8)
% 3.45/0.98      | ~ v1_relat_1(sK8)
% 3.45/0.98      | k1_funct_1(sK8,X0) = X1 ),
% 3.45/0.98      inference(unflattening,[status(thm)],[c_345]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1031,plain,
% 3.45/0.98      ( k1_funct_1(sK8,X0) = X1
% 3.45/0.98      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
% 3.45/0.98      | v1_relat_1(sK8) != iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_346]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_2593,plain,
% 3.45/0.98      ( k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) = sK9
% 3.45/0.98      | v1_relat_1(sK8) != iProver_top
% 3.45/0.98      | v1_xboole_0(sK6) = iProver_top
% 3.45/0.98      | v1_xboole_0(sK5) = iProver_top
% 3.45/0.98      | v1_xboole_0(sK7) = iProver_top ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_2583,c_1031]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_4081,plain,
% 3.45/0.98      ( v1_xboole_0(sK5) = iProver_top
% 3.45/0.98      | k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) = sK9 ),
% 3.45/0.98      inference(global_propositional_subsumption,
% 3.45/0.98                [status(thm)],
% 3.45/0.98                [c_2593,c_1512,c_2200,c_2316,c_2708,c_2712,c_3603,c_3733]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_4082,plain,
% 3.45/0.98      ( k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) = sK9
% 3.45/0.98      | v1_xboole_0(sK5) = iProver_top ),
% 3.45/0.98      inference(renaming,[status(thm)],[c_4081]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_24,negated_conjecture,
% 3.45/0.98      ( ~ m1_subset_1(X0,sK5)
% 3.45/0.98      | ~ r2_hidden(X0,sK7)
% 3.45/0.98      | k1_funct_1(sK8,X0) != sK9 ),
% 3.45/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_7521,plain,
% 3.45/0.98      ( ~ m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5)
% 3.45/0.98      | ~ r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7)
% 3.45/0.98      | k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) != sK9 ),
% 3.45/0.98      inference(instantiation,[status(thm)],[c_24]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_7522,plain,
% 3.45/0.98      ( k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) != sK9
% 3.45/0.98      | m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) != iProver_top
% 3.45/0.98      | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7) != iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_7521]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_7564,plain,
% 3.45/0.98      ( v1_xboole_0(sK5) = iProver_top ),
% 3.45/0.98      inference(global_propositional_subsumption,
% 3.45/0.98                [status(thm)],
% 3.45/0.98                [c_6918,c_29,c_30,c_1512,c_1723,c_1887,c_1923,c_2200,
% 3.45/0.98                 c_2316,c_2708,c_2712,c_3603,c_3733,c_3953,c_4082,c_7522]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_19,plain,
% 3.45/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/0.98      | r2_hidden(sK3(X1,X0),X1)
% 3.45/0.98      | k1_relset_1(X1,X2,X0) = X1 ),
% 3.45/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1041,plain,
% 3.45/0.98      ( k1_relset_1(X0,X1,X2) = X0
% 3.45/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.45/0.98      | r2_hidden(sK3(X0,X2),X0) = iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_3148,plain,
% 3.45/0.98      ( k1_relset_1(sK5,sK6,sK8) = sK5
% 3.45/0.98      | r2_hidden(sK3(sK5,sK8),sK5) = iProver_top ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_1034,c_1041]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_15,plain,
% 3.45/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.45/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1045,plain,
% 3.45/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.45/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1673,plain,
% 3.45/0.98      ( k1_relset_1(sK5,sK6,sK8) = k1_relat_1(sK8) ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_1034,c_1045]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_3151,plain,
% 3.45/0.98      ( k1_relat_1(sK8) = sK5
% 3.45/0.98      | r2_hidden(sK3(sK5,sK8),sK5) = iProver_top ),
% 3.45/0.98      inference(demodulation,[status(thm)],[c_3148,c_1673]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1056,plain,
% 3.45/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.45/0.98      | v1_xboole_0(X1) != iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_3982,plain,
% 3.45/0.98      ( k1_relat_1(sK8) = sK5 | v1_xboole_0(sK5) != iProver_top ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_3151,c_1056]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_7569,plain,
% 3.45/0.98      ( k1_relat_1(sK8) = sK5 ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_7564,c_3982]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1049,plain,
% 3.45/0.98      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.45/0.98      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
% 3.45/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_3288,plain,
% 3.45/0.98      ( k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0
% 3.45/0.98      | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 3.45/0.98      | v1_relat_1(sK8) != iProver_top ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_1049,c_1031]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_3629,plain,
% 3.45/0.98      ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 3.45/0.98      | k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0 ),
% 3.45/0.98      inference(global_propositional_subsumption,
% 3.45/0.98                [status(thm)],
% 3.45/0.98                [c_3288,c_1512]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_3630,plain,
% 3.45/0.98      ( k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0
% 3.45/0.98      | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top ),
% 3.45/0.98      inference(renaming,[status(thm)],[c_3629]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_3640,plain,
% 3.45/0.98      ( k1_funct_1(sK8,sK1(sK9,sK7,sK8)) = sK9 ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_2316,c_3630]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_10,plain,
% 3.45/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.45/0.98      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.45/0.98      | ~ v1_funct_1(X1)
% 3.45/0.98      | ~ v1_relat_1(X1) ),
% 3.45/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_330,plain,
% 3.45/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.45/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.45/0.99      | ~ v1_relat_1(X1)
% 3.45/0.99      | sK8 != X1 ),
% 3.45/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_27]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_331,plain,
% 3.45/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK8))
% 3.45/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8)
% 3.45/0.99      | ~ v1_relat_1(sK8) ),
% 3.45/0.99      inference(unflattening,[status(thm)],[c_330]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1032,plain,
% 3.45/0.99      ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 3.45/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top
% 3.45/0.99      | v1_relat_1(sK8) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_331]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3669,plain,
% 3.45/0.99      ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) != iProver_top
% 3.45/0.99      | r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top
% 3.45/0.99      | v1_relat_1(sK8) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_3640,c_1032]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3790,plain,
% 3.45/0.99      ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_3669,c_1512,c_2316,c_2712]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_12,plain,
% 3.45/0.99      ( r2_hidden(X0,k1_relat_1(X1))
% 3.45/0.99      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.45/0.99      | ~ v1_funct_1(X1)
% 3.45/0.99      | ~ v1_relat_1(X1) ),
% 3.45/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_315,plain,
% 3.45/0.99      ( r2_hidden(X0,k1_relat_1(X1))
% 3.45/0.99      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.45/0.99      | ~ v1_relat_1(X1)
% 3.45/0.99      | sK8 != X1 ),
% 3.45/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_316,plain,
% 3.45/0.99      ( r2_hidden(X0,k1_relat_1(sK8))
% 3.45/0.99      | ~ r2_hidden(k4_tarski(X0,X1),sK8)
% 3.45/0.99      | ~ v1_relat_1(sK8) ),
% 3.45/0.99      inference(unflattening,[status(thm)],[c_315]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1033,plain,
% 3.45/0.99      ( r2_hidden(X0,k1_relat_1(sK8)) = iProver_top
% 3.45/0.99      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
% 3.45/0.99      | v1_relat_1(sK8) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_316]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3796,plain,
% 3.45/0.99      ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) = iProver_top
% 3.45/0.99      | v1_relat_1(sK8) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_3790,c_1033]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_9,plain,
% 3.45/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.45/0.99      | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
% 3.45/0.99      | ~ v1_relat_1(X1) ),
% 3.45/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2706,plain,
% 3.45/0.99      ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8))
% 3.45/0.99      | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
% 3.45/0.99      | ~ v1_relat_1(sK8) ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2710,plain,
% 3.45/0.99      ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) = iProver_top
% 3.45/0.99      | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
% 3.45/0.99      | v1_relat_1(sK8) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_2706]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3969,plain,
% 3.45/0.99      ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) = iProver_top ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_3796,c_1512,c_2316,c_2710]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3974,plain,
% 3.45/0.99      ( v1_xboole_0(k1_relat_1(sK8)) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_3969,c_1056]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_7823,plain,
% 3.45/0.99      ( v1_xboole_0(sK5) != iProver_top ),
% 3.45/0.99      inference(demodulation,[status(thm)],[c_7569,c_3974]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(contradiction,plain,
% 3.45/0.99      ( $false ),
% 3.45/0.99      inference(minisat,[status(thm)],[c_7823,c_7564]) ).
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.45/0.99  
% 3.45/0.99  ------                               Statistics
% 3.45/0.99  
% 3.45/0.99  ------ Selected
% 3.45/0.99  
% 3.45/0.99  total_time:                             0.264
% 3.45/0.99  
%------------------------------------------------------------------------------
