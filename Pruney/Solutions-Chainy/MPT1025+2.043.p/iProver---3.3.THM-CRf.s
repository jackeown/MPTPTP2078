%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:08 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :  147 (1001 expanded)
%              Number of clauses        :   82 ( 312 expanded)
%              Number of leaves         :   17 ( 222 expanded)
%              Depth                    :   22
%              Number of atoms          :  545 (4559 expanded)
%              Number of equality atoms :  182 ( 955 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(f30,plain,(
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
    inference(flattening,[],[f30])).

fof(f48,plain,(
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

fof(f47,plain,
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

fof(f49,plain,
    ( ! [X5] :
        ( k1_funct_1(sK6,X5) != sK7
        | ~ r2_hidden(X5,sK5)
        | ~ m1_subset_1(X5,sK3) )
    & r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f31,f48,f47])).

fof(f76,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f49])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X4,X3,X2,X1] :
      ( ? [X6] :
          ( r2_hidden(X6,X1)
          & r2_hidden(k4_tarski(X6,X4),X3)
          & m1_subset_1(X6,X2) )
     => ( r2_hidden(sK2(X1,X2,X3,X4),X1)
        & r2_hidden(k4_tarski(sK2(X1,X2,X3,X4),X4),X3)
        & m1_subset_1(sK2(X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f44,f45])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK2(X1,X2,X3,X4),X1)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

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

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

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
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f79,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f66])).

fof(f75,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f50,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
    r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
    inference(cnf_transformation,[],[f49])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK2(X1,X2,X3,X4),X4),X3)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f78,plain,(
    ! [X5] :
      ( k1_funct_1(sK6,X5) != sK7
      | ~ r2_hidden(X5,sK5)
      | ~ m1_subset_1(X5,sK3) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK2(X1,X2,X3,X4),X2)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1011,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1018,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2426,plain,
    ( k7_relset_1(sK3,sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_1011,c_1018])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | r2_hidden(sK2(X4,X3,X2,X0),X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1016,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | r2_hidden(sK2(X4,X3,X2,X0),X4) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3030,plain,
    ( m1_subset_1(X0,sK4) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(X1,sK3,sK6,X0),X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2426,c_1016])).

cnf(c_30,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1027,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2266,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1011,c_1027])).

cnf(c_9,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1026,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2711,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2266,c_1026])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1020,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3071,plain,
    ( v1_xboole_0(sK4) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1011,c_1020])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1021,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3151,plain,
    ( v1_xboole_0(sK3) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1011,c_1021])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1019,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2568,plain,
    ( m1_subset_1(k9_relat_1(sK6,X0),k1_zfmisc_1(sK4)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2426,c_1019])).

cnf(c_2876,plain,
    ( m1_subset_1(k9_relat_1(sK6,X0),k1_zfmisc_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2568,c_30])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1028,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3171,plain,
    ( m1_subset_1(X0,sK4) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2876,c_1028])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1022,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_337,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_28])).

cnf(c_338,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6)
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_337])).

cnf(c_1009,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_338])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1033,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1692,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1009,c_1033])).

cnf(c_3892,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1022,c_1692])).

cnf(c_4827,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(X1,sK3,sK6,X0),X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3030,c_30,c_2711,c_3071,c_3151,c_3171,c_3892])).

cnf(c_26,negated_conjecture,
    ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1012,plain,
    ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2558,plain,
    ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2426,c_1012])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | r2_hidden(k4_tarski(sK2(X4,X3,X2,X0),X0),X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1015,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X4,X3,X2,X0),X0),X2) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2569,plain,
    ( m1_subset_1(X0,sK4) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X1,sK3,sK6,X0),X0),sK6) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2426,c_1015])).

cnf(c_5510,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X1,sK3,sK6,X0),X0),sK6) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2569,c_30,c_2711,c_3071,c_3151,c_3171,c_3892])).

cnf(c_15,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_352,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_28])).

cnf(c_353,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK6)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_1008,plain,
    ( k1_funct_1(sK6,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_353])).

cnf(c_5524,plain,
    ( k1_funct_1(sK6,sK2(X0,sK3,sK6,X1)) = X1
    | r2_hidden(X1,k9_relat_1(sK6,X0)) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5510,c_1008])).

cnf(c_5598,plain,
    ( r2_hidden(X1,k9_relat_1(sK6,X0)) != iProver_top
    | k1_funct_1(sK6,sK2(X0,sK3,sK6,X1)) = X1
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5524,c_2711])).

cnf(c_5599,plain,
    ( k1_funct_1(sK6,sK2(X0,sK3,sK6,X1)) = X1
    | r2_hidden(X1,k9_relat_1(sK6,X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_5598])).

cnf(c_5610,plain,
    ( k1_funct_1(sK6,sK2(sK5,sK3,sK6,sK7)) = sK7
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2558,c_5599])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1024,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK1(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3294,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1024,c_1033])).

cnf(c_7602,plain,
    ( v1_relat_1(sK6) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2558,c_3294])).

cnf(c_7793,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7602,c_2711])).

cnf(c_7798,plain,
    ( k1_funct_1(sK6,sK2(sK5,sK3,sK6,sK7)) = sK7 ),
    inference(superposition,[status(thm)],[c_5610,c_7793])).

cnf(c_25,negated_conjecture,
    ( ~ m1_subset_1(X0,sK3)
    | ~ r2_hidden(X0,sK5)
    | k1_funct_1(sK6,X0) != sK7 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1013,plain,
    ( k1_funct_1(sK6,X0) != sK7
    | m1_subset_1(X0,sK3) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_8963,plain,
    ( m1_subset_1(sK2(sK5,sK3,sK6,sK7),sK3) != iProver_top
    | r2_hidden(sK2(sK5,sK3,sK6,sK7),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_7798,c_1013])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | m1_subset_1(sK2(X4,X3,X2,X0),X3)
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1014,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(sK2(X4,X3,X2,X0),X3) = iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1553,plain,
    ( m1_subset_1(sK2(sK5,sK3,sK6,sK7),sK3) = iProver_top
    | m1_subset_1(sK7,sK4) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1012,c_1014])).

cnf(c_5220,plain,
    ( m1_subset_1(sK7,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2558,c_3171])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1023,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3995,plain,
    ( k1_funct_1(sK6,sK1(X0,X1,sK6)) = X0
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1023,c_1008])).

cnf(c_4414,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | k1_funct_1(sK6,sK1(X0,X1,sK6)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3995,c_2711])).

cnf(c_4415,plain,
    ( k1_funct_1(sK6,sK1(X0,X1,sK6)) = X0
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4414])).

cnf(c_4425,plain,
    ( k1_funct_1(sK6,sK1(sK7,sK5,sK6)) = sK7 ),
    inference(superposition,[status(thm)],[c_2558,c_4415])).

cnf(c_4455,plain,
    ( r2_hidden(sK1(sK7,sK5,sK6),k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(sK1(sK7,sK5,sK6),sK7),sK6) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4425,c_1009])).

cnf(c_4598,plain,
    ( r2_hidden(k4_tarski(sK1(sK7,sK5,sK6),sK7),sK6) = iProver_top
    | r2_hidden(sK1(sK7,sK5,sK6),k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4455,c_2711])).

cnf(c_4599,plain,
    ( r2_hidden(sK1(sK7,sK5,sK6),k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(sK1(sK7,sK5,sK6),sK7),sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_4598])).

cnf(c_4604,plain,
    ( r2_hidden(sK1(sK7,sK5,sK6),k1_relat_1(sK6)) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4599,c_1033])).

cnf(c_6432,plain,
    ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1022,c_4604])).

cnf(c_9205,plain,
    ( r2_hidden(sK2(sK5,sK3,sK6,sK7),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8963,c_30,c_1553,c_2558,c_2711,c_3071,c_3151,c_5220,c_6432,c_7602])).

cnf(c_9210,plain,
    ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4827,c_9205])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9210,c_7602,c_2711,c_2558])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:35:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.98/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/0.98  
% 2.98/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.98/0.98  
% 2.98/0.98  ------  iProver source info
% 2.98/0.98  
% 2.98/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.98/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.98/0.98  git: non_committed_changes: false
% 2.98/0.98  git: last_make_outside_of_git: false
% 2.98/0.98  
% 2.98/0.98  ------ 
% 2.98/0.98  
% 2.98/0.98  ------ Input Options
% 2.98/0.98  
% 2.98/0.98  --out_options                           all
% 2.98/0.98  --tptp_safe_out                         true
% 2.98/0.98  --problem_path                          ""
% 2.98/0.98  --include_path                          ""
% 2.98/0.98  --clausifier                            res/vclausify_rel
% 2.98/0.98  --clausifier_options                    --mode clausify
% 2.98/0.98  --stdin                                 false
% 2.98/0.98  --stats_out                             all
% 2.98/0.98  
% 2.98/0.98  ------ General Options
% 2.98/0.98  
% 2.98/0.98  --fof                                   false
% 2.98/0.98  --time_out_real                         305.
% 2.98/0.98  --time_out_virtual                      -1.
% 2.98/0.98  --symbol_type_check                     false
% 2.98/0.98  --clausify_out                          false
% 2.98/0.98  --sig_cnt_out                           false
% 2.98/0.98  --trig_cnt_out                          false
% 2.98/0.98  --trig_cnt_out_tolerance                1.
% 2.98/0.98  --trig_cnt_out_sk_spl                   false
% 2.98/0.98  --abstr_cl_out                          false
% 2.98/0.98  
% 2.98/0.98  ------ Global Options
% 2.98/0.98  
% 2.98/0.98  --schedule                              default
% 2.98/0.98  --add_important_lit                     false
% 2.98/0.98  --prop_solver_per_cl                    1000
% 2.98/0.98  --min_unsat_core                        false
% 2.98/0.98  --soft_assumptions                      false
% 2.98/0.98  --soft_lemma_size                       3
% 2.98/0.98  --prop_impl_unit_size                   0
% 2.98/0.98  --prop_impl_unit                        []
% 2.98/0.98  --share_sel_clauses                     true
% 2.98/0.98  --reset_solvers                         false
% 2.98/0.98  --bc_imp_inh                            [conj_cone]
% 2.98/0.98  --conj_cone_tolerance                   3.
% 2.98/0.98  --extra_neg_conj                        none
% 2.98/0.98  --large_theory_mode                     true
% 2.98/0.98  --prolific_symb_bound                   200
% 2.98/0.98  --lt_threshold                          2000
% 2.98/0.98  --clause_weak_htbl                      true
% 2.98/0.98  --gc_record_bc_elim                     false
% 2.98/0.98  
% 2.98/0.98  ------ Preprocessing Options
% 2.98/0.98  
% 2.98/0.98  --preprocessing_flag                    true
% 2.98/0.98  --time_out_prep_mult                    0.1
% 2.98/0.98  --splitting_mode                        input
% 2.98/0.98  --splitting_grd                         true
% 2.98/0.98  --splitting_cvd                         false
% 2.98/0.98  --splitting_cvd_svl                     false
% 2.98/0.98  --splitting_nvd                         32
% 2.98/0.98  --sub_typing                            true
% 2.98/0.98  --prep_gs_sim                           true
% 2.98/0.98  --prep_unflatten                        true
% 2.98/0.98  --prep_res_sim                          true
% 2.98/0.98  --prep_upred                            true
% 2.98/0.98  --prep_sem_filter                       exhaustive
% 2.98/0.98  --prep_sem_filter_out                   false
% 2.98/0.98  --pred_elim                             true
% 2.98/0.98  --res_sim_input                         true
% 2.98/0.98  --eq_ax_congr_red                       true
% 2.98/0.98  --pure_diseq_elim                       true
% 2.98/0.98  --brand_transform                       false
% 2.98/0.98  --non_eq_to_eq                          false
% 2.98/0.98  --prep_def_merge                        true
% 2.98/0.98  --prep_def_merge_prop_impl              false
% 2.98/0.98  --prep_def_merge_mbd                    true
% 2.98/0.98  --prep_def_merge_tr_red                 false
% 2.98/0.98  --prep_def_merge_tr_cl                  false
% 2.98/0.98  --smt_preprocessing                     true
% 2.98/0.98  --smt_ac_axioms                         fast
% 2.98/0.98  --preprocessed_out                      false
% 2.98/0.98  --preprocessed_stats                    false
% 2.98/0.98  
% 2.98/0.98  ------ Abstraction refinement Options
% 2.98/0.98  
% 2.98/0.98  --abstr_ref                             []
% 2.98/0.98  --abstr_ref_prep                        false
% 2.98/0.98  --abstr_ref_until_sat                   false
% 2.98/0.98  --abstr_ref_sig_restrict                funpre
% 2.98/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.98/0.98  --abstr_ref_under                       []
% 2.98/0.98  
% 2.98/0.98  ------ SAT Options
% 2.98/0.98  
% 2.98/0.98  --sat_mode                              false
% 2.98/0.98  --sat_fm_restart_options                ""
% 2.98/0.98  --sat_gr_def                            false
% 2.98/0.98  --sat_epr_types                         true
% 2.98/0.98  --sat_non_cyclic_types                  false
% 2.98/0.98  --sat_finite_models                     false
% 2.98/0.98  --sat_fm_lemmas                         false
% 2.98/0.98  --sat_fm_prep                           false
% 2.98/0.98  --sat_fm_uc_incr                        true
% 2.98/0.98  --sat_out_model                         small
% 2.98/0.98  --sat_out_clauses                       false
% 2.98/0.98  
% 2.98/0.98  ------ QBF Options
% 2.98/0.98  
% 2.98/0.98  --qbf_mode                              false
% 2.98/0.98  --qbf_elim_univ                         false
% 2.98/0.98  --qbf_dom_inst                          none
% 2.98/0.98  --qbf_dom_pre_inst                      false
% 2.98/0.98  --qbf_sk_in                             false
% 2.98/0.98  --qbf_pred_elim                         true
% 2.98/0.98  --qbf_split                             512
% 2.98/0.98  
% 2.98/0.98  ------ BMC1 Options
% 2.98/0.98  
% 2.98/0.98  --bmc1_incremental                      false
% 2.98/0.98  --bmc1_axioms                           reachable_all
% 2.98/0.98  --bmc1_min_bound                        0
% 2.98/0.98  --bmc1_max_bound                        -1
% 2.98/0.98  --bmc1_max_bound_default                -1
% 2.98/0.98  --bmc1_symbol_reachability              true
% 2.98/0.98  --bmc1_property_lemmas                  false
% 2.98/0.98  --bmc1_k_induction                      false
% 2.98/0.98  --bmc1_non_equiv_states                 false
% 2.98/0.98  --bmc1_deadlock                         false
% 2.98/0.98  --bmc1_ucm                              false
% 2.98/0.98  --bmc1_add_unsat_core                   none
% 2.98/0.98  --bmc1_unsat_core_children              false
% 2.98/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.98/0.98  --bmc1_out_stat                         full
% 2.98/0.98  --bmc1_ground_init                      false
% 2.98/0.98  --bmc1_pre_inst_next_state              false
% 2.98/0.98  --bmc1_pre_inst_state                   false
% 2.98/0.98  --bmc1_pre_inst_reach_state             false
% 2.98/0.98  --bmc1_out_unsat_core                   false
% 2.98/0.98  --bmc1_aig_witness_out                  false
% 2.98/0.98  --bmc1_verbose                          false
% 2.98/0.98  --bmc1_dump_clauses_tptp                false
% 2.98/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.98/0.98  --bmc1_dump_file                        -
% 2.98/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.98/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.98/0.98  --bmc1_ucm_extend_mode                  1
% 2.98/0.98  --bmc1_ucm_init_mode                    2
% 2.98/0.98  --bmc1_ucm_cone_mode                    none
% 2.98/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.98/0.98  --bmc1_ucm_relax_model                  4
% 2.98/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.98/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.98/0.98  --bmc1_ucm_layered_model                none
% 2.98/0.98  --bmc1_ucm_max_lemma_size               10
% 2.98/0.98  
% 2.98/0.98  ------ AIG Options
% 2.98/0.98  
% 2.98/0.98  --aig_mode                              false
% 2.98/0.98  
% 2.98/0.98  ------ Instantiation Options
% 2.98/0.98  
% 2.98/0.98  --instantiation_flag                    true
% 2.98/0.98  --inst_sos_flag                         false
% 2.98/0.98  --inst_sos_phase                        true
% 2.98/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.98/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.98/0.98  --inst_lit_sel_side                     num_symb
% 2.98/0.98  --inst_solver_per_active                1400
% 2.98/0.98  --inst_solver_calls_frac                1.
% 2.98/0.98  --inst_passive_queue_type               priority_queues
% 2.98/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.98/0.98  --inst_passive_queues_freq              [25;2]
% 2.98/0.98  --inst_dismatching                      true
% 2.98/0.98  --inst_eager_unprocessed_to_passive     true
% 2.98/0.98  --inst_prop_sim_given                   true
% 2.98/0.98  --inst_prop_sim_new                     false
% 2.98/0.98  --inst_subs_new                         false
% 2.98/0.98  --inst_eq_res_simp                      false
% 2.98/0.98  --inst_subs_given                       false
% 2.98/0.98  --inst_orphan_elimination               true
% 2.98/0.98  --inst_learning_loop_flag               true
% 2.98/0.98  --inst_learning_start                   3000
% 2.98/0.98  --inst_learning_factor                  2
% 2.98/0.98  --inst_start_prop_sim_after_learn       3
% 2.98/0.98  --inst_sel_renew                        solver
% 2.98/0.98  --inst_lit_activity_flag                true
% 2.98/0.98  --inst_restr_to_given                   false
% 2.98/0.98  --inst_activity_threshold               500
% 2.98/0.98  --inst_out_proof                        true
% 2.98/0.98  
% 2.98/0.98  ------ Resolution Options
% 2.98/0.98  
% 2.98/0.98  --resolution_flag                       true
% 2.98/0.98  --res_lit_sel                           adaptive
% 2.98/0.98  --res_lit_sel_side                      none
% 2.98/0.98  --res_ordering                          kbo
% 2.98/0.98  --res_to_prop_solver                    active
% 2.98/0.98  --res_prop_simpl_new                    false
% 2.98/0.98  --res_prop_simpl_given                  true
% 2.98/0.98  --res_passive_queue_type                priority_queues
% 2.98/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.98/0.98  --res_passive_queues_freq               [15;5]
% 2.98/0.98  --res_forward_subs                      full
% 2.98/0.98  --res_backward_subs                     full
% 2.98/0.98  --res_forward_subs_resolution           true
% 2.98/0.98  --res_backward_subs_resolution          true
% 2.98/0.98  --res_orphan_elimination                true
% 2.98/0.98  --res_time_limit                        2.
% 2.98/0.98  --res_out_proof                         true
% 2.98/0.98  
% 2.98/0.98  ------ Superposition Options
% 2.98/0.98  
% 2.98/0.98  --superposition_flag                    true
% 2.98/0.98  --sup_passive_queue_type                priority_queues
% 2.98/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.98/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.98/0.98  --demod_completeness_check              fast
% 2.98/0.98  --demod_use_ground                      true
% 2.98/0.98  --sup_to_prop_solver                    passive
% 2.98/0.98  --sup_prop_simpl_new                    true
% 2.98/0.98  --sup_prop_simpl_given                  true
% 2.98/0.98  --sup_fun_splitting                     false
% 2.98/0.98  --sup_smt_interval                      50000
% 2.98/0.98  
% 2.98/0.98  ------ Superposition Simplification Setup
% 2.98/0.98  
% 2.98/0.98  --sup_indices_passive                   []
% 2.98/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.98/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.98  --sup_full_bw                           [BwDemod]
% 2.98/0.98  --sup_immed_triv                        [TrivRules]
% 2.98/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.98/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.98  --sup_immed_bw_main                     []
% 2.98/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.98/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/0.98  
% 2.98/0.98  ------ Combination Options
% 2.98/0.98  
% 2.98/0.98  --comb_res_mult                         3
% 2.98/0.98  --comb_sup_mult                         2
% 2.98/0.98  --comb_inst_mult                        10
% 2.98/0.98  
% 2.98/0.98  ------ Debug Options
% 2.98/0.98  
% 2.98/0.98  --dbg_backtrace                         false
% 2.98/0.98  --dbg_dump_prop_clauses                 false
% 2.98/0.98  --dbg_dump_prop_clauses_file            -
% 2.98/0.98  --dbg_out_stat                          false
% 2.98/0.98  ------ Parsing...
% 2.98/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.98/0.98  
% 2.98/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.98/0.98  
% 2.98/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.98/0.98  
% 2.98/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.98/0.98  ------ Proving...
% 2.98/0.98  ------ Problem Properties 
% 2.98/0.98  
% 2.98/0.98  
% 2.98/0.98  clauses                                 27
% 2.98/0.98  conjectures                             3
% 2.98/0.98  EPR                                     5
% 2.98/0.98  Horn                                    21
% 2.98/0.98  unary                                   3
% 2.98/0.98  binary                                  5
% 2.98/0.98  lits                                    90
% 2.98/0.98  lits eq                                 3
% 2.98/0.98  fd_pure                                 0
% 2.98/0.98  fd_pseudo                               0
% 2.98/0.98  fd_cond                                 0
% 2.98/0.98  fd_pseudo_cond                          1
% 2.98/0.98  AC symbols                              0
% 2.98/0.98  
% 2.98/0.98  ------ Schedule dynamic 5 is on 
% 2.98/0.98  
% 2.98/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.98/0.98  
% 2.98/0.98  
% 2.98/0.98  ------ 
% 2.98/0.98  Current options:
% 2.98/0.98  ------ 
% 2.98/0.98  
% 2.98/0.98  ------ Input Options
% 2.98/0.98  
% 2.98/0.98  --out_options                           all
% 2.98/0.98  --tptp_safe_out                         true
% 2.98/0.98  --problem_path                          ""
% 2.98/0.98  --include_path                          ""
% 2.98/0.98  --clausifier                            res/vclausify_rel
% 2.98/0.98  --clausifier_options                    --mode clausify
% 2.98/0.98  --stdin                                 false
% 2.98/0.98  --stats_out                             all
% 2.98/0.98  
% 2.98/0.98  ------ General Options
% 2.98/0.98  
% 2.98/0.98  --fof                                   false
% 2.98/0.98  --time_out_real                         305.
% 2.98/0.98  --time_out_virtual                      -1.
% 2.98/0.98  --symbol_type_check                     false
% 2.98/0.98  --clausify_out                          false
% 2.98/0.98  --sig_cnt_out                           false
% 2.98/0.98  --trig_cnt_out                          false
% 2.98/0.98  --trig_cnt_out_tolerance                1.
% 2.98/0.98  --trig_cnt_out_sk_spl                   false
% 2.98/0.98  --abstr_cl_out                          false
% 2.98/0.98  
% 2.98/0.98  ------ Global Options
% 2.98/0.98  
% 2.98/0.98  --schedule                              default
% 2.98/0.98  --add_important_lit                     false
% 2.98/0.98  --prop_solver_per_cl                    1000
% 2.98/0.98  --min_unsat_core                        false
% 2.98/0.98  --soft_assumptions                      false
% 2.98/0.98  --soft_lemma_size                       3
% 2.98/0.98  --prop_impl_unit_size                   0
% 2.98/0.98  --prop_impl_unit                        []
% 2.98/0.98  --share_sel_clauses                     true
% 2.98/0.98  --reset_solvers                         false
% 2.98/0.98  --bc_imp_inh                            [conj_cone]
% 2.98/0.98  --conj_cone_tolerance                   3.
% 2.98/0.98  --extra_neg_conj                        none
% 2.98/0.98  --large_theory_mode                     true
% 2.98/0.98  --prolific_symb_bound                   200
% 2.98/0.98  --lt_threshold                          2000
% 2.98/0.98  --clause_weak_htbl                      true
% 2.98/0.98  --gc_record_bc_elim                     false
% 2.98/0.98  
% 2.98/0.98  ------ Preprocessing Options
% 2.98/0.98  
% 2.98/0.98  --preprocessing_flag                    true
% 2.98/0.98  --time_out_prep_mult                    0.1
% 2.98/0.98  --splitting_mode                        input
% 2.98/0.98  --splitting_grd                         true
% 2.98/0.98  --splitting_cvd                         false
% 2.98/0.98  --splitting_cvd_svl                     false
% 2.98/0.98  --splitting_nvd                         32
% 2.98/0.98  --sub_typing                            true
% 2.98/0.98  --prep_gs_sim                           true
% 2.98/0.98  --prep_unflatten                        true
% 2.98/0.98  --prep_res_sim                          true
% 2.98/0.98  --prep_upred                            true
% 2.98/0.98  --prep_sem_filter                       exhaustive
% 2.98/0.98  --prep_sem_filter_out                   false
% 2.98/0.98  --pred_elim                             true
% 2.98/0.98  --res_sim_input                         true
% 2.98/0.98  --eq_ax_congr_red                       true
% 2.98/0.98  --pure_diseq_elim                       true
% 2.98/0.98  --brand_transform                       false
% 2.98/0.98  --non_eq_to_eq                          false
% 2.98/0.98  --prep_def_merge                        true
% 2.98/0.98  --prep_def_merge_prop_impl              false
% 2.98/0.98  --prep_def_merge_mbd                    true
% 2.98/0.98  --prep_def_merge_tr_red                 false
% 2.98/0.98  --prep_def_merge_tr_cl                  false
% 2.98/0.98  --smt_preprocessing                     true
% 2.98/0.98  --smt_ac_axioms                         fast
% 2.98/0.98  --preprocessed_out                      false
% 2.98/0.98  --preprocessed_stats                    false
% 2.98/0.98  
% 2.98/0.98  ------ Abstraction refinement Options
% 2.98/0.98  
% 2.98/0.98  --abstr_ref                             []
% 2.98/0.98  --abstr_ref_prep                        false
% 2.98/0.98  --abstr_ref_until_sat                   false
% 2.98/0.98  --abstr_ref_sig_restrict                funpre
% 2.98/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.98/0.98  --abstr_ref_under                       []
% 2.98/0.98  
% 2.98/0.98  ------ SAT Options
% 2.98/0.98  
% 2.98/0.98  --sat_mode                              false
% 2.98/0.98  --sat_fm_restart_options                ""
% 2.98/0.98  --sat_gr_def                            false
% 2.98/0.98  --sat_epr_types                         true
% 2.98/0.98  --sat_non_cyclic_types                  false
% 2.98/0.98  --sat_finite_models                     false
% 2.98/0.98  --sat_fm_lemmas                         false
% 2.98/0.98  --sat_fm_prep                           false
% 2.98/0.98  --sat_fm_uc_incr                        true
% 2.98/0.98  --sat_out_model                         small
% 2.98/0.98  --sat_out_clauses                       false
% 2.98/0.98  
% 2.98/0.98  ------ QBF Options
% 2.98/0.98  
% 2.98/0.98  --qbf_mode                              false
% 2.98/0.98  --qbf_elim_univ                         false
% 2.98/0.98  --qbf_dom_inst                          none
% 2.98/0.98  --qbf_dom_pre_inst                      false
% 2.98/0.98  --qbf_sk_in                             false
% 2.98/0.98  --qbf_pred_elim                         true
% 2.98/0.98  --qbf_split                             512
% 2.98/0.98  
% 2.98/0.98  ------ BMC1 Options
% 2.98/0.98  
% 2.98/0.98  --bmc1_incremental                      false
% 2.98/0.98  --bmc1_axioms                           reachable_all
% 2.98/0.98  --bmc1_min_bound                        0
% 2.98/0.98  --bmc1_max_bound                        -1
% 2.98/0.98  --bmc1_max_bound_default                -1
% 2.98/0.98  --bmc1_symbol_reachability              true
% 2.98/0.98  --bmc1_property_lemmas                  false
% 2.98/0.98  --bmc1_k_induction                      false
% 2.98/0.98  --bmc1_non_equiv_states                 false
% 2.98/0.98  --bmc1_deadlock                         false
% 2.98/0.98  --bmc1_ucm                              false
% 2.98/0.98  --bmc1_add_unsat_core                   none
% 2.98/0.98  --bmc1_unsat_core_children              false
% 2.98/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.98/0.98  --bmc1_out_stat                         full
% 2.98/0.98  --bmc1_ground_init                      false
% 2.98/0.98  --bmc1_pre_inst_next_state              false
% 2.98/0.98  --bmc1_pre_inst_state                   false
% 2.98/0.98  --bmc1_pre_inst_reach_state             false
% 2.98/0.98  --bmc1_out_unsat_core                   false
% 2.98/0.98  --bmc1_aig_witness_out                  false
% 2.98/0.98  --bmc1_verbose                          false
% 2.98/0.98  --bmc1_dump_clauses_tptp                false
% 2.98/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.98/0.98  --bmc1_dump_file                        -
% 2.98/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.98/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.98/0.98  --bmc1_ucm_extend_mode                  1
% 2.98/0.98  --bmc1_ucm_init_mode                    2
% 2.98/0.98  --bmc1_ucm_cone_mode                    none
% 2.98/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.98/0.98  --bmc1_ucm_relax_model                  4
% 2.98/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.98/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.98/0.98  --bmc1_ucm_layered_model                none
% 2.98/0.98  --bmc1_ucm_max_lemma_size               10
% 2.98/0.98  
% 2.98/0.98  ------ AIG Options
% 2.98/0.98  
% 2.98/0.98  --aig_mode                              false
% 2.98/0.98  
% 2.98/0.98  ------ Instantiation Options
% 2.98/0.98  
% 2.98/0.98  --instantiation_flag                    true
% 2.98/0.98  --inst_sos_flag                         false
% 2.98/0.98  --inst_sos_phase                        true
% 2.98/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.98/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.98/0.98  --inst_lit_sel_side                     none
% 2.98/0.98  --inst_solver_per_active                1400
% 2.98/0.98  --inst_solver_calls_frac                1.
% 2.98/0.98  --inst_passive_queue_type               priority_queues
% 2.98/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.98/0.98  --inst_passive_queues_freq              [25;2]
% 2.98/0.98  --inst_dismatching                      true
% 2.98/0.98  --inst_eager_unprocessed_to_passive     true
% 2.98/0.98  --inst_prop_sim_given                   true
% 2.98/0.98  --inst_prop_sim_new                     false
% 2.98/0.98  --inst_subs_new                         false
% 2.98/0.98  --inst_eq_res_simp                      false
% 2.98/0.98  --inst_subs_given                       false
% 2.98/0.98  --inst_orphan_elimination               true
% 2.98/0.98  --inst_learning_loop_flag               true
% 2.98/0.98  --inst_learning_start                   3000
% 2.98/0.98  --inst_learning_factor                  2
% 2.98/0.98  --inst_start_prop_sim_after_learn       3
% 2.98/0.98  --inst_sel_renew                        solver
% 2.98/0.98  --inst_lit_activity_flag                true
% 2.98/0.98  --inst_restr_to_given                   false
% 2.98/0.98  --inst_activity_threshold               500
% 2.98/0.98  --inst_out_proof                        true
% 2.98/0.98  
% 2.98/0.98  ------ Resolution Options
% 2.98/0.98  
% 2.98/0.98  --resolution_flag                       false
% 2.98/0.98  --res_lit_sel                           adaptive
% 2.98/0.98  --res_lit_sel_side                      none
% 2.98/0.98  --res_ordering                          kbo
% 2.98/0.98  --res_to_prop_solver                    active
% 2.98/0.98  --res_prop_simpl_new                    false
% 2.98/0.98  --res_prop_simpl_given                  true
% 2.98/0.98  --res_passive_queue_type                priority_queues
% 2.98/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.98/0.98  --res_passive_queues_freq               [15;5]
% 2.98/0.98  --res_forward_subs                      full
% 2.98/0.98  --res_backward_subs                     full
% 2.98/0.98  --res_forward_subs_resolution           true
% 2.98/0.98  --res_backward_subs_resolution          true
% 2.98/0.98  --res_orphan_elimination                true
% 2.98/0.98  --res_time_limit                        2.
% 2.98/0.98  --res_out_proof                         true
% 2.98/0.98  
% 2.98/0.98  ------ Superposition Options
% 2.98/0.98  
% 2.98/0.98  --superposition_flag                    true
% 2.98/0.98  --sup_passive_queue_type                priority_queues
% 2.98/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.98/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.98/0.98  --demod_completeness_check              fast
% 2.98/0.98  --demod_use_ground                      true
% 2.98/0.98  --sup_to_prop_solver                    passive
% 2.98/0.98  --sup_prop_simpl_new                    true
% 2.98/0.98  --sup_prop_simpl_given                  true
% 2.98/0.98  --sup_fun_splitting                     false
% 2.98/0.98  --sup_smt_interval                      50000
% 2.98/0.98  
% 2.98/0.98  ------ Superposition Simplification Setup
% 2.98/0.98  
% 2.98/0.98  --sup_indices_passive                   []
% 2.98/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.98/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.98  --sup_full_bw                           [BwDemod]
% 2.98/0.98  --sup_immed_triv                        [TrivRules]
% 2.98/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.98/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.98  --sup_immed_bw_main                     []
% 2.98/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.98/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/0.98  
% 2.98/0.98  ------ Combination Options
% 2.98/0.98  
% 2.98/0.98  --comb_res_mult                         3
% 2.98/0.98  --comb_sup_mult                         2
% 2.98/0.98  --comb_inst_mult                        10
% 2.98/0.98  
% 2.98/0.98  ------ Debug Options
% 2.98/0.98  
% 2.98/0.98  --dbg_backtrace                         false
% 2.98/0.98  --dbg_dump_prop_clauses                 false
% 2.98/0.98  --dbg_dump_prop_clauses_file            -
% 2.98/0.98  --dbg_out_stat                          false
% 2.98/0.98  
% 2.98/0.98  
% 2.98/0.98  
% 2.98/0.98  
% 2.98/0.98  ------ Proving...
% 2.98/0.98  
% 2.98/0.98  
% 2.98/0.98  % SZS status Theorem for theBenchmark.p
% 2.98/0.98  
% 2.98/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.98/0.98  
% 2.98/0.98  fof(f14,conjecture,(
% 2.98/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.98/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.98  
% 2.98/0.98  fof(f15,negated_conjecture,(
% 2.98/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.98/0.98    inference(negated_conjecture,[],[f14])).
% 2.98/0.98  
% 2.98/0.98  fof(f16,plain,(
% 2.98/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.98/0.98    inference(pure_predicate_removal,[],[f15])).
% 2.98/0.98  
% 2.98/0.98  fof(f30,plain,(
% 2.98/0.98    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 2.98/0.98    inference(ennf_transformation,[],[f16])).
% 2.98/0.98  
% 2.98/0.98  fof(f31,plain,(
% 2.98/0.98    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 2.98/0.98    inference(flattening,[],[f30])).
% 2.98/0.98  
% 2.98/0.98  fof(f48,plain,(
% 2.98/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK7 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(sK7,k7_relset_1(X0,X1,X3,X2)))) )),
% 2.98/0.98    introduced(choice_axiom,[])).
% 2.98/0.98  
% 2.98/0.98  fof(f47,plain,(
% 2.98/0.98    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK6,X5) != X4 | ~r2_hidden(X5,sK5) | ~m1_subset_1(X5,sK3)) & r2_hidden(X4,k7_relset_1(sK3,sK4,sK6,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK6))),
% 2.98/0.98    introduced(choice_axiom,[])).
% 2.98/0.98  
% 2.98/0.98  fof(f49,plain,(
% 2.98/0.98    (! [X5] : (k1_funct_1(sK6,X5) != sK7 | ~r2_hidden(X5,sK5) | ~m1_subset_1(X5,sK3)) & r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK6)),
% 2.98/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f31,f48,f47])).
% 2.98/0.98  
% 2.98/0.98  fof(f76,plain,(
% 2.98/0.98    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 2.98/0.98    inference(cnf_transformation,[],[f49])).
% 2.98/0.98  
% 2.98/0.98  fof(f12,axiom,(
% 2.98/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.98/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.98  
% 2.98/0.98  fof(f28,plain,(
% 2.98/0.98    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.98/0.98    inference(ennf_transformation,[],[f12])).
% 2.98/0.98  
% 2.98/0.98  fof(f70,plain,(
% 2.98/0.98    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.98/0.98    inference(cnf_transformation,[],[f28])).
% 2.98/0.98  
% 2.98/0.98  fof(f13,axiom,(
% 2.98/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 2.98/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.98  
% 2.98/0.98  fof(f29,plain,(
% 2.98/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.98/0.98    inference(ennf_transformation,[],[f13])).
% 2.98/0.98  
% 2.98/0.98  fof(f43,plain,(
% 2.98/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.98/0.98    inference(nnf_transformation,[],[f29])).
% 2.98/0.98  
% 2.98/0.98  fof(f44,plain,(
% 2.98/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.98/0.98    inference(rectify,[],[f43])).
% 2.98/0.98  
% 2.98/0.98  fof(f45,plain,(
% 2.98/0.98    ! [X4,X3,X2,X1] : (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) => (r2_hidden(sK2(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK2(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK2(X1,X2,X3,X4),X2)))),
% 2.98/0.98    introduced(choice_axiom,[])).
% 2.98/0.98  
% 2.98/0.98  fof(f46,plain,(
% 2.98/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & ((r2_hidden(sK2(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK2(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK2(X1,X2,X3,X4),X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.98/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f44,f45])).
% 2.98/0.98  
% 2.98/0.98  fof(f73,plain,(
% 2.98/0.98    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK2(X1,X2,X3,X4),X1) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.98/0.98    inference(cnf_transformation,[],[f46])).
% 2.98/0.98  
% 2.98/0.98  fof(f5,axiom,(
% 2.98/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.98/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.98  
% 2.98/0.98  fof(f21,plain,(
% 2.98/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.98/0.98    inference(ennf_transformation,[],[f5])).
% 2.98/0.98  
% 2.98/0.98  fof(f58,plain,(
% 2.98/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.98/0.98    inference(cnf_transformation,[],[f21])).
% 2.98/0.98  
% 2.98/0.98  fof(f6,axiom,(
% 2.98/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.98/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.98  
% 2.98/0.98  fof(f59,plain,(
% 2.98/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.98/0.98    inference(cnf_transformation,[],[f6])).
% 2.98/0.98  
% 2.98/0.98  fof(f10,axiom,(
% 2.98/0.98    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.98/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.98  
% 2.98/0.98  fof(f26,plain,(
% 2.98/0.98    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.98/0.99    inference(ennf_transformation,[],[f10])).
% 2.98/0.99  
% 2.98/0.99  fof(f68,plain,(
% 2.98/0.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f26])).
% 2.98/0.99  
% 2.98/0.99  fof(f9,axiom,(
% 2.98/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 2.98/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f25,plain,(
% 2.98/0.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.98/0.99    inference(ennf_transformation,[],[f9])).
% 2.98/0.99  
% 2.98/0.99  fof(f67,plain,(
% 2.98/0.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f25])).
% 2.98/0.99  
% 2.98/0.99  fof(f11,axiom,(
% 2.98/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 2.98/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f27,plain,(
% 2.98/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.98/0.99    inference(ennf_transformation,[],[f11])).
% 2.98/0.99  
% 2.98/0.99  fof(f69,plain,(
% 2.98/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.98/0.99    inference(cnf_transformation,[],[f27])).
% 2.98/0.99  
% 2.98/0.99  fof(f4,axiom,(
% 2.98/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.98/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f19,plain,(
% 2.98/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.98/0.99    inference(ennf_transformation,[],[f4])).
% 2.98/0.99  
% 2.98/0.99  fof(f20,plain,(
% 2.98/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.98/0.99    inference(flattening,[],[f19])).
% 2.98/0.99  
% 2.98/0.99  fof(f57,plain,(
% 2.98/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f20])).
% 2.98/0.99  
% 2.98/0.99  fof(f7,axiom,(
% 2.98/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 2.98/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f22,plain,(
% 2.98/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 2.98/0.99    inference(ennf_transformation,[],[f7])).
% 2.98/0.99  
% 2.98/0.99  fof(f37,plain,(
% 2.98/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.98/0.99    inference(nnf_transformation,[],[f22])).
% 2.98/0.99  
% 2.98/0.99  fof(f38,plain,(
% 2.98/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.98/0.99    inference(rectify,[],[f37])).
% 2.98/0.99  
% 2.98/0.99  fof(f39,plain,(
% 2.98/0.99    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 2.98/0.99    introduced(choice_axiom,[])).
% 2.98/0.99  
% 2.98/0.99  fof(f40,plain,(
% 2.98/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.98/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).
% 2.98/0.99  
% 2.98/0.99  fof(f60,plain,(
% 2.98/0.99    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f40])).
% 2.98/0.99  
% 2.98/0.99  fof(f8,axiom,(
% 2.98/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 2.98/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f23,plain,(
% 2.98/0.99    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.98/0.99    inference(ennf_transformation,[],[f8])).
% 2.98/0.99  
% 2.98/0.99  fof(f24,plain,(
% 2.98/0.99    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.98/0.99    inference(flattening,[],[f23])).
% 2.98/0.99  
% 2.98/0.99  fof(f41,plain,(
% 2.98/0.99    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.98/0.99    inference(nnf_transformation,[],[f24])).
% 2.98/0.99  
% 2.98/0.99  fof(f42,plain,(
% 2.98/0.99    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.98/0.99    inference(flattening,[],[f41])).
% 2.98/0.99  
% 2.98/0.99  fof(f66,plain,(
% 2.98/0.99    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f42])).
% 2.98/0.99  
% 2.98/0.99  fof(f79,plain,(
% 2.98/0.99    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.98/0.99    inference(equality_resolution,[],[f66])).
% 2.98/0.99  
% 2.98/0.99  fof(f75,plain,(
% 2.98/0.99    v1_funct_1(sK6)),
% 2.98/0.99    inference(cnf_transformation,[],[f49])).
% 2.98/0.99  
% 2.98/0.99  fof(f1,axiom,(
% 2.98/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.98/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f32,plain,(
% 2.98/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.98/0.99    inference(nnf_transformation,[],[f1])).
% 2.98/0.99  
% 2.98/0.99  fof(f33,plain,(
% 2.98/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.98/0.99    inference(rectify,[],[f32])).
% 2.98/0.99  
% 2.98/0.99  fof(f34,plain,(
% 2.98/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.98/0.99    introduced(choice_axiom,[])).
% 2.98/0.99  
% 2.98/0.99  fof(f35,plain,(
% 2.98/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.98/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 2.98/0.99  
% 2.98/0.99  fof(f50,plain,(
% 2.98/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f35])).
% 2.98/0.99  
% 2.98/0.99  fof(f77,plain,(
% 2.98/0.99    r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))),
% 2.98/0.99    inference(cnf_transformation,[],[f49])).
% 2.98/0.99  
% 2.98/0.99  fof(f72,plain,(
% 2.98/0.99    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK2(X1,X2,X3,X4),X4),X3) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f46])).
% 2.98/0.99  
% 2.98/0.99  fof(f65,plain,(
% 2.98/0.99    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f42])).
% 2.98/0.99  
% 2.98/0.99  fof(f62,plain,(
% 2.98/0.99    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f40])).
% 2.98/0.99  
% 2.98/0.99  fof(f78,plain,(
% 2.98/0.99    ( ! [X5] : (k1_funct_1(sK6,X5) != sK7 | ~r2_hidden(X5,sK5) | ~m1_subset_1(X5,sK3)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f49])).
% 2.98/0.99  
% 2.98/0.99  fof(f71,plain,(
% 2.98/0.99    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK2(X1,X2,X3,X4),X2) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f46])).
% 2.98/0.99  
% 2.98/0.99  fof(f61,plain,(
% 2.98/0.99    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f40])).
% 2.98/0.99  
% 2.98/0.99  cnf(c_27,negated_conjecture,
% 2.98/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 2.98/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1011,plain,
% 2.98/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_20,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.98/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1018,plain,
% 2.98/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.98/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2426,plain,
% 2.98/0.99      ( k7_relset_1(sK3,sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_1011,c_1018]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_22,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0,X1)
% 2.98/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 2.98/0.99      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 2.98/0.99      | r2_hidden(sK2(X4,X3,X2,X0),X4)
% 2.98/0.99      | v1_xboole_0(X1)
% 2.98/0.99      | v1_xboole_0(X3)
% 2.98/0.99      | v1_xboole_0(X4) ),
% 2.98/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1016,plain,
% 2.98/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 2.98/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 2.98/0.99      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 2.98/0.99      | r2_hidden(sK2(X4,X3,X2,X0),X4) = iProver_top
% 2.98/0.99      | v1_xboole_0(X1) = iProver_top
% 2.98/0.99      | v1_xboole_0(X3) = iProver_top
% 2.98/0.99      | v1_xboole_0(X4) = iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3030,plain,
% 2.98/0.99      ( m1_subset_1(X0,sK4) != iProver_top
% 2.98/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 2.98/0.99      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 2.98/0.99      | r2_hidden(sK2(X1,sK3,sK6,X0),X1) = iProver_top
% 2.98/0.99      | v1_xboole_0(X1) = iProver_top
% 2.98/0.99      | v1_xboole_0(sK4) = iProver_top
% 2.98/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_2426,c_1016]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_30,plain,
% 2.98/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_8,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.98/0.99      | ~ v1_relat_1(X1)
% 2.98/0.99      | v1_relat_1(X0) ),
% 2.98/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1027,plain,
% 2.98/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.98/0.99      | v1_relat_1(X1) != iProver_top
% 2.98/0.99      | v1_relat_1(X0) = iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2266,plain,
% 2.98/0.99      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
% 2.98/0.99      | v1_relat_1(sK6) = iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_1011,c_1027]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_9,plain,
% 2.98/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.98/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1026,plain,
% 2.98/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2711,plain,
% 2.98/0.99      ( v1_relat_1(sK6) = iProver_top ),
% 2.98/0.99      inference(forward_subsumption_resolution,
% 2.98/0.99                [status(thm)],
% 2.98/0.99                [c_2266,c_1026]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_18,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/0.99      | ~ v1_xboole_0(X2)
% 2.98/0.99      | v1_xboole_0(X0) ),
% 2.98/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1020,plain,
% 2.98/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.98/0.99      | v1_xboole_0(X2) != iProver_top
% 2.98/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3071,plain,
% 2.98/0.99      ( v1_xboole_0(sK4) != iProver_top
% 2.98/0.99      | v1_xboole_0(sK6) = iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_1011,c_1020]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_17,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/0.99      | ~ v1_xboole_0(X1)
% 2.98/0.99      | v1_xboole_0(X0) ),
% 2.98/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1021,plain,
% 2.98/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.98/0.99      | v1_xboole_0(X1) != iProver_top
% 2.98/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3151,plain,
% 2.98/0.99      ( v1_xboole_0(sK3) != iProver_top
% 2.98/0.99      | v1_xboole_0(sK6) = iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_1011,c_1021]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_19,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/0.99      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
% 2.98/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1019,plain,
% 2.98/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.98/0.99      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2568,plain,
% 2.98/0.99      ( m1_subset_1(k9_relat_1(sK6,X0),k1_zfmisc_1(sK4)) = iProver_top
% 2.98/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_2426,c_1019]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2876,plain,
% 2.98/0.99      ( m1_subset_1(k9_relat_1(sK6,X0),k1_zfmisc_1(sK4)) = iProver_top ),
% 2.98/0.99      inference(global_propositional_subsumption,
% 2.98/0.99                [status(thm)],
% 2.98/0.99                [c_2568,c_30]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_7,plain,
% 2.98/0.99      ( m1_subset_1(X0,X1)
% 2.98/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.98/0.99      | ~ r2_hidden(X0,X2) ),
% 2.98/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1028,plain,
% 2.98/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 2.98/0.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.98/0.99      | r2_hidden(X0,X2) != iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3171,plain,
% 2.98/0.99      ( m1_subset_1(X0,sK4) = iProver_top
% 2.98/0.99      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_2876,c_1028]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_13,plain,
% 2.98/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.98/0.99      | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
% 2.98/0.99      | ~ v1_relat_1(X1) ),
% 2.98/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1022,plain,
% 2.98/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.98/0.99      | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 2.98/0.99      | v1_relat_1(X1) != iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_14,plain,
% 2.98/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.98/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 2.98/0.99      | ~ v1_funct_1(X1)
% 2.98/0.99      | ~ v1_relat_1(X1) ),
% 2.98/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_28,negated_conjecture,
% 2.98/0.99      ( v1_funct_1(sK6) ),
% 2.98/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_337,plain,
% 2.98/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.98/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 2.98/0.99      | ~ v1_relat_1(X1)
% 2.98/0.99      | sK6 != X1 ),
% 2.98/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_28]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_338,plain,
% 2.98/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 2.98/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6)
% 2.98/0.99      | ~ v1_relat_1(sK6) ),
% 2.98/0.99      inference(unflattening,[status(thm)],[c_337]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1009,plain,
% 2.98/0.99      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 2.98/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
% 2.98/0.99      | v1_relat_1(sK6) != iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_338]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1,plain,
% 2.98/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.98/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1033,plain,
% 2.98/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.98/0.99      | v1_xboole_0(X1) != iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1692,plain,
% 2.98/0.99      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 2.98/0.99      | v1_relat_1(sK6) != iProver_top
% 2.98/0.99      | v1_xboole_0(sK6) != iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_1009,c_1033]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3892,plain,
% 2.98/0.99      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 2.98/0.99      | v1_relat_1(sK6) != iProver_top
% 2.98/0.99      | v1_xboole_0(sK6) != iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_1022,c_1692]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_4827,plain,
% 2.98/0.99      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 2.98/0.99      | r2_hidden(sK2(X1,sK3,sK6,X0),X1) = iProver_top
% 2.98/0.99      | v1_xboole_0(X1) = iProver_top ),
% 2.98/0.99      inference(global_propositional_subsumption,
% 2.98/0.99                [status(thm)],
% 2.98/0.99                [c_3030,c_30,c_2711,c_3071,c_3151,c_3171,c_3892]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_26,negated_conjecture,
% 2.98/0.99      ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
% 2.98/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1012,plain,
% 2.98/0.99      ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2558,plain,
% 2.98/0.99      ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) = iProver_top ),
% 2.98/0.99      inference(demodulation,[status(thm)],[c_2426,c_1012]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_23,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0,X1)
% 2.98/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 2.98/0.99      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 2.98/0.99      | r2_hidden(k4_tarski(sK2(X4,X3,X2,X0),X0),X2)
% 2.98/0.99      | v1_xboole_0(X1)
% 2.98/0.99      | v1_xboole_0(X3)
% 2.98/0.99      | v1_xboole_0(X4) ),
% 2.98/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1015,plain,
% 2.98/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 2.98/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 2.98/0.99      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 2.98/0.99      | r2_hidden(k4_tarski(sK2(X4,X3,X2,X0),X0),X2) = iProver_top
% 2.98/0.99      | v1_xboole_0(X1) = iProver_top
% 2.98/0.99      | v1_xboole_0(X3) = iProver_top
% 2.98/0.99      | v1_xboole_0(X4) = iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2569,plain,
% 2.98/0.99      ( m1_subset_1(X0,sK4) != iProver_top
% 2.98/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 2.98/0.99      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 2.98/0.99      | r2_hidden(k4_tarski(sK2(X1,sK3,sK6,X0),X0),sK6) = iProver_top
% 2.98/0.99      | v1_xboole_0(X1) = iProver_top
% 2.98/0.99      | v1_xboole_0(sK4) = iProver_top
% 2.98/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_2426,c_1015]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_5510,plain,
% 2.98/0.99      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 2.98/0.99      | r2_hidden(k4_tarski(sK2(X1,sK3,sK6,X0),X0),sK6) = iProver_top
% 2.98/0.99      | v1_xboole_0(X1) = iProver_top ),
% 2.98/0.99      inference(global_propositional_subsumption,
% 2.98/0.99                [status(thm)],
% 2.98/0.99                [c_2569,c_30,c_2711,c_3071,c_3151,c_3171,c_3892]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_15,plain,
% 2.98/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 2.98/0.99      | ~ v1_funct_1(X2)
% 2.98/0.99      | ~ v1_relat_1(X2)
% 2.98/0.99      | k1_funct_1(X2,X0) = X1 ),
% 2.98/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_352,plain,
% 2.98/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 2.98/0.99      | ~ v1_relat_1(X2)
% 2.98/0.99      | k1_funct_1(X2,X0) = X1
% 2.98/0.99      | sK6 != X2 ),
% 2.98/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_28]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_353,plain,
% 2.98/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),sK6)
% 2.98/0.99      | ~ v1_relat_1(sK6)
% 2.98/0.99      | k1_funct_1(sK6,X0) = X1 ),
% 2.98/0.99      inference(unflattening,[status(thm)],[c_352]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1008,plain,
% 2.98/0.99      ( k1_funct_1(sK6,X0) = X1
% 2.98/0.99      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
% 2.98/0.99      | v1_relat_1(sK6) != iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_353]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_5524,plain,
% 2.98/0.99      ( k1_funct_1(sK6,sK2(X0,sK3,sK6,X1)) = X1
% 2.98/0.99      | r2_hidden(X1,k9_relat_1(sK6,X0)) != iProver_top
% 2.98/0.99      | v1_relat_1(sK6) != iProver_top
% 2.98/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_5510,c_1008]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_5598,plain,
% 2.98/0.99      ( r2_hidden(X1,k9_relat_1(sK6,X0)) != iProver_top
% 2.98/0.99      | k1_funct_1(sK6,sK2(X0,sK3,sK6,X1)) = X1
% 2.98/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.98/0.99      inference(global_propositional_subsumption,
% 2.98/0.99                [status(thm)],
% 2.98/0.99                [c_5524,c_2711]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_5599,plain,
% 2.98/0.99      ( k1_funct_1(sK6,sK2(X0,sK3,sK6,X1)) = X1
% 2.98/0.99      | r2_hidden(X1,k9_relat_1(sK6,X0)) != iProver_top
% 2.98/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.98/0.99      inference(renaming,[status(thm)],[c_5598]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_5610,plain,
% 2.98/0.99      ( k1_funct_1(sK6,sK2(sK5,sK3,sK6,sK7)) = sK7
% 2.98/0.99      | v1_xboole_0(sK5) = iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_2558,c_5599]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_11,plain,
% 2.98/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.98/0.99      | r2_hidden(sK1(X0,X2,X1),X2)
% 2.98/0.99      | ~ v1_relat_1(X1) ),
% 2.98/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1024,plain,
% 2.98/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.98/0.99      | r2_hidden(sK1(X0,X2,X1),X2) = iProver_top
% 2.98/0.99      | v1_relat_1(X1) != iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3294,plain,
% 2.98/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.98/0.99      | v1_relat_1(X1) != iProver_top
% 2.98/0.99      | v1_xboole_0(X2) != iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_1024,c_1033]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_7602,plain,
% 2.98/0.99      ( v1_relat_1(sK6) != iProver_top
% 2.98/0.99      | v1_xboole_0(sK5) != iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_2558,c_3294]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_7793,plain,
% 2.98/0.99      ( v1_xboole_0(sK5) != iProver_top ),
% 2.98/0.99      inference(global_propositional_subsumption,
% 2.98/0.99                [status(thm)],
% 2.98/0.99                [c_7602,c_2711]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_7798,plain,
% 2.98/0.99      ( k1_funct_1(sK6,sK2(sK5,sK3,sK6,sK7)) = sK7 ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_5610,c_7793]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_25,negated_conjecture,
% 2.98/0.99      ( ~ m1_subset_1(X0,sK3)
% 2.98/0.99      | ~ r2_hidden(X0,sK5)
% 2.98/0.99      | k1_funct_1(sK6,X0) != sK7 ),
% 2.98/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1013,plain,
% 2.98/0.99      ( k1_funct_1(sK6,X0) != sK7
% 2.98/0.99      | m1_subset_1(X0,sK3) != iProver_top
% 2.98/0.99      | r2_hidden(X0,sK5) != iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_8963,plain,
% 2.98/0.99      ( m1_subset_1(sK2(sK5,sK3,sK6,sK7),sK3) != iProver_top
% 2.98/0.99      | r2_hidden(sK2(sK5,sK3,sK6,sK7),sK5) != iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_7798,c_1013]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_24,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0,X1)
% 2.98/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 2.98/0.99      | m1_subset_1(sK2(X4,X3,X2,X0),X3)
% 2.98/0.99      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 2.98/0.99      | v1_xboole_0(X1)
% 2.98/0.99      | v1_xboole_0(X3)
% 2.98/0.99      | v1_xboole_0(X4) ),
% 2.98/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1014,plain,
% 2.98/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 2.98/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 2.98/0.99      | m1_subset_1(sK2(X4,X3,X2,X0),X3) = iProver_top
% 2.98/0.99      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 2.98/0.99      | v1_xboole_0(X1) = iProver_top
% 2.98/0.99      | v1_xboole_0(X3) = iProver_top
% 2.98/0.99      | v1_xboole_0(X4) = iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1553,plain,
% 2.98/0.99      ( m1_subset_1(sK2(sK5,sK3,sK6,sK7),sK3) = iProver_top
% 2.98/0.99      | m1_subset_1(sK7,sK4) != iProver_top
% 2.98/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 2.98/0.99      | v1_xboole_0(sK4) = iProver_top
% 2.98/0.99      | v1_xboole_0(sK3) = iProver_top
% 2.98/0.99      | v1_xboole_0(sK5) = iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_1012,c_1014]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_5220,plain,
% 2.98/0.99      ( m1_subset_1(sK7,sK4) = iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_2558,c_3171]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_12,plain,
% 2.98/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.98/0.99      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 2.98/0.99      | ~ v1_relat_1(X1) ),
% 2.98/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1023,plain,
% 2.98/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.98/0.99      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
% 2.98/0.99      | v1_relat_1(X1) != iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3995,plain,
% 2.98/0.99      ( k1_funct_1(sK6,sK1(X0,X1,sK6)) = X0
% 2.98/0.99      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 2.98/0.99      | v1_relat_1(sK6) != iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_1023,c_1008]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_4414,plain,
% 2.98/0.99      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 2.98/0.99      | k1_funct_1(sK6,sK1(X0,X1,sK6)) = X0 ),
% 2.98/0.99      inference(global_propositional_subsumption,
% 2.98/0.99                [status(thm)],
% 2.98/0.99                [c_3995,c_2711]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_4415,plain,
% 2.98/0.99      ( k1_funct_1(sK6,sK1(X0,X1,sK6)) = X0
% 2.98/0.99      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
% 2.98/0.99      inference(renaming,[status(thm)],[c_4414]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_4425,plain,
% 2.98/0.99      ( k1_funct_1(sK6,sK1(sK7,sK5,sK6)) = sK7 ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_2558,c_4415]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_4455,plain,
% 2.98/0.99      ( r2_hidden(sK1(sK7,sK5,sK6),k1_relat_1(sK6)) != iProver_top
% 2.98/0.99      | r2_hidden(k4_tarski(sK1(sK7,sK5,sK6),sK7),sK6) = iProver_top
% 2.98/0.99      | v1_relat_1(sK6) != iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_4425,c_1009]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_4598,plain,
% 2.98/0.99      ( r2_hidden(k4_tarski(sK1(sK7,sK5,sK6),sK7),sK6) = iProver_top
% 2.98/0.99      | r2_hidden(sK1(sK7,sK5,sK6),k1_relat_1(sK6)) != iProver_top ),
% 2.98/0.99      inference(global_propositional_subsumption,
% 2.98/0.99                [status(thm)],
% 2.98/0.99                [c_4455,c_2711]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_4599,plain,
% 2.98/0.99      ( r2_hidden(sK1(sK7,sK5,sK6),k1_relat_1(sK6)) != iProver_top
% 2.98/0.99      | r2_hidden(k4_tarski(sK1(sK7,sK5,sK6),sK7),sK6) = iProver_top ),
% 2.98/0.99      inference(renaming,[status(thm)],[c_4598]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_4604,plain,
% 2.98/0.99      ( r2_hidden(sK1(sK7,sK5,sK6),k1_relat_1(sK6)) != iProver_top
% 2.98/0.99      | v1_xboole_0(sK6) != iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_4599,c_1033]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_6432,plain,
% 2.98/0.99      ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
% 2.98/0.99      | v1_relat_1(sK6) != iProver_top
% 2.98/0.99      | v1_xboole_0(sK6) != iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_1022,c_4604]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_9205,plain,
% 2.98/0.99      ( r2_hidden(sK2(sK5,sK3,sK6,sK7),sK5) != iProver_top ),
% 2.98/0.99      inference(global_propositional_subsumption,
% 2.98/0.99                [status(thm)],
% 2.98/0.99                [c_8963,c_30,c_1553,c_2558,c_2711,c_3071,c_3151,c_5220,
% 2.98/0.99                 c_6432,c_7602]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_9210,plain,
% 2.98/0.99      ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
% 2.98/0.99      | v1_xboole_0(sK5) = iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_4827,c_9205]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(contradiction,plain,
% 2.98/0.99      ( $false ),
% 2.98/0.99      inference(minisat,[status(thm)],[c_9210,c_7602,c_2711,c_2558]) ).
% 2.98/0.99  
% 2.98/0.99  
% 2.98/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.98/0.99  
% 2.98/0.99  ------                               Statistics
% 2.98/0.99  
% 2.98/0.99  ------ General
% 2.98/0.99  
% 2.98/0.99  abstr_ref_over_cycles:                  0
% 2.98/0.99  abstr_ref_under_cycles:                 0
% 2.98/0.99  gc_basic_clause_elim:                   0
% 2.98/0.99  forced_gc_time:                         0
% 2.98/0.99  parsing_time:                           0.01
% 2.98/0.99  unif_index_cands_time:                  0.
% 2.98/0.99  unif_index_add_time:                    0.
% 2.98/0.99  orderings_time:                         0.
% 2.98/0.99  out_proof_time:                         0.01
% 2.98/0.99  total_time:                             0.353
% 2.98/0.99  num_of_symbols:                         51
% 2.98/0.99  num_of_terms:                           10655
% 2.98/0.99  
% 2.98/0.99  ------ Preprocessing
% 2.98/0.99  
% 2.98/0.99  num_of_splits:                          0
% 2.98/0.99  num_of_split_atoms:                     0
% 2.98/0.99  num_of_reused_defs:                     0
% 2.98/0.99  num_eq_ax_congr_red:                    37
% 2.98/0.99  num_of_sem_filtered_clauses:            1
% 2.98/0.99  num_of_subtypes:                        0
% 2.98/0.99  monotx_restored_types:                  0
% 2.98/0.99  sat_num_of_epr_types:                   0
% 2.98/0.99  sat_num_of_non_cyclic_types:            0
% 2.98/0.99  sat_guarded_non_collapsed_types:        0
% 2.98/0.99  num_pure_diseq_elim:                    0
% 2.98/0.99  simp_replaced_by:                       0
% 2.98/0.99  res_preprocessed:                       132
% 2.98/0.99  prep_upred:                             0
% 2.98/0.99  prep_unflattend:                        3
% 2.98/0.99  smt_new_axioms:                         0
% 2.98/0.99  pred_elim_cands:                        4
% 2.98/0.99  pred_elim:                              1
% 2.98/0.99  pred_elim_cl:                           1
% 2.98/0.99  pred_elim_cycles:                       3
% 2.98/0.99  merged_defs:                            0
% 2.98/0.99  merged_defs_ncl:                        0
% 2.98/0.99  bin_hyper_res:                          0
% 2.98/0.99  prep_cycles:                            4
% 2.98/0.99  pred_elim_time:                         0.002
% 2.98/0.99  splitting_time:                         0.
% 2.98/0.99  sem_filter_time:                        0.
% 2.98/0.99  monotx_time:                            0.001
% 2.98/0.99  subtype_inf_time:                       0.
% 2.98/0.99  
% 2.98/0.99  ------ Problem properties
% 2.98/0.99  
% 2.98/0.99  clauses:                                27
% 2.98/0.99  conjectures:                            3
% 2.98/0.99  epr:                                    5
% 2.98/0.99  horn:                                   21
% 2.98/0.99  ground:                                 2
% 2.98/0.99  unary:                                  3
% 2.98/0.99  binary:                                 5
% 2.98/0.99  lits:                                   90
% 2.98/0.99  lits_eq:                                3
% 2.98/0.99  fd_pure:                                0
% 2.98/0.99  fd_pseudo:                              0
% 2.98/0.99  fd_cond:                                0
% 2.98/0.99  fd_pseudo_cond:                         1
% 2.98/0.99  ac_symbols:                             0
% 2.98/0.99  
% 2.98/0.99  ------ Propositional Solver
% 2.98/0.99  
% 2.98/0.99  prop_solver_calls:                      30
% 2.98/0.99  prop_fast_solver_calls:                 1389
% 2.98/0.99  smt_solver_calls:                       0
% 2.98/0.99  smt_fast_solver_calls:                  0
% 2.98/0.99  prop_num_of_clauses:                    3314
% 2.98/0.99  prop_preprocess_simplified:             7486
% 2.98/0.99  prop_fo_subsumed:                       61
% 2.98/0.99  prop_solver_time:                       0.
% 2.98/0.99  smt_solver_time:                        0.
% 2.98/0.99  smt_fast_solver_time:                   0.
% 2.98/0.99  prop_fast_solver_time:                  0.
% 2.98/0.99  prop_unsat_core_time:                   0.
% 2.98/0.99  
% 2.98/0.99  ------ QBF
% 2.98/0.99  
% 2.98/0.99  qbf_q_res:                              0
% 2.98/0.99  qbf_num_tautologies:                    0
% 2.98/0.99  qbf_prep_cycles:                        0
% 2.98/0.99  
% 2.98/0.99  ------ BMC1
% 2.98/0.99  
% 2.98/0.99  bmc1_current_bound:                     -1
% 2.98/0.99  bmc1_last_solved_bound:                 -1
% 2.98/0.99  bmc1_unsat_core_size:                   -1
% 2.98/0.99  bmc1_unsat_core_parents_size:           -1
% 2.98/0.99  bmc1_merge_next_fun:                    0
% 2.98/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.98/0.99  
% 2.98/0.99  ------ Instantiation
% 2.98/0.99  
% 2.98/0.99  inst_num_of_clauses:                    739
% 2.98/0.99  inst_num_in_passive:                    344
% 2.98/0.99  inst_num_in_active:                     345
% 2.98/0.99  inst_num_in_unprocessed:                50
% 2.98/0.99  inst_num_of_loops:                      520
% 2.98/0.99  inst_num_of_learning_restarts:          0
% 2.98/0.99  inst_num_moves_active_passive:          171
% 2.98/0.99  inst_lit_activity:                      0
% 2.98/0.99  inst_lit_activity_moves:                0
% 2.98/0.99  inst_num_tautologies:                   0
% 2.98/0.99  inst_num_prop_implied:                  0
% 2.98/0.99  inst_num_existing_simplified:           0
% 2.98/0.99  inst_num_eq_res_simplified:             0
% 2.98/0.99  inst_num_child_elim:                    0
% 2.98/0.99  inst_num_of_dismatching_blockings:      228
% 2.98/0.99  inst_num_of_non_proper_insts:           659
% 2.98/0.99  inst_num_of_duplicates:                 0
% 2.98/0.99  inst_inst_num_from_inst_to_res:         0
% 2.98/0.99  inst_dismatching_checking_time:         0.
% 2.98/0.99  
% 2.98/0.99  ------ Resolution
% 2.98/0.99  
% 2.98/0.99  res_num_of_clauses:                     0
% 2.98/0.99  res_num_in_passive:                     0
% 2.98/0.99  res_num_in_active:                      0
% 2.98/0.99  res_num_of_loops:                       136
% 2.98/0.99  res_forward_subset_subsumed:            19
% 2.98/0.99  res_backward_subset_subsumed:           0
% 2.98/0.99  res_forward_subsumed:                   0
% 2.98/0.99  res_backward_subsumed:                  0
% 2.98/0.99  res_forward_subsumption_resolution:     0
% 2.98/0.99  res_backward_subsumption_resolution:    0
% 2.98/0.99  res_clause_to_clause_subsumption:       1082
% 2.98/0.99  res_orphan_elimination:                 0
% 2.98/0.99  res_tautology_del:                      9
% 2.98/0.99  res_num_eq_res_simplified:              0
% 2.98/0.99  res_num_sel_changes:                    0
% 2.98/0.99  res_moves_from_active_to_pass:          0
% 2.98/0.99  
% 2.98/0.99  ------ Superposition
% 2.98/0.99  
% 2.98/0.99  sup_time_total:                         0.
% 2.98/0.99  sup_time_generating:                    0.
% 2.98/0.99  sup_time_sim_full:                      0.
% 2.98/0.99  sup_time_sim_immed:                     0.
% 2.98/0.99  
% 2.98/0.99  sup_num_of_clauses:                     223
% 2.98/0.99  sup_num_in_active:                      96
% 2.98/0.99  sup_num_in_passive:                     127
% 2.98/0.99  sup_num_of_loops:                       102
% 2.98/0.99  sup_fw_superposition:                   112
% 2.98/0.99  sup_bw_superposition:                   159
% 2.98/0.99  sup_immediate_simplified:               36
% 2.98/0.99  sup_given_eliminated:                   0
% 2.98/0.99  comparisons_done:                       0
% 2.98/0.99  comparisons_avoided:                    0
% 2.98/0.99  
% 2.98/0.99  ------ Simplifications
% 2.98/0.99  
% 2.98/0.99  
% 2.98/0.99  sim_fw_subset_subsumed:                 18
% 2.98/0.99  sim_bw_subset_subsumed:                 9
% 2.98/0.99  sim_fw_subsumed:                        9
% 2.98/0.99  sim_bw_subsumed:                        2
% 2.98/0.99  sim_fw_subsumption_res:                 4
% 2.98/0.99  sim_bw_subsumption_res:                 0
% 2.98/0.99  sim_tautology_del:                      20
% 2.98/0.99  sim_eq_tautology_del:                   1
% 2.98/0.99  sim_eq_res_simp:                        0
% 2.98/0.99  sim_fw_demodulated:                     0
% 2.98/0.99  sim_bw_demodulated:                     3
% 2.98/0.99  sim_light_normalised:                   6
% 2.98/0.99  sim_joinable_taut:                      0
% 2.98/0.99  sim_joinable_simp:                      0
% 2.98/0.99  sim_ac_normalised:                      0
% 2.98/0.99  sim_smt_subsumption:                    0
% 2.98/0.99  
%------------------------------------------------------------------------------
