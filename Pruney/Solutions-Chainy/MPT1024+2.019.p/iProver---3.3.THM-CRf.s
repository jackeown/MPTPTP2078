%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:51 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :  157 (1042 expanded)
%              Number of clauses        :   92 ( 324 expanded)
%              Number of leaves         :   18 ( 235 expanded)
%              Depth                    :   21
%              Number of atoms          :  576 (4693 expanded)
%              Number of equality atoms :  189 ( 879 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    6 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f48,plain,(
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

fof(f47,plain,
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

fof(f49,plain,
    ( ! [X5] :
        ( k1_funct_1(sK6,X5) != sK7
        | ~ r2_hidden(X5,sK5)
        | ~ r2_hidden(X5,sK3) )
    & r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f32,f48,f47])).

fof(f73,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f49])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

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
    inference(nnf_transformation,[],[f30])).

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

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK2(X1,X2,X3,X4),X1)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f74,plain,(
    r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
    inference(cnf_transformation,[],[f49])).

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

fof(f50,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f36])).

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

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK2(X1,X2,X3,X4),X4),X3)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f72,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f75,plain,(
    ! [X5] :
      ( k1_funct_1(sK6,X5) != sK7
      | ~ r2_hidden(X5,sK5)
      | ~ r2_hidden(X5,sK3) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK2(X1,X2,X3,X4),X2)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1216,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1223,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2647,plain,
    ( k7_relset_1(sK3,sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_1216,c_1223])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | r2_hidden(sK2(X4,X3,X2,X0),X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1221,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | r2_hidden(sK2(X4,X3,X2,X0),X4) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3836,plain,
    ( m1_subset_1(X0,sK4) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(X1,sK3,sK6,X0),X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2647,c_1221])).

cnf(c_27,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_28,plain,
    ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1463,plain,
    ( ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
    | ~ v1_xboole_0(k7_relset_1(sK3,sK4,sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1464,plain,
    ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) != iProver_top
    | v1_xboole_0(k7_relset_1(sK3,sK4,sK6,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1463])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1473,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1474,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1473])).

cnf(c_777,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1587,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k7_relset_1(sK3,sK4,sK6,sK5))
    | k7_relset_1(sK3,sK4,sK6,sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_777])).

cnf(c_1776,plain,
    ( v1_xboole_0(k7_relset_1(sK3,sK4,sK6,sK5))
    | ~ v1_xboole_0(k9_relat_1(sK6,sK5))
    | k7_relset_1(sK3,sK4,sK6,sK5) != k9_relat_1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_1587])).

cnf(c_1778,plain,
    ( k7_relset_1(sK3,sK4,sK6,sK5) != k9_relat_1(sK6,sK5)
    | v1_xboole_0(k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top
    | v1_xboole_0(k9_relat_1(sK6,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1776])).

cnf(c_1517,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k7_relset_1(sK3,sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1777,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k7_relset_1(sK3,sK4,sK6,sK5) = k9_relat_1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_1517])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2121,plain,
    ( r2_hidden(sK0(k9_relat_1(sK6,sK5)),k9_relat_1(sK6,sK5))
    | v1_xboole_0(k9_relat_1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2122,plain,
    ( r2_hidden(sK0(k9_relat_1(sK6,sK5)),k9_relat_1(sK6,sK5)) = iProver_top
    | v1_xboole_0(k9_relat_1(sK6,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2121])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2635,plain,
    ( r2_hidden(k4_tarski(sK1(sK0(k9_relat_1(sK6,sK5)),sK5,sK6),sK0(k9_relat_1(sK6,sK5))),sK6)
    | ~ r2_hidden(sK0(k9_relat_1(sK6,sK5)),k9_relat_1(sK6,sK5))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2642,plain,
    ( r2_hidden(k4_tarski(sK1(sK0(k9_relat_1(sK6,sK5)),sK5,sK6),sK0(k9_relat_1(sK6,sK5))),sK6) = iProver_top
    | r2_hidden(sK0(k9_relat_1(sK6,sK5)),k9_relat_1(sK6,sK5)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2635])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1225,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2840,plain,
    ( v1_xboole_0(sK4) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1216,c_1225])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1226,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2860,plain,
    ( v1_xboole_0(sK3) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1216,c_1226])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1224,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2990,plain,
    ( m1_subset_1(k9_relat_1(sK6,X0),k1_zfmisc_1(sK4)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2647,c_1224])).

cnf(c_3638,plain,
    ( m1_subset_1(k9_relat_1(sK6,X0),k1_zfmisc_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2990,c_27])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1232,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3877,plain,
    ( m1_subset_1(X0,sK4) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3638,c_1232])).

cnf(c_5520,plain,
    ( ~ r2_hidden(k4_tarski(sK1(sK0(k9_relat_1(sK6,sK5)),sK5,sK6),sK0(k9_relat_1(sK6,sK5))),sK6)
    | ~ v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5521,plain,
    ( r2_hidden(k4_tarski(sK1(sK0(k9_relat_1(sK6,sK5)),sK5,sK6),sK0(k9_relat_1(sK6,sK5))),sK6) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5520])).

cnf(c_5709,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(X1,sK3,sK6,X0),X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3836,c_24,c_27,c_28,c_1464,c_1474,c_1778,c_1777,c_2122,c_2642,c_2840,c_2860,c_3877,c_5521])).

cnf(c_1217,plain,
    ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2980,plain,
    ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2647,c_1217])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | r2_hidden(k4_tarski(sK2(X4,X3,X2,X0),X0),X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1220,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X4,X3,X2,X0),X0),X2) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2991,plain,
    ( m1_subset_1(X0,sK4) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X1,sK3,sK6,X0),X0),sK6) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2647,c_1220])).

cnf(c_6161,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X1,sK3,sK6,X0),X0),sK6) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2991,c_24,c_27,c_28,c_1464,c_1474,c_1778,c_1777,c_2122,c_2642,c_2840,c_2860,c_3877,c_5521])).

cnf(c_11,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_324,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_25])).

cnf(c_325,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK6)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_1213,plain,
    ( k1_funct_1(sK6,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_325])).

cnf(c_326,plain,
    ( k1_funct_1(sK6,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_325])).

cnf(c_1504,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | k1_funct_1(sK6,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1213,c_27,c_326,c_1474])).

cnf(c_1505,plain,
    ( k1_funct_1(sK6,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_1504])).

cnf(c_6175,plain,
    ( k1_funct_1(sK6,sK2(X0,sK3,sK6,X1)) = X1
    | r2_hidden(X1,k9_relat_1(sK6,X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6161,c_1505])).

cnf(c_6264,plain,
    ( k1_funct_1(sK6,sK2(sK5,sK3,sK6,sK7)) = sK7
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2980,c_6175])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2637,plain,
    ( r2_hidden(sK1(sK0(k9_relat_1(sK6,sK5)),sK5,sK6),sK5)
    | ~ r2_hidden(sK0(k9_relat_1(sK6,sK5)),k9_relat_1(sK6,sK5))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2443,plain,
    ( m1_subset_1(sK7,sK4) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | r2_hidden(k4_tarski(sK2(sK5,sK3,sK6,sK7),sK7),sK6) = iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1217,c_1220])).

cnf(c_1494,plain,
    ( ~ m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(X0))
    | m1_subset_1(sK7,X0)
    | ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1640,plain,
    ( ~ m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(sK4))
    | m1_subset_1(sK7,sK4)
    | ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_1494])).

cnf(c_1642,plain,
    ( m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(sK4)) != iProver_top
    | m1_subset_1(sK7,sK4) = iProver_top
    | r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1640])).

cnf(c_1512,plain,
    ( m1_subset_1(k7_relset_1(sK3,sK4,sK6,X0),k1_zfmisc_1(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1641,plain,
    ( m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_1512])).

cnf(c_1644,plain,
    ( m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(sK4)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1641])).

cnf(c_3498,plain,
    ( r2_hidden(k4_tarski(sK2(sK5,sK3,sK6,sK7),sK7),sK6) = iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2443,c_27,c_28,c_1642,c_1644])).

cnf(c_3509,plain,
    ( k1_funct_1(sK6,sK2(sK5,sK3,sK6,sK7)) = sK7
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3498,c_1505])).

cnf(c_4654,plain,
    ( k1_funct_1(sK6,sK2(sK5,sK3,sK6,sK7)) = sK7
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3509,c_2840])).

cnf(c_5365,plain,
    ( k1_funct_1(sK6,sK2(sK5,sK3,sK6,sK7)) = sK7
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4654,c_2860])).

cnf(c_5367,plain,
    ( v1_xboole_0(sK5)
    | v1_xboole_0(sK6)
    | k1_funct_1(sK6,sK2(sK5,sK3,sK6,sK7)) = sK7 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5365])).

cnf(c_5574,plain,
    ( ~ r2_hidden(sK1(sK0(k9_relat_1(sK6,sK5)),sK5,sK6),sK5)
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_6326,plain,
    ( k1_funct_1(sK6,sK2(sK5,sK3,sK6,sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6264,c_24,c_23,c_1463,c_1473,c_1776,c_1777,c_2121,c_2637,c_2635,c_5367,c_5520,c_5574])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK5)
    | k1_funct_1(sK6,X0) != sK7 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1218,plain,
    ( k1_funct_1(sK6,X0) != sK7
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6332,plain,
    ( r2_hidden(sK2(sK5,sK3,sK6,sK7),sK3) != iProver_top
    | r2_hidden(sK2(sK5,sK3,sK6,sK7),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6326,c_1218])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | m1_subset_1(sK2(X4,X3,X2,X0),X3)
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1219,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(sK2(X4,X3,X2,X0),X3) = iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1691,plain,
    ( m1_subset_1(sK2(sK5,sK3,sK6,sK7),sK3) = iProver_top
    | m1_subset_1(sK7,sK4) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1217,c_1219])).

cnf(c_2109,plain,
    ( m1_subset_1(sK2(sK5,sK3,sK6,sK7),sK3) = iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1691,c_27,c_28,c_1642,c_1644])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1233,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2117,plain,
    ( r2_hidden(sK2(sK5,sK3,sK6,sK7),sK3) = iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2109,c_1233])).

cnf(c_2638,plain,
    ( r2_hidden(sK1(sK0(k9_relat_1(sK6,sK5)),sK5,sK6),sK5) = iProver_top
    | r2_hidden(sK0(k9_relat_1(sK6,sK5)),k9_relat_1(sK6,sK5)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2637])).

cnf(c_5575,plain,
    ( r2_hidden(sK1(sK0(k9_relat_1(sK6,sK5)),sK5,sK6),sK5) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5574])).

cnf(c_6385,plain,
    ( r2_hidden(sK2(sK5,sK3,sK6,sK7),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6332,c_24,c_27,c_28,c_1464,c_1474,c_1778,c_1777,c_2117,c_2122,c_2638,c_2642,c_2840,c_2860,c_5521,c_5575])).

cnf(c_6390,plain,
    ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_5709,c_6385])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6390,c_5575,c_2980,c_2638,c_2122,c_1777,c_1778,c_1474,c_1464,c_28,c_27,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:28:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.39/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.00  
% 2.39/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.39/1.00  
% 2.39/1.00  ------  iProver source info
% 2.39/1.00  
% 2.39/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.39/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.39/1.00  git: non_committed_changes: false
% 2.39/1.00  git: last_make_outside_of_git: false
% 2.39/1.00  
% 2.39/1.00  ------ 
% 2.39/1.00  
% 2.39/1.00  ------ Input Options
% 2.39/1.00  
% 2.39/1.00  --out_options                           all
% 2.39/1.00  --tptp_safe_out                         true
% 2.39/1.00  --problem_path                          ""
% 2.39/1.00  --include_path                          ""
% 2.39/1.00  --clausifier                            res/vclausify_rel
% 2.39/1.00  --clausifier_options                    --mode clausify
% 2.39/1.00  --stdin                                 false
% 2.39/1.00  --stats_out                             all
% 2.39/1.00  
% 2.39/1.00  ------ General Options
% 2.39/1.00  
% 2.39/1.00  --fof                                   false
% 2.39/1.00  --time_out_real                         305.
% 2.39/1.00  --time_out_virtual                      -1.
% 2.39/1.00  --symbol_type_check                     false
% 2.39/1.00  --clausify_out                          false
% 2.39/1.00  --sig_cnt_out                           false
% 2.39/1.00  --trig_cnt_out                          false
% 2.39/1.00  --trig_cnt_out_tolerance                1.
% 2.39/1.00  --trig_cnt_out_sk_spl                   false
% 2.39/1.00  --abstr_cl_out                          false
% 2.39/1.00  
% 2.39/1.00  ------ Global Options
% 2.39/1.00  
% 2.39/1.00  --schedule                              default
% 2.39/1.00  --add_important_lit                     false
% 2.39/1.00  --prop_solver_per_cl                    1000
% 2.39/1.00  --min_unsat_core                        false
% 2.39/1.00  --soft_assumptions                      false
% 2.39/1.00  --soft_lemma_size                       3
% 2.39/1.00  --prop_impl_unit_size                   0
% 2.39/1.00  --prop_impl_unit                        []
% 2.39/1.00  --share_sel_clauses                     true
% 2.39/1.00  --reset_solvers                         false
% 2.39/1.00  --bc_imp_inh                            [conj_cone]
% 2.39/1.00  --conj_cone_tolerance                   3.
% 2.39/1.00  --extra_neg_conj                        none
% 2.39/1.00  --large_theory_mode                     true
% 2.39/1.00  --prolific_symb_bound                   200
% 2.39/1.00  --lt_threshold                          2000
% 2.39/1.00  --clause_weak_htbl                      true
% 2.39/1.00  --gc_record_bc_elim                     false
% 2.39/1.00  
% 2.39/1.00  ------ Preprocessing Options
% 2.39/1.00  
% 2.39/1.00  --preprocessing_flag                    true
% 2.39/1.00  --time_out_prep_mult                    0.1
% 2.39/1.00  --splitting_mode                        input
% 2.39/1.00  --splitting_grd                         true
% 2.39/1.00  --splitting_cvd                         false
% 2.39/1.00  --splitting_cvd_svl                     false
% 2.39/1.00  --splitting_nvd                         32
% 2.39/1.00  --sub_typing                            true
% 2.39/1.00  --prep_gs_sim                           true
% 2.39/1.00  --prep_unflatten                        true
% 2.39/1.00  --prep_res_sim                          true
% 2.39/1.00  --prep_upred                            true
% 2.39/1.00  --prep_sem_filter                       exhaustive
% 2.39/1.00  --prep_sem_filter_out                   false
% 2.39/1.00  --pred_elim                             true
% 2.39/1.00  --res_sim_input                         true
% 2.39/1.00  --eq_ax_congr_red                       true
% 2.39/1.00  --pure_diseq_elim                       true
% 2.39/1.00  --brand_transform                       false
% 2.39/1.00  --non_eq_to_eq                          false
% 2.39/1.00  --prep_def_merge                        true
% 2.39/1.00  --prep_def_merge_prop_impl              false
% 2.39/1.00  --prep_def_merge_mbd                    true
% 2.39/1.00  --prep_def_merge_tr_red                 false
% 2.39/1.00  --prep_def_merge_tr_cl                  false
% 2.39/1.00  --smt_preprocessing                     true
% 2.39/1.00  --smt_ac_axioms                         fast
% 2.39/1.00  --preprocessed_out                      false
% 2.39/1.00  --preprocessed_stats                    false
% 2.39/1.00  
% 2.39/1.00  ------ Abstraction refinement Options
% 2.39/1.00  
% 2.39/1.00  --abstr_ref                             []
% 2.39/1.00  --abstr_ref_prep                        false
% 2.39/1.00  --abstr_ref_until_sat                   false
% 2.39/1.00  --abstr_ref_sig_restrict                funpre
% 2.39/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.39/1.00  --abstr_ref_under                       []
% 2.39/1.00  
% 2.39/1.00  ------ SAT Options
% 2.39/1.00  
% 2.39/1.00  --sat_mode                              false
% 2.39/1.00  --sat_fm_restart_options                ""
% 2.39/1.00  --sat_gr_def                            false
% 2.39/1.00  --sat_epr_types                         true
% 2.39/1.00  --sat_non_cyclic_types                  false
% 2.39/1.00  --sat_finite_models                     false
% 2.39/1.00  --sat_fm_lemmas                         false
% 2.39/1.00  --sat_fm_prep                           false
% 2.39/1.00  --sat_fm_uc_incr                        true
% 2.39/1.00  --sat_out_model                         small
% 2.39/1.00  --sat_out_clauses                       false
% 2.39/1.00  
% 2.39/1.00  ------ QBF Options
% 2.39/1.00  
% 2.39/1.00  --qbf_mode                              false
% 2.39/1.00  --qbf_elim_univ                         false
% 2.39/1.00  --qbf_dom_inst                          none
% 2.39/1.00  --qbf_dom_pre_inst                      false
% 2.39/1.00  --qbf_sk_in                             false
% 2.39/1.00  --qbf_pred_elim                         true
% 2.39/1.00  --qbf_split                             512
% 2.39/1.00  
% 2.39/1.00  ------ BMC1 Options
% 2.39/1.00  
% 2.39/1.00  --bmc1_incremental                      false
% 2.39/1.00  --bmc1_axioms                           reachable_all
% 2.39/1.00  --bmc1_min_bound                        0
% 2.39/1.00  --bmc1_max_bound                        -1
% 2.39/1.00  --bmc1_max_bound_default                -1
% 2.39/1.00  --bmc1_symbol_reachability              true
% 2.39/1.00  --bmc1_property_lemmas                  false
% 2.39/1.00  --bmc1_k_induction                      false
% 2.39/1.00  --bmc1_non_equiv_states                 false
% 2.39/1.00  --bmc1_deadlock                         false
% 2.39/1.00  --bmc1_ucm                              false
% 2.39/1.00  --bmc1_add_unsat_core                   none
% 2.39/1.00  --bmc1_unsat_core_children              false
% 2.39/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.39/1.00  --bmc1_out_stat                         full
% 2.39/1.00  --bmc1_ground_init                      false
% 2.39/1.00  --bmc1_pre_inst_next_state              false
% 2.39/1.00  --bmc1_pre_inst_state                   false
% 2.39/1.00  --bmc1_pre_inst_reach_state             false
% 2.39/1.00  --bmc1_out_unsat_core                   false
% 2.39/1.00  --bmc1_aig_witness_out                  false
% 2.39/1.00  --bmc1_verbose                          false
% 2.39/1.00  --bmc1_dump_clauses_tptp                false
% 2.39/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.39/1.00  --bmc1_dump_file                        -
% 2.39/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.39/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.39/1.00  --bmc1_ucm_extend_mode                  1
% 2.39/1.00  --bmc1_ucm_init_mode                    2
% 2.39/1.00  --bmc1_ucm_cone_mode                    none
% 2.39/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.39/1.00  --bmc1_ucm_relax_model                  4
% 2.39/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.39/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.39/1.00  --bmc1_ucm_layered_model                none
% 2.39/1.00  --bmc1_ucm_max_lemma_size               10
% 2.39/1.00  
% 2.39/1.00  ------ AIG Options
% 2.39/1.00  
% 2.39/1.00  --aig_mode                              false
% 2.39/1.00  
% 2.39/1.00  ------ Instantiation Options
% 2.39/1.00  
% 2.39/1.00  --instantiation_flag                    true
% 2.39/1.00  --inst_sos_flag                         false
% 2.39/1.00  --inst_sos_phase                        true
% 2.39/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.39/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.39/1.00  --inst_lit_sel_side                     num_symb
% 2.39/1.00  --inst_solver_per_active                1400
% 2.39/1.00  --inst_solver_calls_frac                1.
% 2.39/1.00  --inst_passive_queue_type               priority_queues
% 2.39/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.39/1.00  --inst_passive_queues_freq              [25;2]
% 2.39/1.00  --inst_dismatching                      true
% 2.39/1.00  --inst_eager_unprocessed_to_passive     true
% 2.39/1.00  --inst_prop_sim_given                   true
% 2.39/1.00  --inst_prop_sim_new                     false
% 2.39/1.00  --inst_subs_new                         false
% 2.39/1.00  --inst_eq_res_simp                      false
% 2.39/1.00  --inst_subs_given                       false
% 2.39/1.00  --inst_orphan_elimination               true
% 2.39/1.00  --inst_learning_loop_flag               true
% 2.39/1.00  --inst_learning_start                   3000
% 2.39/1.00  --inst_learning_factor                  2
% 2.39/1.00  --inst_start_prop_sim_after_learn       3
% 2.39/1.00  --inst_sel_renew                        solver
% 2.39/1.00  --inst_lit_activity_flag                true
% 2.39/1.00  --inst_restr_to_given                   false
% 2.39/1.00  --inst_activity_threshold               500
% 2.39/1.00  --inst_out_proof                        true
% 2.39/1.00  
% 2.39/1.00  ------ Resolution Options
% 2.39/1.00  
% 2.39/1.00  --resolution_flag                       true
% 2.39/1.00  --res_lit_sel                           adaptive
% 2.39/1.00  --res_lit_sel_side                      none
% 2.39/1.00  --res_ordering                          kbo
% 2.39/1.00  --res_to_prop_solver                    active
% 2.39/1.00  --res_prop_simpl_new                    false
% 2.39/1.00  --res_prop_simpl_given                  true
% 2.39/1.00  --res_passive_queue_type                priority_queues
% 2.39/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.39/1.00  --res_passive_queues_freq               [15;5]
% 2.39/1.00  --res_forward_subs                      full
% 2.39/1.00  --res_backward_subs                     full
% 2.39/1.00  --res_forward_subs_resolution           true
% 2.39/1.00  --res_backward_subs_resolution          true
% 2.39/1.00  --res_orphan_elimination                true
% 2.39/1.00  --res_time_limit                        2.
% 2.39/1.00  --res_out_proof                         true
% 2.39/1.00  
% 2.39/1.00  ------ Superposition Options
% 2.39/1.00  
% 2.39/1.00  --superposition_flag                    true
% 2.39/1.00  --sup_passive_queue_type                priority_queues
% 2.39/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.39/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.39/1.00  --demod_completeness_check              fast
% 2.39/1.00  --demod_use_ground                      true
% 2.39/1.00  --sup_to_prop_solver                    passive
% 2.39/1.00  --sup_prop_simpl_new                    true
% 2.39/1.00  --sup_prop_simpl_given                  true
% 2.39/1.00  --sup_fun_splitting                     false
% 2.39/1.00  --sup_smt_interval                      50000
% 2.39/1.00  
% 2.39/1.00  ------ Superposition Simplification Setup
% 2.39/1.00  
% 2.39/1.00  --sup_indices_passive                   []
% 2.39/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.39/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/1.00  --sup_full_bw                           [BwDemod]
% 2.39/1.00  --sup_immed_triv                        [TrivRules]
% 2.39/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.39/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/1.00  --sup_immed_bw_main                     []
% 2.39/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.39/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.39/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.39/1.00  
% 2.39/1.00  ------ Combination Options
% 2.39/1.00  
% 2.39/1.00  --comb_res_mult                         3
% 2.39/1.00  --comb_sup_mult                         2
% 2.39/1.00  --comb_inst_mult                        10
% 2.39/1.00  
% 2.39/1.00  ------ Debug Options
% 2.39/1.00  
% 2.39/1.00  --dbg_backtrace                         false
% 2.39/1.00  --dbg_dump_prop_clauses                 false
% 2.39/1.00  --dbg_dump_prop_clauses_file            -
% 2.39/1.00  --dbg_out_stat                          false
% 2.39/1.00  ------ Parsing...
% 2.39/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.39/1.00  
% 2.39/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.39/1.00  
% 2.39/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.39/1.00  
% 2.39/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.39/1.00  ------ Proving...
% 2.39/1.00  ------ Problem Properties 
% 2.39/1.00  
% 2.39/1.00  
% 2.39/1.00  clauses                                 25
% 2.39/1.00  conjectures                             3
% 2.39/1.00  EPR                                     3
% 2.39/1.00  Horn                                    19
% 2.39/1.00  unary                                   3
% 2.39/1.00  binary                                  6
% 2.39/1.00  lits                                    83
% 2.39/1.00  lits eq                                 3
% 2.39/1.00  fd_pure                                 0
% 2.39/1.00  fd_pseudo                               0
% 2.39/1.00  fd_cond                                 0
% 2.39/1.00  fd_pseudo_cond                          1
% 2.39/1.00  AC symbols                              0
% 2.39/1.00  
% 2.39/1.00  ------ Schedule dynamic 5 is on 
% 2.39/1.00  
% 2.39/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.39/1.00  
% 2.39/1.00  
% 2.39/1.00  ------ 
% 2.39/1.00  Current options:
% 2.39/1.00  ------ 
% 2.39/1.00  
% 2.39/1.00  ------ Input Options
% 2.39/1.00  
% 2.39/1.00  --out_options                           all
% 2.39/1.00  --tptp_safe_out                         true
% 2.39/1.00  --problem_path                          ""
% 2.39/1.00  --include_path                          ""
% 2.39/1.00  --clausifier                            res/vclausify_rel
% 2.39/1.00  --clausifier_options                    --mode clausify
% 2.39/1.00  --stdin                                 false
% 2.39/1.00  --stats_out                             all
% 2.39/1.00  
% 2.39/1.00  ------ General Options
% 2.39/1.00  
% 2.39/1.00  --fof                                   false
% 2.39/1.00  --time_out_real                         305.
% 2.39/1.00  --time_out_virtual                      -1.
% 2.39/1.00  --symbol_type_check                     false
% 2.39/1.00  --clausify_out                          false
% 2.39/1.00  --sig_cnt_out                           false
% 2.39/1.00  --trig_cnt_out                          false
% 2.39/1.00  --trig_cnt_out_tolerance                1.
% 2.39/1.00  --trig_cnt_out_sk_spl                   false
% 2.39/1.00  --abstr_cl_out                          false
% 2.39/1.00  
% 2.39/1.00  ------ Global Options
% 2.39/1.00  
% 2.39/1.00  --schedule                              default
% 2.39/1.00  --add_important_lit                     false
% 2.39/1.00  --prop_solver_per_cl                    1000
% 2.39/1.00  --min_unsat_core                        false
% 2.39/1.00  --soft_assumptions                      false
% 2.39/1.00  --soft_lemma_size                       3
% 2.39/1.00  --prop_impl_unit_size                   0
% 2.39/1.00  --prop_impl_unit                        []
% 2.39/1.00  --share_sel_clauses                     true
% 2.39/1.00  --reset_solvers                         false
% 2.39/1.00  --bc_imp_inh                            [conj_cone]
% 2.39/1.00  --conj_cone_tolerance                   3.
% 2.39/1.00  --extra_neg_conj                        none
% 2.39/1.00  --large_theory_mode                     true
% 2.39/1.00  --prolific_symb_bound                   200
% 2.39/1.00  --lt_threshold                          2000
% 2.39/1.00  --clause_weak_htbl                      true
% 2.39/1.00  --gc_record_bc_elim                     false
% 2.39/1.00  
% 2.39/1.00  ------ Preprocessing Options
% 2.39/1.00  
% 2.39/1.00  --preprocessing_flag                    true
% 2.39/1.00  --time_out_prep_mult                    0.1
% 2.39/1.00  --splitting_mode                        input
% 2.39/1.00  --splitting_grd                         true
% 2.39/1.00  --splitting_cvd                         false
% 2.39/1.00  --splitting_cvd_svl                     false
% 2.39/1.00  --splitting_nvd                         32
% 2.39/1.00  --sub_typing                            true
% 2.39/1.00  --prep_gs_sim                           true
% 2.39/1.00  --prep_unflatten                        true
% 2.39/1.00  --prep_res_sim                          true
% 2.39/1.00  --prep_upred                            true
% 2.39/1.00  --prep_sem_filter                       exhaustive
% 2.39/1.00  --prep_sem_filter_out                   false
% 2.39/1.00  --pred_elim                             true
% 2.39/1.00  --res_sim_input                         true
% 2.39/1.00  --eq_ax_congr_red                       true
% 2.39/1.00  --pure_diseq_elim                       true
% 2.39/1.00  --brand_transform                       false
% 2.39/1.00  --non_eq_to_eq                          false
% 2.39/1.00  --prep_def_merge                        true
% 2.39/1.00  --prep_def_merge_prop_impl              false
% 2.39/1.00  --prep_def_merge_mbd                    true
% 2.39/1.00  --prep_def_merge_tr_red                 false
% 2.39/1.00  --prep_def_merge_tr_cl                  false
% 2.39/1.00  --smt_preprocessing                     true
% 2.39/1.00  --smt_ac_axioms                         fast
% 2.39/1.00  --preprocessed_out                      false
% 2.39/1.00  --preprocessed_stats                    false
% 2.39/1.00  
% 2.39/1.00  ------ Abstraction refinement Options
% 2.39/1.00  
% 2.39/1.00  --abstr_ref                             []
% 2.39/1.00  --abstr_ref_prep                        false
% 2.39/1.00  --abstr_ref_until_sat                   false
% 2.39/1.00  --abstr_ref_sig_restrict                funpre
% 2.39/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.39/1.00  --abstr_ref_under                       []
% 2.39/1.00  
% 2.39/1.00  ------ SAT Options
% 2.39/1.00  
% 2.39/1.00  --sat_mode                              false
% 2.39/1.00  --sat_fm_restart_options                ""
% 2.39/1.00  --sat_gr_def                            false
% 2.39/1.00  --sat_epr_types                         true
% 2.39/1.00  --sat_non_cyclic_types                  false
% 2.39/1.00  --sat_finite_models                     false
% 2.39/1.00  --sat_fm_lemmas                         false
% 2.39/1.00  --sat_fm_prep                           false
% 2.39/1.00  --sat_fm_uc_incr                        true
% 2.39/1.00  --sat_out_model                         small
% 2.39/1.00  --sat_out_clauses                       false
% 2.39/1.00  
% 2.39/1.00  ------ QBF Options
% 2.39/1.00  
% 2.39/1.00  --qbf_mode                              false
% 2.39/1.00  --qbf_elim_univ                         false
% 2.39/1.00  --qbf_dom_inst                          none
% 2.39/1.00  --qbf_dom_pre_inst                      false
% 2.39/1.00  --qbf_sk_in                             false
% 2.39/1.00  --qbf_pred_elim                         true
% 2.39/1.00  --qbf_split                             512
% 2.39/1.00  
% 2.39/1.00  ------ BMC1 Options
% 2.39/1.00  
% 2.39/1.00  --bmc1_incremental                      false
% 2.39/1.00  --bmc1_axioms                           reachable_all
% 2.39/1.00  --bmc1_min_bound                        0
% 2.39/1.00  --bmc1_max_bound                        -1
% 2.39/1.00  --bmc1_max_bound_default                -1
% 2.39/1.00  --bmc1_symbol_reachability              true
% 2.39/1.00  --bmc1_property_lemmas                  false
% 2.39/1.00  --bmc1_k_induction                      false
% 2.39/1.00  --bmc1_non_equiv_states                 false
% 2.39/1.00  --bmc1_deadlock                         false
% 2.39/1.00  --bmc1_ucm                              false
% 2.39/1.00  --bmc1_add_unsat_core                   none
% 2.39/1.00  --bmc1_unsat_core_children              false
% 2.39/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.39/1.00  --bmc1_out_stat                         full
% 2.39/1.00  --bmc1_ground_init                      false
% 2.39/1.00  --bmc1_pre_inst_next_state              false
% 2.39/1.00  --bmc1_pre_inst_state                   false
% 2.39/1.00  --bmc1_pre_inst_reach_state             false
% 2.39/1.00  --bmc1_out_unsat_core                   false
% 2.39/1.00  --bmc1_aig_witness_out                  false
% 2.39/1.00  --bmc1_verbose                          false
% 2.39/1.00  --bmc1_dump_clauses_tptp                false
% 2.39/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.39/1.00  --bmc1_dump_file                        -
% 2.39/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.39/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.39/1.00  --bmc1_ucm_extend_mode                  1
% 2.39/1.00  --bmc1_ucm_init_mode                    2
% 2.39/1.00  --bmc1_ucm_cone_mode                    none
% 2.39/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.39/1.00  --bmc1_ucm_relax_model                  4
% 2.39/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.39/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.39/1.00  --bmc1_ucm_layered_model                none
% 2.39/1.00  --bmc1_ucm_max_lemma_size               10
% 2.39/1.00  
% 2.39/1.00  ------ AIG Options
% 2.39/1.00  
% 2.39/1.00  --aig_mode                              false
% 2.39/1.00  
% 2.39/1.00  ------ Instantiation Options
% 2.39/1.00  
% 2.39/1.00  --instantiation_flag                    true
% 2.39/1.00  --inst_sos_flag                         false
% 2.39/1.00  --inst_sos_phase                        true
% 2.39/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.39/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.39/1.00  --inst_lit_sel_side                     none
% 2.39/1.00  --inst_solver_per_active                1400
% 2.39/1.00  --inst_solver_calls_frac                1.
% 2.39/1.00  --inst_passive_queue_type               priority_queues
% 2.39/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.39/1.00  --inst_passive_queues_freq              [25;2]
% 2.39/1.00  --inst_dismatching                      true
% 2.39/1.00  --inst_eager_unprocessed_to_passive     true
% 2.39/1.00  --inst_prop_sim_given                   true
% 2.39/1.00  --inst_prop_sim_new                     false
% 2.39/1.00  --inst_subs_new                         false
% 2.39/1.00  --inst_eq_res_simp                      false
% 2.39/1.00  --inst_subs_given                       false
% 2.39/1.00  --inst_orphan_elimination               true
% 2.39/1.00  --inst_learning_loop_flag               true
% 2.39/1.00  --inst_learning_start                   3000
% 2.39/1.00  --inst_learning_factor                  2
% 2.39/1.00  --inst_start_prop_sim_after_learn       3
% 2.39/1.00  --inst_sel_renew                        solver
% 2.39/1.00  --inst_lit_activity_flag                true
% 2.39/1.00  --inst_restr_to_given                   false
% 2.39/1.00  --inst_activity_threshold               500
% 2.39/1.00  --inst_out_proof                        true
% 2.39/1.00  
% 2.39/1.00  ------ Resolution Options
% 2.39/1.00  
% 2.39/1.00  --resolution_flag                       false
% 2.39/1.00  --res_lit_sel                           adaptive
% 2.39/1.00  --res_lit_sel_side                      none
% 2.39/1.00  --res_ordering                          kbo
% 2.39/1.00  --res_to_prop_solver                    active
% 2.39/1.00  --res_prop_simpl_new                    false
% 2.39/1.00  --res_prop_simpl_given                  true
% 2.39/1.00  --res_passive_queue_type                priority_queues
% 2.39/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.39/1.00  --res_passive_queues_freq               [15;5]
% 2.39/1.00  --res_forward_subs                      full
% 2.39/1.00  --res_backward_subs                     full
% 2.39/1.00  --res_forward_subs_resolution           true
% 2.39/1.00  --res_backward_subs_resolution          true
% 2.39/1.00  --res_orphan_elimination                true
% 2.39/1.00  --res_time_limit                        2.
% 2.39/1.00  --res_out_proof                         true
% 2.39/1.00  
% 2.39/1.00  ------ Superposition Options
% 2.39/1.00  
% 2.39/1.00  --superposition_flag                    true
% 2.39/1.00  --sup_passive_queue_type                priority_queues
% 2.39/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.39/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.39/1.00  --demod_completeness_check              fast
% 2.39/1.00  --demod_use_ground                      true
% 2.39/1.00  --sup_to_prop_solver                    passive
% 2.39/1.00  --sup_prop_simpl_new                    true
% 2.39/1.00  --sup_prop_simpl_given                  true
% 2.39/1.00  --sup_fun_splitting                     false
% 2.39/1.00  --sup_smt_interval                      50000
% 2.39/1.00  
% 2.39/1.00  ------ Superposition Simplification Setup
% 2.39/1.00  
% 2.39/1.00  --sup_indices_passive                   []
% 2.39/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.39/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/1.00  --sup_full_bw                           [BwDemod]
% 2.39/1.00  --sup_immed_triv                        [TrivRules]
% 2.39/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.39/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/1.00  --sup_immed_bw_main                     []
% 2.39/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.39/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.39/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.39/1.00  
% 2.39/1.00  ------ Combination Options
% 2.39/1.00  
% 2.39/1.00  --comb_res_mult                         3
% 2.39/1.00  --comb_sup_mult                         2
% 2.39/1.00  --comb_inst_mult                        10
% 2.39/1.00  
% 2.39/1.00  ------ Debug Options
% 2.39/1.00  
% 2.39/1.00  --dbg_backtrace                         false
% 2.39/1.00  --dbg_dump_prop_clauses                 false
% 2.39/1.00  --dbg_dump_prop_clauses_file            -
% 2.39/1.00  --dbg_out_stat                          false
% 2.39/1.00  
% 2.39/1.00  
% 2.39/1.00  
% 2.39/1.00  
% 2.39/1.00  ------ Proving...
% 2.39/1.00  
% 2.39/1.00  
% 2.39/1.00  % SZS status Theorem for theBenchmark.p
% 2.39/1.00  
% 2.39/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.39/1.00  
% 2.39/1.00  fof(f14,conjecture,(
% 2.39/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.00  
% 2.39/1.00  fof(f15,negated_conjecture,(
% 2.39/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.39/1.00    inference(negated_conjecture,[],[f14])).
% 2.39/1.00  
% 2.39/1.00  fof(f16,plain,(
% 2.39/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.39/1.00    inference(pure_predicate_removal,[],[f15])).
% 2.39/1.00  
% 2.39/1.00  fof(f31,plain,(
% 2.39/1.00    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 2.39/1.00    inference(ennf_transformation,[],[f16])).
% 2.39/1.00  
% 2.39/1.00  fof(f32,plain,(
% 2.39/1.00    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 2.39/1.00    inference(flattening,[],[f31])).
% 2.39/1.00  
% 2.39/1.00  fof(f48,plain,(
% 2.39/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK7 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(sK7,k7_relset_1(X0,X1,X3,X2)))) )),
% 2.39/1.00    introduced(choice_axiom,[])).
% 2.39/1.00  
% 2.39/1.00  fof(f47,plain,(
% 2.39/1.00    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK6,X5) != X4 | ~r2_hidden(X5,sK5) | ~r2_hidden(X5,sK3)) & r2_hidden(X4,k7_relset_1(sK3,sK4,sK6,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK6))),
% 2.39/1.00    introduced(choice_axiom,[])).
% 2.39/1.00  
% 2.39/1.00  fof(f49,plain,(
% 2.39/1.00    (! [X5] : (k1_funct_1(sK6,X5) != sK7 | ~r2_hidden(X5,sK5) | ~r2_hidden(X5,sK3)) & r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK6)),
% 2.39/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f32,f48,f47])).
% 2.39/1.00  
% 2.39/1.00  fof(f73,plain,(
% 2.39/1.00    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 2.39/1.00    inference(cnf_transformation,[],[f49])).
% 2.39/1.00  
% 2.39/1.00  fof(f12,axiom,(
% 2.39/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.00  
% 2.39/1.00  fof(f29,plain,(
% 2.39/1.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.39/1.00    inference(ennf_transformation,[],[f12])).
% 2.39/1.00  
% 2.39/1.00  fof(f67,plain,(
% 2.39/1.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.39/1.00    inference(cnf_transformation,[],[f29])).
% 2.39/1.00  
% 2.39/1.00  fof(f13,axiom,(
% 2.39/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 2.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.00  
% 2.39/1.00  fof(f30,plain,(
% 2.39/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.39/1.00    inference(ennf_transformation,[],[f13])).
% 2.39/1.00  
% 2.39/1.00  fof(f43,plain,(
% 2.39/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.39/1.00    inference(nnf_transformation,[],[f30])).
% 2.39/1.00  
% 2.39/1.00  fof(f44,plain,(
% 2.39/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.39/1.00    inference(rectify,[],[f43])).
% 2.39/1.00  
% 2.39/1.00  fof(f45,plain,(
% 2.39/1.00    ! [X4,X3,X2,X1] : (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) => (r2_hidden(sK2(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK2(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK2(X1,X2,X3,X4),X2)))),
% 2.39/1.00    introduced(choice_axiom,[])).
% 2.39/1.00  
% 2.39/1.00  fof(f46,plain,(
% 2.39/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & ((r2_hidden(sK2(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK2(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK2(X1,X2,X3,X4),X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.39/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f44,f45])).
% 2.39/1.00  
% 2.39/1.00  fof(f70,plain,(
% 2.39/1.00    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK2(X1,X2,X3,X4),X1) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.39/1.00    inference(cnf_transformation,[],[f46])).
% 2.39/1.00  
% 2.39/1.00  fof(f74,plain,(
% 2.39/1.00    r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))),
% 2.39/1.00    inference(cnf_transformation,[],[f49])).
% 2.39/1.00  
% 2.39/1.00  fof(f1,axiom,(
% 2.39/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.00  
% 2.39/1.00  fof(f33,plain,(
% 2.39/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.39/1.00    inference(nnf_transformation,[],[f1])).
% 2.39/1.00  
% 2.39/1.00  fof(f34,plain,(
% 2.39/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.39/1.00    inference(rectify,[],[f33])).
% 2.39/1.00  
% 2.39/1.00  fof(f35,plain,(
% 2.39/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.39/1.00    introduced(choice_axiom,[])).
% 2.39/1.00  
% 2.39/1.00  fof(f36,plain,(
% 2.39/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.39/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 2.39/1.00  
% 2.39/1.00  fof(f50,plain,(
% 2.39/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.39/1.00    inference(cnf_transformation,[],[f36])).
% 2.39/1.00  
% 2.39/1.00  fof(f8,axiom,(
% 2.39/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.00  
% 2.39/1.00  fof(f25,plain,(
% 2.39/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.39/1.00    inference(ennf_transformation,[],[f8])).
% 2.39/1.00  
% 2.39/1.00  fof(f63,plain,(
% 2.39/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.39/1.00    inference(cnf_transformation,[],[f25])).
% 2.39/1.00  
% 2.39/1.00  fof(f51,plain,(
% 2.39/1.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.39/1.00    inference(cnf_transformation,[],[f36])).
% 2.39/1.00  
% 2.39/1.00  fof(f6,axiom,(
% 2.39/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 2.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.00  
% 2.39/1.00  fof(f22,plain,(
% 2.39/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 2.39/1.00    inference(ennf_transformation,[],[f6])).
% 2.39/1.00  
% 2.39/1.00  fof(f37,plain,(
% 2.39/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.39/1.00    inference(nnf_transformation,[],[f22])).
% 2.39/1.00  
% 2.39/1.00  fof(f38,plain,(
% 2.39/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.39/1.00    inference(rectify,[],[f37])).
% 2.39/1.00  
% 2.39/1.00  fof(f39,plain,(
% 2.39/1.00    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 2.39/1.00    introduced(choice_axiom,[])).
% 2.39/1.00  
% 2.39/1.00  fof(f40,plain,(
% 2.39/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.39/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).
% 2.39/1.00  
% 2.39/1.00  fof(f57,plain,(
% 2.39/1.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.39/1.00    inference(cnf_transformation,[],[f40])).
% 2.39/1.00  
% 2.39/1.00  fof(f10,axiom,(
% 2.39/1.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.00  
% 2.39/1.00  fof(f27,plain,(
% 2.39/1.00    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.39/1.00    inference(ennf_transformation,[],[f10])).
% 2.39/1.00  
% 2.39/1.00  fof(f65,plain,(
% 2.39/1.00    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 2.39/1.00    inference(cnf_transformation,[],[f27])).
% 2.39/1.00  
% 2.39/1.00  fof(f9,axiom,(
% 2.39/1.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 2.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.00  
% 2.39/1.00  fof(f26,plain,(
% 2.39/1.00    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.39/1.00    inference(ennf_transformation,[],[f9])).
% 2.39/1.00  
% 2.39/1.00  fof(f64,plain,(
% 2.39/1.00    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.39/1.00    inference(cnf_transformation,[],[f26])).
% 2.39/1.00  
% 2.39/1.00  fof(f11,axiom,(
% 2.39/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 2.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.00  
% 2.39/1.00  fof(f28,plain,(
% 2.39/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.39/1.00    inference(ennf_transformation,[],[f11])).
% 2.39/1.00  
% 2.39/1.00  fof(f66,plain,(
% 2.39/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.39/1.00    inference(cnf_transformation,[],[f28])).
% 2.39/1.00  
% 2.39/1.00  fof(f5,axiom,(
% 2.39/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.00  
% 2.39/1.00  fof(f20,plain,(
% 2.39/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.39/1.00    inference(ennf_transformation,[],[f5])).
% 2.39/1.00  
% 2.39/1.00  fof(f21,plain,(
% 2.39/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.39/1.00    inference(flattening,[],[f20])).
% 2.39/1.00  
% 2.39/1.00  fof(f55,plain,(
% 2.39/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.39/1.00    inference(cnf_transformation,[],[f21])).
% 2.39/1.00  
% 2.39/1.00  fof(f69,plain,(
% 2.39/1.00    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK2(X1,X2,X3,X4),X4),X3) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.39/1.00    inference(cnf_transformation,[],[f46])).
% 2.39/1.00  
% 2.39/1.00  fof(f7,axiom,(
% 2.39/1.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 2.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.00  
% 2.39/1.00  fof(f23,plain,(
% 2.39/1.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.39/1.00    inference(ennf_transformation,[],[f7])).
% 2.39/1.00  
% 2.39/1.00  fof(f24,plain,(
% 2.39/1.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.39/1.00    inference(flattening,[],[f23])).
% 2.39/1.00  
% 2.39/1.00  fof(f41,plain,(
% 2.39/1.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.39/1.00    inference(nnf_transformation,[],[f24])).
% 2.39/1.00  
% 2.39/1.00  fof(f42,plain,(
% 2.39/1.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.39/1.00    inference(flattening,[],[f41])).
% 2.39/1.00  
% 2.39/1.00  fof(f61,plain,(
% 2.39/1.00    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.39/1.00    inference(cnf_transformation,[],[f42])).
% 2.39/1.00  
% 2.39/1.00  fof(f72,plain,(
% 2.39/1.00    v1_funct_1(sK6)),
% 2.39/1.00    inference(cnf_transformation,[],[f49])).
% 2.39/1.00  
% 2.39/1.00  fof(f58,plain,(
% 2.39/1.00    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.39/1.00    inference(cnf_transformation,[],[f40])).
% 2.39/1.00  
% 2.39/1.00  fof(f75,plain,(
% 2.39/1.00    ( ! [X5] : (k1_funct_1(sK6,X5) != sK7 | ~r2_hidden(X5,sK5) | ~r2_hidden(X5,sK3)) )),
% 2.39/1.00    inference(cnf_transformation,[],[f49])).
% 2.39/1.00  
% 2.39/1.00  fof(f68,plain,(
% 2.39/1.00    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK2(X1,X2,X3,X4),X2) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.39/1.00    inference(cnf_transformation,[],[f46])).
% 2.39/1.00  
% 2.39/1.00  fof(f4,axiom,(
% 2.39/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.00  
% 2.39/1.00  fof(f18,plain,(
% 2.39/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.39/1.00    inference(ennf_transformation,[],[f4])).
% 2.39/1.00  
% 2.39/1.00  fof(f19,plain,(
% 2.39/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.39/1.00    inference(flattening,[],[f18])).
% 2.39/1.00  
% 2.39/1.00  fof(f54,plain,(
% 2.39/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.39/1.00    inference(cnf_transformation,[],[f19])).
% 2.39/1.00  
% 2.39/1.00  cnf(c_24,negated_conjecture,
% 2.39/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 2.39/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1216,plain,
% 2.39/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.39/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_17,plain,
% 2.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.39/1.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.39/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1223,plain,
% 2.39/1.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.39/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.39/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_2647,plain,
% 2.39/1.00      ( k7_relset_1(sK3,sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
% 2.39/1.00      inference(superposition,[status(thm)],[c_1216,c_1223]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_19,plain,
% 2.39/1.00      ( ~ m1_subset_1(X0,X1)
% 2.39/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 2.39/1.00      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 2.39/1.00      | r2_hidden(sK2(X4,X3,X2,X0),X4)
% 2.39/1.00      | v1_xboole_0(X1)
% 2.39/1.00      | v1_xboole_0(X3)
% 2.39/1.00      | v1_xboole_0(X4) ),
% 2.39/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1221,plain,
% 2.39/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 2.39/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 2.39/1.00      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 2.39/1.00      | r2_hidden(sK2(X4,X3,X2,X0),X4) = iProver_top
% 2.39/1.00      | v1_xboole_0(X1) = iProver_top
% 2.39/1.00      | v1_xboole_0(X3) = iProver_top
% 2.39/1.00      | v1_xboole_0(X4) = iProver_top ),
% 2.39/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_3836,plain,
% 2.39/1.00      ( m1_subset_1(X0,sK4) != iProver_top
% 2.39/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 2.39/1.00      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 2.39/1.00      | r2_hidden(sK2(X1,sK3,sK6,X0),X1) = iProver_top
% 2.39/1.00      | v1_xboole_0(X1) = iProver_top
% 2.39/1.00      | v1_xboole_0(sK4) = iProver_top
% 2.39/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 2.39/1.00      inference(superposition,[status(thm)],[c_2647,c_1221]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_27,plain,
% 2.39/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.39/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_23,negated_conjecture,
% 2.39/1.00      ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
% 2.39/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_28,plain,
% 2.39/1.00      ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
% 2.39/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1,plain,
% 2.39/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.39/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1463,plain,
% 2.39/1.00      ( ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
% 2.39/1.00      | ~ v1_xboole_0(k7_relset_1(sK3,sK4,sK6,sK5)) ),
% 2.39/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1464,plain,
% 2.39/1.00      ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) != iProver_top
% 2.39/1.00      | v1_xboole_0(k7_relset_1(sK3,sK4,sK6,sK5)) != iProver_top ),
% 2.39/1.00      inference(predicate_to_equality,[status(thm)],[c_1463]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_13,plain,
% 2.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.39/1.00      | v1_relat_1(X0) ),
% 2.39/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1473,plain,
% 2.39/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.39/1.00      | v1_relat_1(sK6) ),
% 2.39/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1474,plain,
% 2.39/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 2.39/1.00      | v1_relat_1(sK6) = iProver_top ),
% 2.39/1.00      inference(predicate_to_equality,[status(thm)],[c_1473]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_777,plain,
% 2.39/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.39/1.00      theory(equality) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1587,plain,
% 2.39/1.00      ( ~ v1_xboole_0(X0)
% 2.39/1.00      | v1_xboole_0(k7_relset_1(sK3,sK4,sK6,sK5))
% 2.39/1.00      | k7_relset_1(sK3,sK4,sK6,sK5) != X0 ),
% 2.39/1.00      inference(instantiation,[status(thm)],[c_777]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1776,plain,
% 2.39/1.00      ( v1_xboole_0(k7_relset_1(sK3,sK4,sK6,sK5))
% 2.39/1.00      | ~ v1_xboole_0(k9_relat_1(sK6,sK5))
% 2.39/1.00      | k7_relset_1(sK3,sK4,sK6,sK5) != k9_relat_1(sK6,sK5) ),
% 2.39/1.00      inference(instantiation,[status(thm)],[c_1587]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1778,plain,
% 2.39/1.00      ( k7_relset_1(sK3,sK4,sK6,sK5) != k9_relat_1(sK6,sK5)
% 2.39/1.00      | v1_xboole_0(k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top
% 2.39/1.00      | v1_xboole_0(k9_relat_1(sK6,sK5)) != iProver_top ),
% 2.39/1.00      inference(predicate_to_equality,[status(thm)],[c_1776]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1517,plain,
% 2.39/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.39/1.00      | k7_relset_1(sK3,sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
% 2.39/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1777,plain,
% 2.39/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.39/1.00      | k7_relset_1(sK3,sK4,sK6,sK5) = k9_relat_1(sK6,sK5) ),
% 2.39/1.00      inference(instantiation,[status(thm)],[c_1517]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_0,plain,
% 2.39/1.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.39/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_2121,plain,
% 2.39/1.00      ( r2_hidden(sK0(k9_relat_1(sK6,sK5)),k9_relat_1(sK6,sK5))
% 2.39/1.00      | v1_xboole_0(k9_relat_1(sK6,sK5)) ),
% 2.39/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_2122,plain,
% 2.39/1.00      ( r2_hidden(sK0(k9_relat_1(sK6,sK5)),k9_relat_1(sK6,sK5)) = iProver_top
% 2.39/1.00      | v1_xboole_0(k9_relat_1(sK6,sK5)) = iProver_top ),
% 2.39/1.00      inference(predicate_to_equality,[status(thm)],[c_2121]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_8,plain,
% 2.39/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.39/1.00      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 2.39/1.00      | ~ v1_relat_1(X1) ),
% 2.39/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_2635,plain,
% 2.39/1.00      ( r2_hidden(k4_tarski(sK1(sK0(k9_relat_1(sK6,sK5)),sK5,sK6),sK0(k9_relat_1(sK6,sK5))),sK6)
% 2.39/1.00      | ~ r2_hidden(sK0(k9_relat_1(sK6,sK5)),k9_relat_1(sK6,sK5))
% 2.39/1.00      | ~ v1_relat_1(sK6) ),
% 2.39/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_2642,plain,
% 2.39/1.00      ( r2_hidden(k4_tarski(sK1(sK0(k9_relat_1(sK6,sK5)),sK5,sK6),sK0(k9_relat_1(sK6,sK5))),sK6) = iProver_top
% 2.39/1.00      | r2_hidden(sK0(k9_relat_1(sK6,sK5)),k9_relat_1(sK6,sK5)) != iProver_top
% 2.39/1.00      | v1_relat_1(sK6) != iProver_top ),
% 2.39/1.00      inference(predicate_to_equality,[status(thm)],[c_2635]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_15,plain,
% 2.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.39/1.00      | ~ v1_xboole_0(X2)
% 2.39/1.00      | v1_xboole_0(X0) ),
% 2.39/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1225,plain,
% 2.39/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.39/1.00      | v1_xboole_0(X2) != iProver_top
% 2.39/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.39/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_2840,plain,
% 2.39/1.00      ( v1_xboole_0(sK4) != iProver_top
% 2.39/1.00      | v1_xboole_0(sK6) = iProver_top ),
% 2.39/1.00      inference(superposition,[status(thm)],[c_1216,c_1225]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_14,plain,
% 2.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.39/1.00      | ~ v1_xboole_0(X1)
% 2.39/1.00      | v1_xboole_0(X0) ),
% 2.39/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1226,plain,
% 2.39/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.39/1.00      | v1_xboole_0(X1) != iProver_top
% 2.39/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.39/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_2860,plain,
% 2.39/1.00      ( v1_xboole_0(sK3) != iProver_top
% 2.39/1.00      | v1_xboole_0(sK6) = iProver_top ),
% 2.39/1.00      inference(superposition,[status(thm)],[c_1216,c_1226]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_16,plain,
% 2.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.39/1.00      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
% 2.39/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1224,plain,
% 2.39/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.39/1.00      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
% 2.39/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_2990,plain,
% 2.39/1.00      ( m1_subset_1(k9_relat_1(sK6,X0),k1_zfmisc_1(sK4)) = iProver_top
% 2.39/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
% 2.39/1.00      inference(superposition,[status(thm)],[c_2647,c_1224]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_3638,plain,
% 2.39/1.00      ( m1_subset_1(k9_relat_1(sK6,X0),k1_zfmisc_1(sK4)) = iProver_top ),
% 2.39/1.00      inference(global_propositional_subsumption,
% 2.39/1.00                [status(thm)],
% 2.39/1.00                [c_2990,c_27]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_5,plain,
% 2.39/1.00      ( m1_subset_1(X0,X1)
% 2.39/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.39/1.00      | ~ r2_hidden(X0,X2) ),
% 2.39/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1232,plain,
% 2.39/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 2.39/1.00      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.39/1.00      | r2_hidden(X0,X2) != iProver_top ),
% 2.39/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_3877,plain,
% 2.39/1.00      ( m1_subset_1(X0,sK4) = iProver_top
% 2.39/1.00      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
% 2.39/1.00      inference(superposition,[status(thm)],[c_3638,c_1232]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_5520,plain,
% 2.39/1.00      ( ~ r2_hidden(k4_tarski(sK1(sK0(k9_relat_1(sK6,sK5)),sK5,sK6),sK0(k9_relat_1(sK6,sK5))),sK6)
% 2.39/1.00      | ~ v1_xboole_0(sK6) ),
% 2.39/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_5521,plain,
% 2.39/1.00      ( r2_hidden(k4_tarski(sK1(sK0(k9_relat_1(sK6,sK5)),sK5,sK6),sK0(k9_relat_1(sK6,sK5))),sK6) != iProver_top
% 2.39/1.00      | v1_xboole_0(sK6) != iProver_top ),
% 2.39/1.00      inference(predicate_to_equality,[status(thm)],[c_5520]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_5709,plain,
% 2.39/1.00      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 2.39/1.00      | r2_hidden(sK2(X1,sK3,sK6,X0),X1) = iProver_top
% 2.39/1.00      | v1_xboole_0(X1) = iProver_top ),
% 2.39/1.00      inference(global_propositional_subsumption,
% 2.39/1.00                [status(thm)],
% 2.39/1.00                [c_3836,c_24,c_27,c_28,c_1464,c_1474,c_1778,c_1777,
% 2.39/1.00                 c_2122,c_2642,c_2840,c_2860,c_3877,c_5521]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1217,plain,
% 2.39/1.00      ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
% 2.39/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_2980,plain,
% 2.39/1.00      ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) = iProver_top ),
% 2.39/1.00      inference(demodulation,[status(thm)],[c_2647,c_1217]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_20,plain,
% 2.39/1.00      ( ~ m1_subset_1(X0,X1)
% 2.39/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 2.39/1.00      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 2.39/1.00      | r2_hidden(k4_tarski(sK2(X4,X3,X2,X0),X0),X2)
% 2.39/1.00      | v1_xboole_0(X1)
% 2.39/1.00      | v1_xboole_0(X3)
% 2.39/1.00      | v1_xboole_0(X4) ),
% 2.39/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1220,plain,
% 2.39/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 2.39/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 2.39/1.00      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 2.39/1.00      | r2_hidden(k4_tarski(sK2(X4,X3,X2,X0),X0),X2) = iProver_top
% 2.39/1.00      | v1_xboole_0(X1) = iProver_top
% 2.39/1.00      | v1_xboole_0(X3) = iProver_top
% 2.39/1.00      | v1_xboole_0(X4) = iProver_top ),
% 2.39/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_2991,plain,
% 2.39/1.00      ( m1_subset_1(X0,sK4) != iProver_top
% 2.39/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 2.39/1.00      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 2.39/1.00      | r2_hidden(k4_tarski(sK2(X1,sK3,sK6,X0),X0),sK6) = iProver_top
% 2.39/1.00      | v1_xboole_0(X1) = iProver_top
% 2.39/1.00      | v1_xboole_0(sK4) = iProver_top
% 2.39/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 2.39/1.00      inference(superposition,[status(thm)],[c_2647,c_1220]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_6161,plain,
% 2.39/1.00      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 2.39/1.00      | r2_hidden(k4_tarski(sK2(X1,sK3,sK6,X0),X0),sK6) = iProver_top
% 2.39/1.00      | v1_xboole_0(X1) = iProver_top ),
% 2.39/1.00      inference(global_propositional_subsumption,
% 2.39/1.00                [status(thm)],
% 2.39/1.00                [c_2991,c_24,c_27,c_28,c_1464,c_1474,c_1778,c_1777,
% 2.39/1.00                 c_2122,c_2642,c_2840,c_2860,c_3877,c_5521]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_11,plain,
% 2.39/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 2.39/1.00      | ~ v1_funct_1(X2)
% 2.39/1.00      | ~ v1_relat_1(X2)
% 2.39/1.00      | k1_funct_1(X2,X0) = X1 ),
% 2.39/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_25,negated_conjecture,
% 2.39/1.00      ( v1_funct_1(sK6) ),
% 2.39/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_324,plain,
% 2.39/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 2.39/1.00      | ~ v1_relat_1(X2)
% 2.39/1.00      | k1_funct_1(X2,X0) = X1
% 2.39/1.00      | sK6 != X2 ),
% 2.39/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_25]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_325,plain,
% 2.39/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),sK6)
% 2.39/1.00      | ~ v1_relat_1(sK6)
% 2.39/1.00      | k1_funct_1(sK6,X0) = X1 ),
% 2.39/1.00      inference(unflattening,[status(thm)],[c_324]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1213,plain,
% 2.39/1.00      ( k1_funct_1(sK6,X0) = X1
% 2.39/1.00      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
% 2.39/1.00      | v1_relat_1(sK6) != iProver_top ),
% 2.39/1.00      inference(predicate_to_equality,[status(thm)],[c_325]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_326,plain,
% 2.39/1.00      ( k1_funct_1(sK6,X0) = X1
% 2.39/1.00      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
% 2.39/1.00      | v1_relat_1(sK6) != iProver_top ),
% 2.39/1.00      inference(predicate_to_equality,[status(thm)],[c_325]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1504,plain,
% 2.39/1.00      ( r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
% 2.39/1.00      | k1_funct_1(sK6,X0) = X1 ),
% 2.39/1.00      inference(global_propositional_subsumption,
% 2.39/1.00                [status(thm)],
% 2.39/1.00                [c_1213,c_27,c_326,c_1474]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1505,plain,
% 2.39/1.00      ( k1_funct_1(sK6,X0) = X1
% 2.39/1.00      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top ),
% 2.39/1.00      inference(renaming,[status(thm)],[c_1504]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_6175,plain,
% 2.39/1.00      ( k1_funct_1(sK6,sK2(X0,sK3,sK6,X1)) = X1
% 2.39/1.00      | r2_hidden(X1,k9_relat_1(sK6,X0)) != iProver_top
% 2.39/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.39/1.00      inference(superposition,[status(thm)],[c_6161,c_1505]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_6264,plain,
% 2.39/1.00      ( k1_funct_1(sK6,sK2(sK5,sK3,sK6,sK7)) = sK7
% 2.39/1.00      | v1_xboole_0(sK5) = iProver_top ),
% 2.39/1.00      inference(superposition,[status(thm)],[c_2980,c_6175]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_7,plain,
% 2.39/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.39/1.00      | r2_hidden(sK1(X0,X2,X1),X2)
% 2.39/1.00      | ~ v1_relat_1(X1) ),
% 2.39/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_2637,plain,
% 2.39/1.00      ( r2_hidden(sK1(sK0(k9_relat_1(sK6,sK5)),sK5,sK6),sK5)
% 2.39/1.00      | ~ r2_hidden(sK0(k9_relat_1(sK6,sK5)),k9_relat_1(sK6,sK5))
% 2.39/1.00      | ~ v1_relat_1(sK6) ),
% 2.39/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_2443,plain,
% 2.39/1.00      ( m1_subset_1(sK7,sK4) != iProver_top
% 2.39/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 2.39/1.00      | r2_hidden(k4_tarski(sK2(sK5,sK3,sK6,sK7),sK7),sK6) = iProver_top
% 2.39/1.00      | v1_xboole_0(sK4) = iProver_top
% 2.39/1.00      | v1_xboole_0(sK3) = iProver_top
% 2.39/1.00      | v1_xboole_0(sK5) = iProver_top ),
% 2.39/1.00      inference(superposition,[status(thm)],[c_1217,c_1220]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1494,plain,
% 2.39/1.00      ( ~ m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(X0))
% 2.39/1.00      | m1_subset_1(sK7,X0)
% 2.39/1.00      | ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
% 2.39/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1640,plain,
% 2.39/1.00      ( ~ m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(sK4))
% 2.39/1.00      | m1_subset_1(sK7,sK4)
% 2.39/1.00      | ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
% 2.39/1.00      inference(instantiation,[status(thm)],[c_1494]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1642,plain,
% 2.39/1.00      ( m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(sK4)) != iProver_top
% 2.39/1.00      | m1_subset_1(sK7,sK4) = iProver_top
% 2.39/1.00      | r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) != iProver_top ),
% 2.39/1.00      inference(predicate_to_equality,[status(thm)],[c_1640]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1512,plain,
% 2.39/1.00      ( m1_subset_1(k7_relset_1(sK3,sK4,sK6,X0),k1_zfmisc_1(sK4))
% 2.39/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 2.39/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1641,plain,
% 2.39/1.00      ( m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(sK4))
% 2.39/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 2.39/1.00      inference(instantiation,[status(thm)],[c_1512]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1644,plain,
% 2.39/1.00      ( m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(sK4)) = iProver_top
% 2.39/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
% 2.39/1.00      inference(predicate_to_equality,[status(thm)],[c_1641]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_3498,plain,
% 2.39/1.00      ( r2_hidden(k4_tarski(sK2(sK5,sK3,sK6,sK7),sK7),sK6) = iProver_top
% 2.39/1.00      | v1_xboole_0(sK4) = iProver_top
% 2.39/1.00      | v1_xboole_0(sK3) = iProver_top
% 2.39/1.00      | v1_xboole_0(sK5) = iProver_top ),
% 2.39/1.00      inference(global_propositional_subsumption,
% 2.39/1.00                [status(thm)],
% 2.39/1.00                [c_2443,c_27,c_28,c_1642,c_1644]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_3509,plain,
% 2.39/1.00      ( k1_funct_1(sK6,sK2(sK5,sK3,sK6,sK7)) = sK7
% 2.39/1.00      | v1_xboole_0(sK4) = iProver_top
% 2.39/1.00      | v1_xboole_0(sK3) = iProver_top
% 2.39/1.00      | v1_xboole_0(sK5) = iProver_top ),
% 2.39/1.00      inference(superposition,[status(thm)],[c_3498,c_1505]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_4654,plain,
% 2.39/1.00      ( k1_funct_1(sK6,sK2(sK5,sK3,sK6,sK7)) = sK7
% 2.39/1.00      | v1_xboole_0(sK3) = iProver_top
% 2.39/1.00      | v1_xboole_0(sK5) = iProver_top
% 2.39/1.00      | v1_xboole_0(sK6) = iProver_top ),
% 2.39/1.00      inference(superposition,[status(thm)],[c_3509,c_2840]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_5365,plain,
% 2.39/1.00      ( k1_funct_1(sK6,sK2(sK5,sK3,sK6,sK7)) = sK7
% 2.39/1.00      | v1_xboole_0(sK5) = iProver_top
% 2.39/1.00      | v1_xboole_0(sK6) = iProver_top ),
% 2.39/1.00      inference(global_propositional_subsumption,
% 2.39/1.00                [status(thm)],
% 2.39/1.00                [c_4654,c_2860]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_5367,plain,
% 2.39/1.00      ( v1_xboole_0(sK5)
% 2.39/1.00      | v1_xboole_0(sK6)
% 2.39/1.00      | k1_funct_1(sK6,sK2(sK5,sK3,sK6,sK7)) = sK7 ),
% 2.39/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_5365]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_5574,plain,
% 2.39/1.00      ( ~ r2_hidden(sK1(sK0(k9_relat_1(sK6,sK5)),sK5,sK6),sK5)
% 2.39/1.00      | ~ v1_xboole_0(sK5) ),
% 2.39/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_6326,plain,
% 2.39/1.00      ( k1_funct_1(sK6,sK2(sK5,sK3,sK6,sK7)) = sK7 ),
% 2.39/1.00      inference(global_propositional_subsumption,
% 2.39/1.00                [status(thm)],
% 2.39/1.00                [c_6264,c_24,c_23,c_1463,c_1473,c_1776,c_1777,c_2121,
% 2.39/1.00                 c_2637,c_2635,c_5367,c_5520,c_5574]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_22,negated_conjecture,
% 2.39/1.00      ( ~ r2_hidden(X0,sK3)
% 2.39/1.00      | ~ r2_hidden(X0,sK5)
% 2.39/1.00      | k1_funct_1(sK6,X0) != sK7 ),
% 2.39/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1218,plain,
% 2.39/1.00      ( k1_funct_1(sK6,X0) != sK7
% 2.39/1.00      | r2_hidden(X0,sK3) != iProver_top
% 2.39/1.00      | r2_hidden(X0,sK5) != iProver_top ),
% 2.39/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_6332,plain,
% 2.39/1.00      ( r2_hidden(sK2(sK5,sK3,sK6,sK7),sK3) != iProver_top
% 2.39/1.00      | r2_hidden(sK2(sK5,sK3,sK6,sK7),sK5) != iProver_top ),
% 2.39/1.00      inference(superposition,[status(thm)],[c_6326,c_1218]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_21,plain,
% 2.39/1.00      ( ~ m1_subset_1(X0,X1)
% 2.39/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 2.39/1.00      | m1_subset_1(sK2(X4,X3,X2,X0),X3)
% 2.39/1.00      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 2.39/1.00      | v1_xboole_0(X1)
% 2.39/1.00      | v1_xboole_0(X3)
% 2.39/1.00      | v1_xboole_0(X4) ),
% 2.39/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1219,plain,
% 2.39/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 2.39/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 2.39/1.00      | m1_subset_1(sK2(X4,X3,X2,X0),X3) = iProver_top
% 2.39/1.00      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 2.39/1.00      | v1_xboole_0(X1) = iProver_top
% 2.39/1.00      | v1_xboole_0(X3) = iProver_top
% 2.39/1.00      | v1_xboole_0(X4) = iProver_top ),
% 2.39/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1691,plain,
% 2.39/1.00      ( m1_subset_1(sK2(sK5,sK3,sK6,sK7),sK3) = iProver_top
% 2.39/1.00      | m1_subset_1(sK7,sK4) != iProver_top
% 2.39/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 2.39/1.00      | v1_xboole_0(sK4) = iProver_top
% 2.39/1.00      | v1_xboole_0(sK3) = iProver_top
% 2.39/1.00      | v1_xboole_0(sK5) = iProver_top ),
% 2.39/1.00      inference(superposition,[status(thm)],[c_1217,c_1219]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_2109,plain,
% 2.39/1.00      ( m1_subset_1(sK2(sK5,sK3,sK6,sK7),sK3) = iProver_top
% 2.39/1.00      | v1_xboole_0(sK4) = iProver_top
% 2.39/1.00      | v1_xboole_0(sK3) = iProver_top
% 2.39/1.00      | v1_xboole_0(sK5) = iProver_top ),
% 2.39/1.00      inference(global_propositional_subsumption,
% 2.39/1.00                [status(thm)],
% 2.39/1.00                [c_1691,c_27,c_28,c_1642,c_1644]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_4,plain,
% 2.39/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.39/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_1233,plain,
% 2.39/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 2.39/1.00      | r2_hidden(X0,X1) = iProver_top
% 2.39/1.00      | v1_xboole_0(X1) = iProver_top ),
% 2.39/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_2117,plain,
% 2.39/1.00      ( r2_hidden(sK2(sK5,sK3,sK6,sK7),sK3) = iProver_top
% 2.39/1.00      | v1_xboole_0(sK4) = iProver_top
% 2.39/1.00      | v1_xboole_0(sK3) = iProver_top
% 2.39/1.00      | v1_xboole_0(sK5) = iProver_top ),
% 2.39/1.00      inference(superposition,[status(thm)],[c_2109,c_1233]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_2638,plain,
% 2.39/1.00      ( r2_hidden(sK1(sK0(k9_relat_1(sK6,sK5)),sK5,sK6),sK5) = iProver_top
% 2.39/1.00      | r2_hidden(sK0(k9_relat_1(sK6,sK5)),k9_relat_1(sK6,sK5)) != iProver_top
% 2.39/1.00      | v1_relat_1(sK6) != iProver_top ),
% 2.39/1.00      inference(predicate_to_equality,[status(thm)],[c_2637]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_5575,plain,
% 2.39/1.00      ( r2_hidden(sK1(sK0(k9_relat_1(sK6,sK5)),sK5,sK6),sK5) != iProver_top
% 2.39/1.00      | v1_xboole_0(sK5) != iProver_top ),
% 2.39/1.00      inference(predicate_to_equality,[status(thm)],[c_5574]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_6385,plain,
% 2.39/1.00      ( r2_hidden(sK2(sK5,sK3,sK6,sK7),sK5) != iProver_top ),
% 2.39/1.00      inference(global_propositional_subsumption,
% 2.39/1.00                [status(thm)],
% 2.39/1.00                [c_6332,c_24,c_27,c_28,c_1464,c_1474,c_1778,c_1777,
% 2.39/1.00                 c_2117,c_2122,c_2638,c_2642,c_2840,c_2860,c_5521,c_5575]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(c_6390,plain,
% 2.39/1.00      ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
% 2.39/1.00      | v1_xboole_0(sK5) = iProver_top ),
% 2.39/1.00      inference(superposition,[status(thm)],[c_5709,c_6385]) ).
% 2.39/1.00  
% 2.39/1.00  cnf(contradiction,plain,
% 2.39/1.00      ( $false ),
% 2.39/1.00      inference(minisat,
% 2.39/1.00                [status(thm)],
% 2.39/1.00                [c_6390,c_5575,c_2980,c_2638,c_2122,c_1777,c_1778,c_1474,
% 2.39/1.00                 c_1464,c_28,c_27,c_24]) ).
% 2.39/1.00  
% 2.39/1.00  
% 2.39/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.39/1.00  
% 2.39/1.00  ------                               Statistics
% 2.39/1.00  
% 2.39/1.00  ------ General
% 2.39/1.00  
% 2.39/1.00  abstr_ref_over_cycles:                  0
% 2.39/1.00  abstr_ref_under_cycles:                 0
% 2.39/1.00  gc_basic_clause_elim:                   0
% 2.39/1.00  forced_gc_time:                         0
% 2.39/1.00  parsing_time:                           0.01
% 2.39/1.00  unif_index_cands_time:                  0.
% 2.39/1.00  unif_index_add_time:                    0.
% 2.39/1.00  orderings_time:                         0.
% 2.39/1.00  out_proof_time:                         0.01
% 2.39/1.00  total_time:                             0.241
% 2.39/1.00  num_of_symbols:                         51
% 2.39/1.00  num_of_terms:                           7994
% 2.39/1.00  
% 2.39/1.00  ------ Preprocessing
% 2.39/1.00  
% 2.39/1.00  num_of_splits:                          0
% 2.39/1.00  num_of_split_atoms:                     0
% 2.39/1.00  num_of_reused_defs:                     0
% 2.39/1.00  num_eq_ax_congr_red:                    35
% 2.39/1.00  num_of_sem_filtered_clauses:            1
% 2.39/1.00  num_of_subtypes:                        0
% 2.39/1.00  monotx_restored_types:                  0
% 2.39/1.00  sat_num_of_epr_types:                   0
% 2.39/1.00  sat_num_of_non_cyclic_types:            0
% 2.39/1.00  sat_guarded_non_collapsed_types:        0
% 2.39/1.00  num_pure_diseq_elim:                    0
% 2.39/1.00  simp_replaced_by:                       0
% 2.39/1.00  res_preprocessed:                       126
% 2.39/1.00  prep_upred:                             0
% 2.39/1.00  prep_unflattend:                        17
% 2.39/1.00  smt_new_axioms:                         0
% 2.39/1.00  pred_elim_cands:                        4
% 2.39/1.00  pred_elim:                              1
% 2.39/1.00  pred_elim_cl:                           1
% 2.39/1.00  pred_elim_cycles:                       3
% 2.39/1.00  merged_defs:                            0
% 2.39/1.00  merged_defs_ncl:                        0
% 2.39/1.00  bin_hyper_res:                          0
% 2.39/1.00  prep_cycles:                            4
% 2.39/1.00  pred_elim_time:                         0.005
% 2.39/1.00  splitting_time:                         0.
% 2.39/1.00  sem_filter_time:                        0.
% 2.39/1.00  monotx_time:                            0.
% 2.39/1.00  subtype_inf_time:                       0.
% 2.39/1.00  
% 2.39/1.00  ------ Problem properties
% 2.39/1.00  
% 2.39/1.00  clauses:                                25
% 2.39/1.00  conjectures:                            3
% 2.39/1.00  epr:                                    3
% 2.39/1.00  horn:                                   19
% 2.39/1.00  ground:                                 2
% 2.39/1.00  unary:                                  3
% 2.39/1.00  binary:                                 6
% 2.39/1.00  lits:                                   83
% 2.39/1.00  lits_eq:                                3
% 2.39/1.00  fd_pure:                                0
% 2.39/1.00  fd_pseudo:                              0
% 2.39/1.00  fd_cond:                                0
% 2.39/1.00  fd_pseudo_cond:                         1
% 2.39/1.00  ac_symbols:                             0
% 2.39/1.00  
% 2.39/1.00  ------ Propositional Solver
% 2.39/1.00  
% 2.39/1.00  prop_solver_calls:                      27
% 2.39/1.00  prop_fast_solver_calls:                 1115
% 2.39/1.00  smt_solver_calls:                       0
% 2.39/1.00  smt_fast_solver_calls:                  0
% 2.39/1.00  prop_num_of_clauses:                    2645
% 2.39/1.00  prop_preprocess_simplified:             6891
% 2.39/1.00  prop_fo_subsumed:                       36
% 2.39/1.00  prop_solver_time:                       0.
% 2.39/1.00  smt_solver_time:                        0.
% 2.39/1.00  smt_fast_solver_time:                   0.
% 2.39/1.00  prop_fast_solver_time:                  0.
% 2.39/1.00  prop_unsat_core_time:                   0.
% 2.39/1.00  
% 2.39/1.00  ------ QBF
% 2.39/1.00  
% 2.39/1.00  qbf_q_res:                              0
% 2.39/1.00  qbf_num_tautologies:                    0
% 2.39/1.00  qbf_prep_cycles:                        0
% 2.39/1.00  
% 2.39/1.00  ------ BMC1
% 2.39/1.00  
% 2.39/1.00  bmc1_current_bound:                     -1
% 2.39/1.00  bmc1_last_solved_bound:                 -1
% 2.39/1.00  bmc1_unsat_core_size:                   -1
% 2.39/1.00  bmc1_unsat_core_parents_size:           -1
% 2.39/1.00  bmc1_merge_next_fun:                    0
% 2.39/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.39/1.00  
% 2.39/1.00  ------ Instantiation
% 2.39/1.00  
% 2.39/1.00  inst_num_of_clauses:                    635
% 2.39/1.00  inst_num_in_passive:                    8
% 2.39/1.00  inst_num_in_active:                     334
% 2.39/1.00  inst_num_in_unprocessed:                293
% 2.39/1.00  inst_num_of_loops:                      350
% 2.39/1.00  inst_num_of_learning_restarts:          0
% 2.39/1.00  inst_num_moves_active_passive:          14
% 2.39/1.00  inst_lit_activity:                      0
% 2.39/1.00  inst_lit_activity_moves:                0
% 2.39/1.00  inst_num_tautologies:                   0
% 2.39/1.00  inst_num_prop_implied:                  0
% 2.39/1.00  inst_num_existing_simplified:           0
% 2.39/1.00  inst_num_eq_res_simplified:             0
% 2.39/1.00  inst_num_child_elim:                    0
% 2.39/1.00  inst_num_of_dismatching_blockings:      168
% 2.39/1.00  inst_num_of_non_proper_insts:           530
% 2.39/1.00  inst_num_of_duplicates:                 0
% 2.39/1.00  inst_inst_num_from_inst_to_res:         0
% 2.39/1.00  inst_dismatching_checking_time:         0.
% 2.39/1.00  
% 2.39/1.00  ------ Resolution
% 2.39/1.00  
% 2.39/1.00  res_num_of_clauses:                     0
% 2.39/1.00  res_num_in_passive:                     0
% 2.39/1.00  res_num_in_active:                      0
% 2.39/1.00  res_num_of_loops:                       130
% 2.39/1.00  res_forward_subset_subsumed:            36
% 2.39/1.00  res_backward_subset_subsumed:           0
% 2.39/1.00  res_forward_subsumed:                   0
% 2.39/1.00  res_backward_subsumed:                  0
% 2.39/1.00  res_forward_subsumption_resolution:     0
% 2.39/1.00  res_backward_subsumption_resolution:    0
% 2.39/1.00  res_clause_to_clause_subsumption:       465
% 2.39/1.00  res_orphan_elimination:                 0
% 2.39/1.00  res_tautology_del:                      43
% 2.39/1.00  res_num_eq_res_simplified:              0
% 2.39/1.00  res_num_sel_changes:                    0
% 2.39/1.00  res_moves_from_active_to_pass:          0
% 2.39/1.00  
% 2.39/1.00  ------ Superposition
% 2.39/1.00  
% 2.39/1.00  sup_time_total:                         0.
% 2.39/1.00  sup_time_generating:                    0.
% 2.39/1.00  sup_time_sim_full:                      0.
% 2.39/1.00  sup_time_sim_immed:                     0.
% 2.39/1.00  
% 2.39/1.00  sup_num_of_clauses:                     135
% 2.39/1.00  sup_num_in_active:                      63
% 2.39/1.00  sup_num_in_passive:                     72
% 2.39/1.00  sup_num_of_loops:                       68
% 2.39/1.00  sup_fw_superposition:                   52
% 2.39/1.00  sup_bw_superposition:                   92
% 2.39/1.00  sup_immediate_simplified:               13
% 2.39/1.00  sup_given_eliminated:                   0
% 2.39/1.00  comparisons_done:                       0
% 2.39/1.00  comparisons_avoided:                    0
% 2.39/1.00  
% 2.39/1.00  ------ Simplifications
% 2.39/1.00  
% 2.39/1.00  
% 2.39/1.00  sim_fw_subset_subsumed:                 7
% 2.39/1.00  sim_bw_subset_subsumed:                 5
% 2.39/1.00  sim_fw_subsumed:                        5
% 2.39/1.00  sim_bw_subsumed:                        0
% 2.39/1.00  sim_fw_subsumption_res:                 3
% 2.39/1.00  sim_bw_subsumption_res:                 0
% 2.39/1.00  sim_tautology_del:                      7
% 2.39/1.00  sim_eq_tautology_del:                   1
% 2.39/1.00  sim_eq_res_simp:                        0
% 2.39/1.00  sim_fw_demodulated:                     0
% 2.39/1.00  sim_bw_demodulated:                     3
% 2.39/1.00  sim_light_normalised:                   0
% 2.39/1.00  sim_joinable_taut:                      0
% 2.39/1.00  sim_joinable_simp:                      0
% 2.39/1.00  sim_ac_normalised:                      0
% 2.39/1.00  sim_smt_subsumption:                    0
% 2.39/1.00  
%------------------------------------------------------------------------------
