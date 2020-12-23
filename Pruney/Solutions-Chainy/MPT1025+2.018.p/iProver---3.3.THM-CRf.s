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
% DateTime   : Thu Dec  3 12:08:03 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 718 expanded)
%              Number of clauses        :   84 ( 226 expanded)
%              Number of leaves         :   19 ( 157 expanded)
%              Depth                    :   17
%              Number of atoms          :  591 (3204 expanded)
%              Number of equality atoms :  145 ( 599 expanded)
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
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

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
    inference(ennf_transformation,[],[f15])).

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

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK8
            | ~ r2_hidden(X5,X2)
            | ~ m1_subset_1(X5,X0) )
        & r2_hidden(sK8,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
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
              ( k1_funct_1(sK7,X5) != X4
              | ~ r2_hidden(X5,sK6)
              | ~ m1_subset_1(X5,sK4) )
          & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6)) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ! [X5] :
        ( k1_funct_1(sK7,X5) != sK8
        | ~ r2_hidden(X5,sK6)
        | ~ m1_subset_1(X5,sK4) )
    & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f31,f52,f51])).

fof(f81,plain,(
    ! [X5] :
      ( k1_funct_1(sK7,X5) != sK8
      | ~ r2_hidden(X5,sK6)
      | ~ m1_subset_1(X5,sK4) ) ),
    inference(cnf_transformation,[],[f53])).

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
    inference(ennf_transformation,[],[f12])).

fof(f47,plain,(
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
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X4,X3,X2,X1] :
      ( ? [X6] :
          ( r2_hidden(X6,X1)
          & r2_hidden(k4_tarski(X6,X4),X3)
          & m1_subset_1(X6,X2) )
     => ( r2_hidden(sK3(X1,X2,X3,X4),X1)
        & r2_hidden(k4_tarski(sK3(X1,X2,X3,X4),X4),X3)
        & m1_subset_1(sK3(X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f48,f49])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK3(X1,X2,X3,X4),X1)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f79,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f53])).

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

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f80,plain,(
    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f53])).

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

fof(f41,plain,(
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

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

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

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK3(X1,X2,X3,X4),X4),X3)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

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

fof(f45,plain,(
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
    inference(flattening,[],[f45])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f78,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK3(X1,X2,X3,X4),X2)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_24,negated_conjecture,
    ( ~ m1_subset_1(X0,sK4)
    | ~ r2_hidden(X0,sK6)
    | k1_funct_1(sK7,X0) != sK8 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_11779,plain,
    ( ~ m1_subset_1(sK3(sK6,sK4,sK7,sK8),sK4)
    | ~ r2_hidden(sK3(sK6,sK4,sK7,sK8),sK6)
    | k1_funct_1(sK7,sK3(sK6,sK4,sK7,sK8)) != sK8 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | r2_hidden(sK3(X4,X3,X2,X0),X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1636,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK5)))
    | ~ m1_subset_1(X2,sK5)
    | ~ r2_hidden(X2,k7_relset_1(X1,sK5,X0,X3))
    | r2_hidden(sK3(X3,X1,X0,X2),X3)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_4837,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK5)))
    | ~ m1_subset_1(sK8,sK5)
    | r2_hidden(sK3(X2,X1,X0,sK8),X2)
    | ~ r2_hidden(sK8,k7_relset_1(X1,sK5,X0,X2))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1636])).

cnf(c_6506,plain,
    ( ~ m1_subset_1(sK8,sK5)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | r2_hidden(sK3(X0,sK4,sK7,sK8),X0)
    | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_4837])).

cnf(c_10378,plain,
    ( ~ m1_subset_1(sK8,sK5)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | r2_hidden(sK3(sK6,sK4,sK7,sK8),sK6)
    | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_6506])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1341,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1348,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2631,plain,
    ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
    inference(superposition,[status(thm)],[c_1341,c_1348])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1342,plain,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2843,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2631,c_1342])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1351,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK2(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1360,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3679,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_xboole_0(k1_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1351,c_1360])).

cnf(c_6539,plain,
    ( v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(k1_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2843,c_3679])).

cnf(c_6562,plain,
    ( ~ v1_relat_1(sK7)
    | ~ v1_xboole_0(k1_relat_1(sK7)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6539])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1353,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK2(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3589,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1353,c_1360])).

cnf(c_5982,plain,
    ( v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2843,c_3589])).

cnf(c_5993,plain,
    ( ~ v1_relat_1(sK7)
    | ~ v1_xboole_0(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5982])).

cnf(c_17,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_320,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_17,c_8])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_324,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_320,c_16])).

cnf(c_325,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_324])).

cnf(c_1340,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_325])).

cnf(c_1954,plain,
    ( r1_tarski(k1_relat_1(sK7),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1341,c_1340])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1361,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1357,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2734,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(sK0(X0),X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1361,c_1357])).

cnf(c_4403,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2734,c_1360])).

cnf(c_4436,plain,
    ( v1_xboole_0(k1_relat_1(sK7)) = iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1954,c_4403])).

cnf(c_4439,plain,
    ( v1_xboole_0(k1_relat_1(sK7))
    | ~ v1_xboole_0(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4436])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1349,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2846,plain,
    ( m1_subset_1(k9_relat_1(sK7,X0),k1_zfmisc_1(sK5)) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2631,c_1349])).

cnf(c_29,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3347,plain,
    ( m1_subset_1(k9_relat_1(sK7,X0),k1_zfmisc_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2846,c_29])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1356,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3578,plain,
    ( m1_subset_1(X0,sK5) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3347,c_1356])).

cnf(c_4003,plain,
    ( m1_subset_1(sK8,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2843,c_3578])).

cnf(c_4019,plain,
    ( m1_subset_1(sK8,sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4003])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | r2_hidden(k4_tarski(sK3(X4,X3,X2,X0),X0),X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1345,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | r2_hidden(k4_tarski(sK3(X4,X3,X2,X0),X0),X2) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3433,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK3(X1,sK4,sK7,X0),X0),sK7) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2631,c_1345])).

cnf(c_30,plain,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1396,plain,
    ( ~ m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(X0))
    | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1482,plain,
    ( ~ m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5))
    | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1396])).

cnf(c_1483,plain,
    ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5)) != iProver_top
    | r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1482])).

cnf(c_1944,plain,
    ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1945,plain,
    ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5)) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1944])).

cnf(c_3793,plain,
    ( v1_xboole_0(X1) = iProver_top
    | r2_hidden(k4_tarski(sK3(X1,sK4,sK7,X0),X0),sK7) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3433,c_29,c_30,c_1483,c_1945,c_3578])).

cnf(c_3794,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK3(X1,sK4,sK7,X0),X0),sK7) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_3793])).

cnf(c_14,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_419,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_27])).

cnf(c_420,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK7)
    | ~ v1_relat_1(sK7)
    | k1_funct_1(sK7,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_1337,plain,
    ( k1_funct_1(sK7,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_420])).

cnf(c_421,plain,
    ( k1_funct_1(sK7,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_420])).

cnf(c_1416,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1519,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1416])).

cnf(c_1520,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1519])).

cnf(c_1610,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
    | k1_funct_1(sK7,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1337,c_29,c_421,c_1520])).

cnf(c_1611,plain,
    ( k1_funct_1(sK7,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_1610])).

cnf(c_3802,plain,
    ( k1_funct_1(sK7,sK3(X0,sK4,sK7,X1)) = X1
    | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3794,c_1611])).

cnf(c_3819,plain,
    ( k1_funct_1(sK7,sK3(sK6,sK4,sK7,sK8)) = sK8
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2843,c_3802])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | m1_subset_1(sK3(X4,X3,X2,X0),X3)
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1344,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(sK3(X4,X3,X2,X0),X3) = iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2622,plain,
    ( m1_subset_1(sK3(sK6,sK4,sK7,sK8),sK4) = iProver_top
    | m1_subset_1(sK8,sK5) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1342,c_1344])).

cnf(c_3057,plain,
    ( m1_subset_1(sK3(sK6,sK4,sK7,sK8),sK4) = iProver_top
    | m1_subset_1(sK8,sK5) != iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2622,c_29,c_30,c_1483,c_1945])).

cnf(c_3059,plain,
    ( m1_subset_1(sK3(sK6,sK4,sK7,sK8),sK4)
    | ~ m1_subset_1(sK8,sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3057])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11779,c_10378,c_6562,c_6539,c_5993,c_5982,c_4439,c_4436,c_4019,c_3819,c_3059,c_1944,c_1520,c_1519,c_1482,c_25,c_29,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n006.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 12:27:22 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 3.75/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.75/0.98  
% 3.75/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.75/0.98  
% 3.75/0.98  ------  iProver source info
% 3.75/0.98  
% 3.75/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.75/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.75/0.98  git: non_committed_changes: false
% 3.75/0.98  git: last_make_outside_of_git: false
% 3.75/0.98  
% 3.75/0.98  ------ 
% 3.75/0.98  
% 3.75/0.98  ------ Input Options
% 3.75/0.98  
% 3.75/0.98  --out_options                           all
% 3.75/0.98  --tptp_safe_out                         true
% 3.75/0.98  --problem_path                          ""
% 3.75/0.98  --include_path                          ""
% 3.75/0.98  --clausifier                            res/vclausify_rel
% 3.75/0.98  --clausifier_options                    ""
% 3.75/0.98  --stdin                                 false
% 3.75/0.98  --stats_out                             all
% 3.75/0.98  
% 3.75/0.98  ------ General Options
% 3.75/0.98  
% 3.75/0.98  --fof                                   false
% 3.75/0.98  --time_out_real                         305.
% 3.75/0.98  --time_out_virtual                      -1.
% 3.75/0.98  --symbol_type_check                     false
% 3.75/0.98  --clausify_out                          false
% 3.75/0.98  --sig_cnt_out                           false
% 3.75/0.98  --trig_cnt_out                          false
% 3.75/0.98  --trig_cnt_out_tolerance                1.
% 3.75/0.98  --trig_cnt_out_sk_spl                   false
% 3.75/0.98  --abstr_cl_out                          false
% 3.75/0.98  
% 3.75/0.98  ------ Global Options
% 3.75/0.98  
% 3.75/0.98  --schedule                              default
% 3.75/0.98  --add_important_lit                     false
% 3.75/0.98  --prop_solver_per_cl                    1000
% 3.75/0.98  --min_unsat_core                        false
% 3.75/0.98  --soft_assumptions                      false
% 3.75/0.98  --soft_lemma_size                       3
% 3.75/0.98  --prop_impl_unit_size                   0
% 3.75/0.98  --prop_impl_unit                        []
% 3.75/0.98  --share_sel_clauses                     true
% 3.75/0.98  --reset_solvers                         false
% 3.75/0.98  --bc_imp_inh                            [conj_cone]
% 3.75/0.98  --conj_cone_tolerance                   3.
% 3.75/0.98  --extra_neg_conj                        none
% 3.75/0.98  --large_theory_mode                     true
% 3.75/0.98  --prolific_symb_bound                   200
% 3.75/0.98  --lt_threshold                          2000
% 3.75/0.98  --clause_weak_htbl                      true
% 3.75/0.98  --gc_record_bc_elim                     false
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing Options
% 3.75/0.98  
% 3.75/0.98  --preprocessing_flag                    true
% 3.75/0.98  --time_out_prep_mult                    0.1
% 3.75/0.98  --splitting_mode                        input
% 3.75/0.98  --splitting_grd                         true
% 3.75/0.98  --splitting_cvd                         false
% 3.75/0.98  --splitting_cvd_svl                     false
% 3.75/0.98  --splitting_nvd                         32
% 3.75/0.98  --sub_typing                            true
% 3.75/0.98  --prep_gs_sim                           true
% 3.75/0.98  --prep_unflatten                        true
% 3.75/0.98  --prep_res_sim                          true
% 3.75/0.98  --prep_upred                            true
% 3.75/0.98  --prep_sem_filter                       exhaustive
% 3.75/0.98  --prep_sem_filter_out                   false
% 3.75/0.98  --pred_elim                             true
% 3.75/0.98  --res_sim_input                         true
% 3.75/0.98  --eq_ax_congr_red                       true
% 3.75/0.98  --pure_diseq_elim                       true
% 3.75/0.98  --brand_transform                       false
% 3.75/0.98  --non_eq_to_eq                          false
% 3.75/0.98  --prep_def_merge                        true
% 3.75/0.98  --prep_def_merge_prop_impl              false
% 3.75/0.98  --prep_def_merge_mbd                    true
% 3.75/0.98  --prep_def_merge_tr_red                 false
% 3.75/0.98  --prep_def_merge_tr_cl                  false
% 3.75/0.98  --smt_preprocessing                     true
% 3.75/0.98  --smt_ac_axioms                         fast
% 3.75/0.98  --preprocessed_out                      false
% 3.75/0.98  --preprocessed_stats                    false
% 3.75/0.98  
% 3.75/0.98  ------ Abstraction refinement Options
% 3.75/0.98  
% 3.75/0.98  --abstr_ref                             []
% 3.75/0.98  --abstr_ref_prep                        false
% 3.75/0.98  --abstr_ref_until_sat                   false
% 3.75/0.98  --abstr_ref_sig_restrict                funpre
% 3.75/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.75/0.98  --abstr_ref_under                       []
% 3.75/0.98  
% 3.75/0.98  ------ SAT Options
% 3.75/0.98  
% 3.75/0.98  --sat_mode                              false
% 3.75/0.98  --sat_fm_restart_options                ""
% 3.75/0.98  --sat_gr_def                            false
% 3.75/0.98  --sat_epr_types                         true
% 3.75/0.98  --sat_non_cyclic_types                  false
% 3.75/0.98  --sat_finite_models                     false
% 3.75/0.98  --sat_fm_lemmas                         false
% 3.75/0.98  --sat_fm_prep                           false
% 3.75/0.98  --sat_fm_uc_incr                        true
% 3.75/0.98  --sat_out_model                         small
% 3.75/0.98  --sat_out_clauses                       false
% 3.75/0.98  
% 3.75/0.98  ------ QBF Options
% 3.75/0.98  
% 3.75/0.98  --qbf_mode                              false
% 3.75/0.98  --qbf_elim_univ                         false
% 3.75/0.98  --qbf_dom_inst                          none
% 3.75/0.98  --qbf_dom_pre_inst                      false
% 3.75/0.98  --qbf_sk_in                             false
% 3.75/0.98  --qbf_pred_elim                         true
% 3.75/0.98  --qbf_split                             512
% 3.75/0.98  
% 3.75/0.98  ------ BMC1 Options
% 3.75/0.98  
% 3.75/0.98  --bmc1_incremental                      false
% 3.75/0.98  --bmc1_axioms                           reachable_all
% 3.75/0.98  --bmc1_min_bound                        0
% 3.75/0.98  --bmc1_max_bound                        -1
% 3.75/0.98  --bmc1_max_bound_default                -1
% 3.75/0.98  --bmc1_symbol_reachability              true
% 3.75/0.98  --bmc1_property_lemmas                  false
% 3.75/0.98  --bmc1_k_induction                      false
% 3.75/0.98  --bmc1_non_equiv_states                 false
% 3.75/0.98  --bmc1_deadlock                         false
% 3.75/0.98  --bmc1_ucm                              false
% 3.75/0.98  --bmc1_add_unsat_core                   none
% 3.75/0.98  --bmc1_unsat_core_children              false
% 3.75/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.75/0.98  --bmc1_out_stat                         full
% 3.75/0.98  --bmc1_ground_init                      false
% 3.75/0.98  --bmc1_pre_inst_next_state              false
% 3.75/0.98  --bmc1_pre_inst_state                   false
% 3.75/0.98  --bmc1_pre_inst_reach_state             false
% 3.75/0.98  --bmc1_out_unsat_core                   false
% 3.75/0.98  --bmc1_aig_witness_out                  false
% 3.75/0.98  --bmc1_verbose                          false
% 3.75/0.98  --bmc1_dump_clauses_tptp                false
% 3.75/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.75/0.98  --bmc1_dump_file                        -
% 3.75/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.75/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.75/0.98  --bmc1_ucm_extend_mode                  1
% 3.75/0.98  --bmc1_ucm_init_mode                    2
% 3.75/0.98  --bmc1_ucm_cone_mode                    none
% 3.75/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.75/0.98  --bmc1_ucm_relax_model                  4
% 3.75/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.75/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.75/0.98  --bmc1_ucm_layered_model                none
% 3.75/0.98  --bmc1_ucm_max_lemma_size               10
% 3.75/0.98  
% 3.75/0.98  ------ AIG Options
% 3.75/0.98  
% 3.75/0.98  --aig_mode                              false
% 3.75/0.98  
% 3.75/0.98  ------ Instantiation Options
% 3.75/0.98  
% 3.75/0.98  --instantiation_flag                    true
% 3.75/0.98  --inst_sos_flag                         true
% 3.75/0.98  --inst_sos_phase                        true
% 3.75/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.75/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.75/0.98  --inst_lit_sel_side                     num_symb
% 3.75/0.98  --inst_solver_per_active                1400
% 3.75/0.98  --inst_solver_calls_frac                1.
% 3.75/0.98  --inst_passive_queue_type               priority_queues
% 3.75/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.75/0.98  --inst_passive_queues_freq              [25;2]
% 3.75/0.98  --inst_dismatching                      true
% 3.75/0.98  --inst_eager_unprocessed_to_passive     true
% 3.75/0.98  --inst_prop_sim_given                   true
% 3.75/0.98  --inst_prop_sim_new                     false
% 3.75/0.98  --inst_subs_new                         false
% 3.75/0.98  --inst_eq_res_simp                      false
% 3.75/0.98  --inst_subs_given                       false
% 3.75/0.98  --inst_orphan_elimination               true
% 3.75/0.98  --inst_learning_loop_flag               true
% 3.75/0.98  --inst_learning_start                   3000
% 3.75/0.98  --inst_learning_factor                  2
% 3.75/0.98  --inst_start_prop_sim_after_learn       3
% 3.75/0.98  --inst_sel_renew                        solver
% 3.75/0.98  --inst_lit_activity_flag                true
% 3.75/0.98  --inst_restr_to_given                   false
% 3.75/0.98  --inst_activity_threshold               500
% 3.75/0.98  --inst_out_proof                        true
% 3.75/0.98  
% 3.75/0.98  ------ Resolution Options
% 3.75/0.98  
% 3.75/0.98  --resolution_flag                       true
% 3.75/0.98  --res_lit_sel                           adaptive
% 3.75/0.98  --res_lit_sel_side                      none
% 3.75/0.98  --res_ordering                          kbo
% 3.75/0.98  --res_to_prop_solver                    active
% 3.75/0.98  --res_prop_simpl_new                    false
% 3.75/0.98  --res_prop_simpl_given                  true
% 3.75/0.98  --res_passive_queue_type                priority_queues
% 3.75/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.75/0.98  --res_passive_queues_freq               [15;5]
% 3.75/0.98  --res_forward_subs                      full
% 3.75/0.98  --res_backward_subs                     full
% 3.75/0.98  --res_forward_subs_resolution           true
% 3.75/0.98  --res_backward_subs_resolution          true
% 3.75/0.98  --res_orphan_elimination                true
% 3.75/0.98  --res_time_limit                        2.
% 3.75/0.98  --res_out_proof                         true
% 3.75/0.98  
% 3.75/0.98  ------ Superposition Options
% 3.75/0.98  
% 3.75/0.98  --superposition_flag                    true
% 3.75/0.98  --sup_passive_queue_type                priority_queues
% 3.75/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.75/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.75/0.98  --demod_completeness_check              fast
% 3.75/0.98  --demod_use_ground                      true
% 3.75/0.98  --sup_to_prop_solver                    passive
% 3.75/0.98  --sup_prop_simpl_new                    true
% 3.75/0.98  --sup_prop_simpl_given                  true
% 3.75/0.98  --sup_fun_splitting                     true
% 3.75/0.98  --sup_smt_interval                      50000
% 3.75/0.98  
% 3.75/0.98  ------ Superposition Simplification Setup
% 3.75/0.98  
% 3.75/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.75/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.75/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.75/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.75/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.75/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.75/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.75/0.98  --sup_immed_triv                        [TrivRules]
% 3.75/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.75/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.75/0.98  --sup_immed_bw_main                     []
% 3.75/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.75/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.75/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.75/0.98  --sup_input_bw                          []
% 3.75/0.98  
% 3.75/0.98  ------ Combination Options
% 3.75/0.98  
% 3.75/0.98  --comb_res_mult                         3
% 3.75/0.98  --comb_sup_mult                         2
% 3.75/0.98  --comb_inst_mult                        10
% 3.75/0.98  
% 3.75/0.98  ------ Debug Options
% 3.75/0.98  
% 3.75/0.98  --dbg_backtrace                         false
% 3.75/0.98  --dbg_dump_prop_clauses                 false
% 3.75/0.98  --dbg_dump_prop_clauses_file            -
% 3.75/0.98  --dbg_out_stat                          false
% 3.75/0.98  ------ Parsing...
% 3.75/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.75/0.98  ------ Proving...
% 3.75/0.98  ------ Problem Properties 
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  clauses                                 25
% 3.75/0.98  conjectures                             3
% 3.75/0.98  EPR                                     2
% 3.75/0.98  Horn                                    19
% 3.75/0.98  unary                                   2
% 3.75/0.98  binary                                  8
% 3.75/0.98  lits                                    83
% 3.75/0.98  lits eq                                 3
% 3.75/0.98  fd_pure                                 0
% 3.75/0.98  fd_pseudo                               0
% 3.75/0.98  fd_cond                                 0
% 3.75/0.98  fd_pseudo_cond                          1
% 3.75/0.98  AC symbols                              0
% 3.75/0.98  
% 3.75/0.98  ------ Schedule dynamic 5 is on 
% 3.75/0.98  
% 3.75/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  ------ 
% 3.75/0.98  Current options:
% 3.75/0.98  ------ 
% 3.75/0.98  
% 3.75/0.98  ------ Input Options
% 3.75/0.98  
% 3.75/0.98  --out_options                           all
% 3.75/0.98  --tptp_safe_out                         true
% 3.75/0.98  --problem_path                          ""
% 3.75/0.98  --include_path                          ""
% 3.75/0.98  --clausifier                            res/vclausify_rel
% 3.75/0.98  --clausifier_options                    ""
% 3.75/0.98  --stdin                                 false
% 3.75/0.98  --stats_out                             all
% 3.75/0.98  
% 3.75/0.98  ------ General Options
% 3.75/0.98  
% 3.75/0.98  --fof                                   false
% 3.75/0.98  --time_out_real                         305.
% 3.75/0.98  --time_out_virtual                      -1.
% 3.75/0.98  --symbol_type_check                     false
% 3.75/0.98  --clausify_out                          false
% 3.75/0.98  --sig_cnt_out                           false
% 3.75/0.98  --trig_cnt_out                          false
% 3.75/0.98  --trig_cnt_out_tolerance                1.
% 3.75/0.98  --trig_cnt_out_sk_spl                   false
% 3.75/0.98  --abstr_cl_out                          false
% 3.75/0.98  
% 3.75/0.98  ------ Global Options
% 3.75/0.98  
% 3.75/0.98  --schedule                              default
% 3.75/0.98  --add_important_lit                     false
% 3.75/0.98  --prop_solver_per_cl                    1000
% 3.75/0.98  --min_unsat_core                        false
% 3.75/0.98  --soft_assumptions                      false
% 3.75/0.98  --soft_lemma_size                       3
% 3.75/0.98  --prop_impl_unit_size                   0
% 3.75/0.98  --prop_impl_unit                        []
% 3.75/0.98  --share_sel_clauses                     true
% 3.75/0.98  --reset_solvers                         false
% 3.75/0.98  --bc_imp_inh                            [conj_cone]
% 3.75/0.98  --conj_cone_tolerance                   3.
% 3.75/0.98  --extra_neg_conj                        none
% 3.75/0.98  --large_theory_mode                     true
% 3.75/0.98  --prolific_symb_bound                   200
% 3.75/0.98  --lt_threshold                          2000
% 3.75/0.98  --clause_weak_htbl                      true
% 3.75/0.98  --gc_record_bc_elim                     false
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing Options
% 3.75/0.98  
% 3.75/0.98  --preprocessing_flag                    true
% 3.75/0.98  --time_out_prep_mult                    0.1
% 3.75/0.98  --splitting_mode                        input
% 3.75/0.98  --splitting_grd                         true
% 3.75/0.98  --splitting_cvd                         false
% 3.75/0.98  --splitting_cvd_svl                     false
% 3.75/0.98  --splitting_nvd                         32
% 3.75/0.98  --sub_typing                            true
% 3.75/0.98  --prep_gs_sim                           true
% 3.75/0.98  --prep_unflatten                        true
% 3.75/0.98  --prep_res_sim                          true
% 3.75/0.98  --prep_upred                            true
% 3.75/0.98  --prep_sem_filter                       exhaustive
% 3.75/0.98  --prep_sem_filter_out                   false
% 3.75/0.98  --pred_elim                             true
% 3.75/0.98  --res_sim_input                         true
% 3.75/0.98  --eq_ax_congr_red                       true
% 3.75/0.98  --pure_diseq_elim                       true
% 3.75/0.98  --brand_transform                       false
% 3.75/0.98  --non_eq_to_eq                          false
% 3.75/0.98  --prep_def_merge                        true
% 3.75/0.98  --prep_def_merge_prop_impl              false
% 3.75/0.98  --prep_def_merge_mbd                    true
% 3.75/0.98  --prep_def_merge_tr_red                 false
% 3.75/0.98  --prep_def_merge_tr_cl                  false
% 3.75/0.98  --smt_preprocessing                     true
% 3.75/0.98  --smt_ac_axioms                         fast
% 3.75/0.98  --preprocessed_out                      false
% 3.75/0.98  --preprocessed_stats                    false
% 3.75/0.98  
% 3.75/0.98  ------ Abstraction refinement Options
% 3.75/0.98  
% 3.75/0.98  --abstr_ref                             []
% 3.75/0.98  --abstr_ref_prep                        false
% 3.75/0.98  --abstr_ref_until_sat                   false
% 3.75/0.98  --abstr_ref_sig_restrict                funpre
% 3.75/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.75/0.98  --abstr_ref_under                       []
% 3.75/0.98  
% 3.75/0.98  ------ SAT Options
% 3.75/0.98  
% 3.75/0.98  --sat_mode                              false
% 3.75/0.98  --sat_fm_restart_options                ""
% 3.75/0.98  --sat_gr_def                            false
% 3.75/0.98  --sat_epr_types                         true
% 3.75/0.98  --sat_non_cyclic_types                  false
% 3.75/0.98  --sat_finite_models                     false
% 3.75/0.98  --sat_fm_lemmas                         false
% 3.75/0.98  --sat_fm_prep                           false
% 3.75/0.98  --sat_fm_uc_incr                        true
% 3.75/0.98  --sat_out_model                         small
% 3.75/0.98  --sat_out_clauses                       false
% 3.75/0.98  
% 3.75/0.98  ------ QBF Options
% 3.75/0.98  
% 3.75/0.98  --qbf_mode                              false
% 3.75/0.98  --qbf_elim_univ                         false
% 3.75/0.98  --qbf_dom_inst                          none
% 3.75/0.98  --qbf_dom_pre_inst                      false
% 3.75/0.98  --qbf_sk_in                             false
% 3.75/0.98  --qbf_pred_elim                         true
% 3.75/0.98  --qbf_split                             512
% 3.75/0.98  
% 3.75/0.98  ------ BMC1 Options
% 3.75/0.98  
% 3.75/0.98  --bmc1_incremental                      false
% 3.75/0.98  --bmc1_axioms                           reachable_all
% 3.75/0.98  --bmc1_min_bound                        0
% 3.75/0.98  --bmc1_max_bound                        -1
% 3.75/0.98  --bmc1_max_bound_default                -1
% 3.75/0.98  --bmc1_symbol_reachability              true
% 3.75/0.98  --bmc1_property_lemmas                  false
% 3.75/0.98  --bmc1_k_induction                      false
% 3.75/0.98  --bmc1_non_equiv_states                 false
% 3.75/0.98  --bmc1_deadlock                         false
% 3.75/0.98  --bmc1_ucm                              false
% 3.75/0.98  --bmc1_add_unsat_core                   none
% 3.75/0.98  --bmc1_unsat_core_children              false
% 3.75/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.75/0.98  --bmc1_out_stat                         full
% 3.75/0.98  --bmc1_ground_init                      false
% 3.75/0.98  --bmc1_pre_inst_next_state              false
% 3.75/0.98  --bmc1_pre_inst_state                   false
% 3.75/0.98  --bmc1_pre_inst_reach_state             false
% 3.75/0.98  --bmc1_out_unsat_core                   false
% 3.75/0.98  --bmc1_aig_witness_out                  false
% 3.75/0.98  --bmc1_verbose                          false
% 3.75/0.98  --bmc1_dump_clauses_tptp                false
% 3.75/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.75/0.98  --bmc1_dump_file                        -
% 3.75/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.75/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.75/0.98  --bmc1_ucm_extend_mode                  1
% 3.75/0.98  --bmc1_ucm_init_mode                    2
% 3.75/0.98  --bmc1_ucm_cone_mode                    none
% 3.75/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.75/0.98  --bmc1_ucm_relax_model                  4
% 3.75/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.75/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.75/0.98  --bmc1_ucm_layered_model                none
% 3.75/0.98  --bmc1_ucm_max_lemma_size               10
% 3.75/0.98  
% 3.75/0.98  ------ AIG Options
% 3.75/0.98  
% 3.75/0.98  --aig_mode                              false
% 3.75/0.98  
% 3.75/0.98  ------ Instantiation Options
% 3.75/0.98  
% 3.75/0.98  --instantiation_flag                    true
% 3.75/0.98  --inst_sos_flag                         true
% 3.75/0.98  --inst_sos_phase                        true
% 3.75/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.75/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.75/0.98  --inst_lit_sel_side                     none
% 3.75/0.98  --inst_solver_per_active                1400
% 3.75/0.98  --inst_solver_calls_frac                1.
% 3.75/0.98  --inst_passive_queue_type               priority_queues
% 3.75/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.75/0.98  --inst_passive_queues_freq              [25;2]
% 3.75/0.98  --inst_dismatching                      true
% 3.75/0.98  --inst_eager_unprocessed_to_passive     true
% 3.75/0.98  --inst_prop_sim_given                   true
% 3.75/0.98  --inst_prop_sim_new                     false
% 3.75/0.98  --inst_subs_new                         false
% 3.75/0.98  --inst_eq_res_simp                      false
% 3.75/0.98  --inst_subs_given                       false
% 3.75/0.98  --inst_orphan_elimination               true
% 3.75/0.98  --inst_learning_loop_flag               true
% 3.75/0.98  --inst_learning_start                   3000
% 3.75/0.98  --inst_learning_factor                  2
% 3.75/0.98  --inst_start_prop_sim_after_learn       3
% 3.75/0.98  --inst_sel_renew                        solver
% 3.75/0.98  --inst_lit_activity_flag                true
% 3.75/0.98  --inst_restr_to_given                   false
% 3.75/0.98  --inst_activity_threshold               500
% 3.75/0.98  --inst_out_proof                        true
% 3.75/0.98  
% 3.75/0.98  ------ Resolution Options
% 3.75/0.98  
% 3.75/0.98  --resolution_flag                       false
% 3.75/0.98  --res_lit_sel                           adaptive
% 3.75/0.98  --res_lit_sel_side                      none
% 3.75/0.98  --res_ordering                          kbo
% 3.75/0.98  --res_to_prop_solver                    active
% 3.75/0.98  --res_prop_simpl_new                    false
% 3.75/0.98  --res_prop_simpl_given                  true
% 3.75/0.98  --res_passive_queue_type                priority_queues
% 3.75/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.75/0.98  --res_passive_queues_freq               [15;5]
% 3.75/0.98  --res_forward_subs                      full
% 3.75/0.98  --res_backward_subs                     full
% 3.75/0.98  --res_forward_subs_resolution           true
% 3.75/0.98  --res_backward_subs_resolution          true
% 3.75/0.98  --res_orphan_elimination                true
% 3.75/0.98  --res_time_limit                        2.
% 3.75/0.98  --res_out_proof                         true
% 3.75/0.98  
% 3.75/0.98  ------ Superposition Options
% 3.75/0.98  
% 3.75/0.98  --superposition_flag                    true
% 3.75/0.98  --sup_passive_queue_type                priority_queues
% 3.75/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.75/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.75/0.98  --demod_completeness_check              fast
% 3.75/0.98  --demod_use_ground                      true
% 3.75/0.98  --sup_to_prop_solver                    passive
% 3.75/0.98  --sup_prop_simpl_new                    true
% 3.75/0.98  --sup_prop_simpl_given                  true
% 3.75/0.98  --sup_fun_splitting                     true
% 3.75/0.98  --sup_smt_interval                      50000
% 3.75/0.98  
% 3.75/0.98  ------ Superposition Simplification Setup
% 3.75/0.98  
% 3.75/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.75/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.75/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.75/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.75/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.75/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.75/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.75/0.98  --sup_immed_triv                        [TrivRules]
% 3.75/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.75/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.75/0.98  --sup_immed_bw_main                     []
% 3.75/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.75/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.75/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.75/0.98  --sup_input_bw                          []
% 3.75/0.98  
% 3.75/0.98  ------ Combination Options
% 3.75/0.98  
% 3.75/0.98  --comb_res_mult                         3
% 3.75/0.98  --comb_sup_mult                         2
% 3.75/0.98  --comb_inst_mult                        10
% 3.75/0.98  
% 3.75/0.98  ------ Debug Options
% 3.75/0.98  
% 3.75/0.98  --dbg_backtrace                         false
% 3.75/0.98  --dbg_dump_prop_clauses                 false
% 3.75/0.98  --dbg_dump_prop_clauses_file            -
% 3.75/0.98  --dbg_out_stat                          false
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  ------ Proving...
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  % SZS status Theorem for theBenchmark.p
% 3.75/0.98  
% 3.75/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.75/0.98  
% 3.75/0.98  fof(f13,conjecture,(
% 3.75/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f14,negated_conjecture,(
% 3.75/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.75/0.98    inference(negated_conjecture,[],[f13])).
% 3.75/0.98  
% 3.75/0.98  fof(f15,plain,(
% 3.75/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.75/0.98    inference(pure_predicate_removal,[],[f14])).
% 3.75/0.98  
% 3.75/0.98  fof(f30,plain,(
% 3.75/0.98    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 3.75/0.98    inference(ennf_transformation,[],[f15])).
% 3.75/0.98  
% 3.75/0.98  fof(f31,plain,(
% 3.75/0.98    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 3.75/0.98    inference(flattening,[],[f30])).
% 3.75/0.98  
% 3.75/0.98  fof(f52,plain,(
% 3.75/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK8 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(sK8,k7_relset_1(X0,X1,X3,X2)))) )),
% 3.75/0.98    introduced(choice_axiom,[])).
% 3.75/0.98  
% 3.75/0.98  fof(f51,plain,(
% 3.75/0.98    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK7,X5) != X4 | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,sK4)) & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_1(sK7))),
% 3.75/0.98    introduced(choice_axiom,[])).
% 3.75/0.98  
% 3.75/0.98  fof(f53,plain,(
% 3.75/0.98    (! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,sK4)) & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_1(sK7)),
% 3.75/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f31,f52,f51])).
% 3.75/0.98  
% 3.75/0.98  fof(f81,plain,(
% 3.75/0.98    ( ! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,sK4)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f53])).
% 3.75/0.98  
% 3.75/0.98  fof(f12,axiom,(
% 3.75/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 3.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f29,plain,(
% 3.75/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.75/0.98    inference(ennf_transformation,[],[f12])).
% 3.75/0.98  
% 3.75/0.98  fof(f47,plain,(
% 3.75/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.75/0.98    inference(nnf_transformation,[],[f29])).
% 3.75/0.98  
% 3.75/0.98  fof(f48,plain,(
% 3.75/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.75/0.98    inference(rectify,[],[f47])).
% 3.75/0.98  
% 3.75/0.98  fof(f49,plain,(
% 3.75/0.98    ! [X4,X3,X2,X1] : (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) => (r2_hidden(sK3(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK3(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK3(X1,X2,X3,X4),X2)))),
% 3.75/0.98    introduced(choice_axiom,[])).
% 3.75/0.98  
% 3.75/0.98  fof(f50,plain,(
% 3.75/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & ((r2_hidden(sK3(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK3(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK3(X1,X2,X3,X4),X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.75/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f48,f49])).
% 3.75/0.98  
% 3.75/0.98  fof(f76,plain,(
% 3.75/0.98    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK3(X1,X2,X3,X4),X1) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f50])).
% 3.75/0.98  
% 3.75/0.98  fof(f79,plain,(
% 3.75/0.98    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 3.75/0.98    inference(cnf_transformation,[],[f53])).
% 3.75/0.98  
% 3.75/0.98  fof(f11,axiom,(
% 3.75/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f28,plain,(
% 3.75/0.98    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.75/0.98    inference(ennf_transformation,[],[f11])).
% 3.75/0.98  
% 3.75/0.98  fof(f73,plain,(
% 3.75/0.98    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.75/0.98    inference(cnf_transformation,[],[f28])).
% 3.75/0.98  
% 3.75/0.98  fof(f80,plain,(
% 3.75/0.98    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))),
% 3.75/0.98    inference(cnf_transformation,[],[f53])).
% 3.75/0.98  
% 3.75/0.98  fof(f6,axiom,(
% 3.75/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f22,plain,(
% 3.75/0.98    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.75/0.98    inference(ennf_transformation,[],[f6])).
% 3.75/0.98  
% 3.75/0.98  fof(f41,plain,(
% 3.75/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.75/0.98    inference(nnf_transformation,[],[f22])).
% 3.75/0.98  
% 3.75/0.98  fof(f42,plain,(
% 3.75/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.75/0.98    inference(rectify,[],[f41])).
% 3.75/0.98  
% 3.75/0.98  fof(f43,plain,(
% 3.75/0.98    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))))),
% 3.75/0.98    introduced(choice_axiom,[])).
% 3.75/0.98  
% 3.75/0.98  fof(f44,plain,(
% 3.75/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.75/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).
% 3.75/0.98  
% 3.75/0.98  fof(f63,plain,(
% 3.75/0.98    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f44])).
% 3.75/0.98  
% 3.75/0.98  fof(f1,axiom,(
% 3.75/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f32,plain,(
% 3.75/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.75/0.98    inference(nnf_transformation,[],[f1])).
% 3.75/0.98  
% 3.75/0.98  fof(f33,plain,(
% 3.75/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.75/0.98    inference(rectify,[],[f32])).
% 3.75/0.98  
% 3.75/0.98  fof(f34,plain,(
% 3.75/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.75/0.98    introduced(choice_axiom,[])).
% 3.75/0.98  
% 3.75/0.98  fof(f35,plain,(
% 3.75/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.75/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 3.75/0.98  
% 3.75/0.98  fof(f54,plain,(
% 3.75/0.98    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f35])).
% 3.75/0.98  
% 3.75/0.98  fof(f65,plain,(
% 3.75/0.98    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f44])).
% 3.75/0.98  
% 3.75/0.98  fof(f9,axiom,(
% 3.75/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f16,plain,(
% 3.75/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.75/0.98    inference(pure_predicate_removal,[],[f9])).
% 3.75/0.98  
% 3.75/0.98  fof(f26,plain,(
% 3.75/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.75/0.98    inference(ennf_transformation,[],[f16])).
% 3.75/0.98  
% 3.75/0.98  fof(f71,plain,(
% 3.75/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.75/0.98    inference(cnf_transformation,[],[f26])).
% 3.75/0.98  
% 3.75/0.98  fof(f5,axiom,(
% 3.75/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f21,plain,(
% 3.75/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.75/0.98    inference(ennf_transformation,[],[f5])).
% 3.75/0.98  
% 3.75/0.98  fof(f40,plain,(
% 3.75/0.98    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.75/0.98    inference(nnf_transformation,[],[f21])).
% 3.75/0.98  
% 3.75/0.98  fof(f61,plain,(
% 3.75/0.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f40])).
% 3.75/0.98  
% 3.75/0.98  fof(f8,axiom,(
% 3.75/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f25,plain,(
% 3.75/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.75/0.98    inference(ennf_transformation,[],[f8])).
% 3.75/0.98  
% 3.75/0.98  fof(f70,plain,(
% 3.75/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.75/0.98    inference(cnf_transformation,[],[f25])).
% 3.75/0.98  
% 3.75/0.98  fof(f55,plain,(
% 3.75/0.98    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f35])).
% 3.75/0.98  
% 3.75/0.98  fof(f2,axiom,(
% 3.75/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f17,plain,(
% 3.75/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.75/0.98    inference(ennf_transformation,[],[f2])).
% 3.75/0.98  
% 3.75/0.98  fof(f36,plain,(
% 3.75/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.75/0.98    inference(nnf_transformation,[],[f17])).
% 3.75/0.98  
% 3.75/0.98  fof(f37,plain,(
% 3.75/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.75/0.98    inference(rectify,[],[f36])).
% 3.75/0.98  
% 3.75/0.98  fof(f38,plain,(
% 3.75/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.75/0.98    introduced(choice_axiom,[])).
% 3.75/0.98  
% 3.75/0.98  fof(f39,plain,(
% 3.75/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.75/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 3.75/0.98  
% 3.75/0.98  fof(f56,plain,(
% 3.75/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f39])).
% 3.75/0.98  
% 3.75/0.98  fof(f10,axiom,(
% 3.75/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 3.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f27,plain,(
% 3.75/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.75/0.98    inference(ennf_transformation,[],[f10])).
% 3.75/0.98  
% 3.75/0.98  fof(f72,plain,(
% 3.75/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.75/0.98    inference(cnf_transformation,[],[f27])).
% 3.75/0.98  
% 3.75/0.98  fof(f3,axiom,(
% 3.75/0.98    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f18,plain,(
% 3.75/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.75/0.98    inference(ennf_transformation,[],[f3])).
% 3.75/0.98  
% 3.75/0.98  fof(f19,plain,(
% 3.75/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.75/0.98    inference(flattening,[],[f18])).
% 3.75/0.98  
% 3.75/0.98  fof(f59,plain,(
% 3.75/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f19])).
% 3.75/0.98  
% 3.75/0.98  fof(f75,plain,(
% 3.75/0.98    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK3(X1,X2,X3,X4),X4),X3) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f50])).
% 3.75/0.98  
% 3.75/0.98  fof(f4,axiom,(
% 3.75/0.98    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f20,plain,(
% 3.75/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.75/0.98    inference(ennf_transformation,[],[f4])).
% 3.75/0.98  
% 3.75/0.98  fof(f60,plain,(
% 3.75/0.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f20])).
% 3.75/0.98  
% 3.75/0.98  fof(f7,axiom,(
% 3.75/0.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f23,plain,(
% 3.75/0.98    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.75/0.98    inference(ennf_transformation,[],[f7])).
% 3.75/0.98  
% 3.75/0.98  fof(f24,plain,(
% 3.75/0.98    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.75/0.98    inference(flattening,[],[f23])).
% 3.75/0.98  
% 3.75/0.98  fof(f45,plain,(
% 3.75/0.98    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.75/0.98    inference(nnf_transformation,[],[f24])).
% 3.75/0.98  
% 3.75/0.98  fof(f46,plain,(
% 3.75/0.98    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.75/0.98    inference(flattening,[],[f45])).
% 3.75/0.98  
% 3.75/0.98  fof(f68,plain,(
% 3.75/0.98    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f46])).
% 3.75/0.98  
% 3.75/0.98  fof(f78,plain,(
% 3.75/0.98    v1_funct_1(sK7)),
% 3.75/0.98    inference(cnf_transformation,[],[f53])).
% 3.75/0.98  
% 3.75/0.98  fof(f74,plain,(
% 3.75/0.98    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK3(X1,X2,X3,X4),X2) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f50])).
% 3.75/0.98  
% 3.75/0.98  cnf(c_24,negated_conjecture,
% 3.75/0.98      ( ~ m1_subset_1(X0,sK4)
% 3.75/0.98      | ~ r2_hidden(X0,sK6)
% 3.75/0.98      | k1_funct_1(sK7,X0) != sK8 ),
% 3.75/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_11779,plain,
% 3.75/0.98      ( ~ m1_subset_1(sK3(sK6,sK4,sK7,sK8),sK4)
% 3.75/0.98      | ~ r2_hidden(sK3(sK6,sK4,sK7,sK8),sK6)
% 3.75/0.98      | k1_funct_1(sK7,sK3(sK6,sK4,sK7,sK8)) != sK8 ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_24]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_21,plain,
% 3.75/0.98      ( ~ m1_subset_1(X0,X1)
% 3.75/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 3.75/0.98      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 3.75/0.98      | r2_hidden(sK3(X4,X3,X2,X0),X4)
% 3.75/0.98      | v1_xboole_0(X1)
% 3.75/0.98      | v1_xboole_0(X3)
% 3.75/0.98      | v1_xboole_0(X4) ),
% 3.75/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1636,plain,
% 3.75/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK5)))
% 3.75/0.98      | ~ m1_subset_1(X2,sK5)
% 3.75/0.98      | ~ r2_hidden(X2,k7_relset_1(X1,sK5,X0,X3))
% 3.75/0.98      | r2_hidden(sK3(X3,X1,X0,X2),X3)
% 3.75/0.98      | v1_xboole_0(X1)
% 3.75/0.98      | v1_xboole_0(X3)
% 3.75/0.98      | v1_xboole_0(sK5) ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_21]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_4837,plain,
% 3.75/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK5)))
% 3.75/0.98      | ~ m1_subset_1(sK8,sK5)
% 3.75/0.98      | r2_hidden(sK3(X2,X1,X0,sK8),X2)
% 3.75/0.98      | ~ r2_hidden(sK8,k7_relset_1(X1,sK5,X0,X2))
% 3.75/0.98      | v1_xboole_0(X1)
% 3.75/0.98      | v1_xboole_0(X2)
% 3.75/0.98      | v1_xboole_0(sK5) ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_1636]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_6506,plain,
% 3.75/0.98      ( ~ m1_subset_1(sK8,sK5)
% 3.75/0.98      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.75/0.98      | r2_hidden(sK3(X0,sK4,sK7,sK8),X0)
% 3.75/0.98      | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,X0))
% 3.75/0.98      | v1_xboole_0(X0)
% 3.75/0.98      | v1_xboole_0(sK5)
% 3.75/0.98      | v1_xboole_0(sK4) ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_4837]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_10378,plain,
% 3.75/0.98      ( ~ m1_subset_1(sK8,sK5)
% 3.75/0.98      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.75/0.98      | r2_hidden(sK3(sK6,sK4,sK7,sK8),sK6)
% 3.75/0.98      | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
% 3.75/0.98      | v1_xboole_0(sK5)
% 3.75/0.98      | v1_xboole_0(sK4)
% 3.75/0.98      | v1_xboole_0(sK6) ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_6506]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_26,negated_conjecture,
% 3.75/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.75/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1341,plain,
% 3.75/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_19,plain,
% 3.75/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.75/0.98      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.75/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1348,plain,
% 3.75/0.98      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.75/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_2631,plain,
% 3.75/0.98      ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_1341,c_1348]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_25,negated_conjecture,
% 3.75/0.98      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
% 3.75/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1342,plain,
% 3.75/0.98      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_2843,plain,
% 3.75/0.98      ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
% 3.75/0.98      inference(demodulation,[status(thm)],[c_2631,c_1342]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_12,plain,
% 3.75/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.75/0.98      | r2_hidden(sK2(X0,X2,X1),k1_relat_1(X1))
% 3.75/0.98      | ~ v1_relat_1(X1) ),
% 3.75/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1351,plain,
% 3.75/0.98      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.75/0.98      | r2_hidden(sK2(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 3.75/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1,plain,
% 3.75/0.98      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.75/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1360,plain,
% 3.75/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.75/0.98      | v1_xboole_0(X1) != iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_3679,plain,
% 3.75/0.98      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.75/0.98      | v1_relat_1(X1) != iProver_top
% 3.75/0.98      | v1_xboole_0(k1_relat_1(X1)) != iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_1351,c_1360]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_6539,plain,
% 3.75/0.98      ( v1_relat_1(sK7) != iProver_top
% 3.75/0.98      | v1_xboole_0(k1_relat_1(sK7)) != iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_2843,c_3679]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_6562,plain,
% 3.75/0.98      ( ~ v1_relat_1(sK7) | ~ v1_xboole_0(k1_relat_1(sK7)) ),
% 3.75/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_6539]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_10,plain,
% 3.75/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.75/0.98      | r2_hidden(sK2(X0,X2,X1),X2)
% 3.75/0.98      | ~ v1_relat_1(X1) ),
% 3.75/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1353,plain,
% 3.75/0.98      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.75/0.98      | r2_hidden(sK2(X0,X2,X1),X2) = iProver_top
% 3.75/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_3589,plain,
% 3.75/0.98      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.75/0.98      | v1_relat_1(X1) != iProver_top
% 3.75/0.98      | v1_xboole_0(X2) != iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_1353,c_1360]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_5982,plain,
% 3.75/0.98      ( v1_relat_1(sK7) != iProver_top
% 3.75/0.98      | v1_xboole_0(sK6) != iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_2843,c_3589]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_5993,plain,
% 3.75/0.98      ( ~ v1_relat_1(sK7) | ~ v1_xboole_0(sK6) ),
% 3.75/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_5982]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_17,plain,
% 3.75/0.98      ( v4_relat_1(X0,X1)
% 3.75/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.75/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_8,plain,
% 3.75/0.98      ( ~ v4_relat_1(X0,X1)
% 3.75/0.98      | r1_tarski(k1_relat_1(X0),X1)
% 3.75/0.98      | ~ v1_relat_1(X0) ),
% 3.75/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_320,plain,
% 3.75/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.75/0.98      | r1_tarski(k1_relat_1(X0),X1)
% 3.75/0.98      | ~ v1_relat_1(X0) ),
% 3.75/0.98      inference(resolution,[status(thm)],[c_17,c_8]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_16,plain,
% 3.75/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.75/0.98      | v1_relat_1(X0) ),
% 3.75/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_324,plain,
% 3.75/0.98      ( r1_tarski(k1_relat_1(X0),X1)
% 3.75/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.75/0.98      inference(global_propositional_subsumption,
% 3.75/0.98                [status(thm)],
% 3.75/0.98                [c_320,c_16]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_325,plain,
% 3.75/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.75/0.98      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.75/0.98      inference(renaming,[status(thm)],[c_324]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1340,plain,
% 3.75/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.75/0.98      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_325]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1954,plain,
% 3.75/0.98      ( r1_tarski(k1_relat_1(sK7),sK4) = iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_1341,c_1340]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_0,plain,
% 3.75/0.98      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.75/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1361,plain,
% 3.75/0.98      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.75/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_4,plain,
% 3.75/0.98      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.75/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1357,plain,
% 3.75/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.75/0.98      | r2_hidden(X2,X0) != iProver_top
% 3.75/0.98      | r2_hidden(X2,X1) = iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_2734,plain,
% 3.75/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.75/0.98      | r2_hidden(sK0(X0),X1) = iProver_top
% 3.75/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_1361,c_1357]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_4403,plain,
% 3.75/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.75/0.98      | v1_xboole_0(X1) != iProver_top
% 3.75/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_2734,c_1360]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_4436,plain,
% 3.75/0.98      ( v1_xboole_0(k1_relat_1(sK7)) = iProver_top
% 3.75/0.98      | v1_xboole_0(sK4) != iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_1954,c_4403]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_4439,plain,
% 3.75/0.98      ( v1_xboole_0(k1_relat_1(sK7)) | ~ v1_xboole_0(sK4) ),
% 3.75/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_4436]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_18,plain,
% 3.75/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.75/0.98      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
% 3.75/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1349,plain,
% 3.75/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.75/0.98      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_2846,plain,
% 3.75/0.98      ( m1_subset_1(k9_relat_1(sK7,X0),k1_zfmisc_1(sK5)) = iProver_top
% 3.75/0.98      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_2631,c_1349]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_29,plain,
% 3.75/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_3347,plain,
% 3.75/0.98      ( m1_subset_1(k9_relat_1(sK7,X0),k1_zfmisc_1(sK5)) = iProver_top ),
% 3.75/0.98      inference(global_propositional_subsumption,
% 3.75/0.98                [status(thm)],
% 3.75/0.98                [c_2846,c_29]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_5,plain,
% 3.75/0.98      ( m1_subset_1(X0,X1)
% 3.75/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.75/0.98      | ~ r2_hidden(X0,X2) ),
% 3.75/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1356,plain,
% 3.75/0.98      ( m1_subset_1(X0,X1) = iProver_top
% 3.75/0.98      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.75/0.98      | r2_hidden(X0,X2) != iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_3578,plain,
% 3.75/0.98      ( m1_subset_1(X0,sK5) = iProver_top
% 3.75/0.98      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_3347,c_1356]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_4003,plain,
% 3.75/0.98      ( m1_subset_1(sK8,sK5) = iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_2843,c_3578]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_4019,plain,
% 3.75/0.98      ( m1_subset_1(sK8,sK5) ),
% 3.75/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_4003]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_22,plain,
% 3.75/0.98      ( ~ m1_subset_1(X0,X1)
% 3.75/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 3.75/0.98      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 3.75/0.98      | r2_hidden(k4_tarski(sK3(X4,X3,X2,X0),X0),X2)
% 3.75/0.98      | v1_xboole_0(X1)
% 3.75/0.98      | v1_xboole_0(X3)
% 3.75/0.98      | v1_xboole_0(X4) ),
% 3.75/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1345,plain,
% 3.75/0.98      ( m1_subset_1(X0,X1) != iProver_top
% 3.75/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 3.75/0.98      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 3.75/0.98      | r2_hidden(k4_tarski(sK3(X4,X3,X2,X0),X0),X2) = iProver_top
% 3.75/0.98      | v1_xboole_0(X1) = iProver_top
% 3.75/0.98      | v1_xboole_0(X3) = iProver_top
% 3.75/0.98      | v1_xboole_0(X4) = iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_3433,plain,
% 3.75/0.98      ( m1_subset_1(X0,sK5) != iProver_top
% 3.75/0.98      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 3.75/0.98      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.75/0.98      | r2_hidden(k4_tarski(sK3(X1,sK4,sK7,X0),X0),sK7) = iProver_top
% 3.75/0.98      | v1_xboole_0(X1) = iProver_top
% 3.75/0.98      | v1_xboole_0(sK5) = iProver_top
% 3.75/0.98      | v1_xboole_0(sK4) = iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_2631,c_1345]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_30,plain,
% 3.75/0.98      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_6,plain,
% 3.75/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.75/0.98      | ~ r2_hidden(X2,X0)
% 3.75/0.98      | ~ v1_xboole_0(X1) ),
% 3.75/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1396,plain,
% 3.75/0.98      ( ~ m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(X0))
% 3.75/0.98      | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
% 3.75/0.98      | ~ v1_xboole_0(X0) ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1482,plain,
% 3.75/0.98      ( ~ m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5))
% 3.75/0.98      | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
% 3.75/0.98      | ~ v1_xboole_0(sK5) ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_1396]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1483,plain,
% 3.75/0.98      ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5)) != iProver_top
% 3.75/0.98      | r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) != iProver_top
% 3.75/0.98      | v1_xboole_0(sK5) != iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_1482]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1944,plain,
% 3.75/0.98      ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5))
% 3.75/0.98      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_18]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1945,plain,
% 3.75/0.98      ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5)) = iProver_top
% 3.75/0.98      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_1944]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_3793,plain,
% 3.75/0.98      ( v1_xboole_0(X1) = iProver_top
% 3.75/0.98      | r2_hidden(k4_tarski(sK3(X1,sK4,sK7,X0),X0),sK7) = iProver_top
% 3.75/0.98      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.75/0.98      | v1_xboole_0(sK4) = iProver_top ),
% 3.75/0.98      inference(global_propositional_subsumption,
% 3.75/0.98                [status(thm)],
% 3.75/0.98                [c_3433,c_29,c_30,c_1483,c_1945,c_3578]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_3794,plain,
% 3.75/0.98      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.75/0.98      | r2_hidden(k4_tarski(sK3(X1,sK4,sK7,X0),X0),sK7) = iProver_top
% 3.75/0.98      | v1_xboole_0(X1) = iProver_top
% 3.75/0.98      | v1_xboole_0(sK4) = iProver_top ),
% 3.75/0.98      inference(renaming,[status(thm)],[c_3793]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_14,plain,
% 3.75/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.75/0.98      | ~ v1_funct_1(X2)
% 3.75/0.98      | ~ v1_relat_1(X2)
% 3.75/0.98      | k1_funct_1(X2,X0) = X1 ),
% 3.75/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_27,negated_conjecture,
% 3.75/0.98      ( v1_funct_1(sK7) ),
% 3.75/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_419,plain,
% 3.75/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.75/0.98      | ~ v1_relat_1(X2)
% 3.75/0.98      | k1_funct_1(X2,X0) = X1
% 3.75/0.98      | sK7 != X2 ),
% 3.75/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_27]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_420,plain,
% 3.75/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),sK7)
% 3.75/0.98      | ~ v1_relat_1(sK7)
% 3.75/0.98      | k1_funct_1(sK7,X0) = X1 ),
% 3.75/0.98      inference(unflattening,[status(thm)],[c_419]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1337,plain,
% 3.75/0.98      ( k1_funct_1(sK7,X0) = X1
% 3.75/0.98      | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
% 3.75/0.98      | v1_relat_1(sK7) != iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_420]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_421,plain,
% 3.75/0.98      ( k1_funct_1(sK7,X0) = X1
% 3.75/0.98      | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
% 3.75/0.98      | v1_relat_1(sK7) != iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_420]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1416,plain,
% 3.75/0.98      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.75/0.98      | v1_relat_1(sK7) ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1519,plain,
% 3.75/0.98      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.75/0.98      | v1_relat_1(sK7) ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_1416]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1520,plain,
% 3.75/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 3.75/0.98      | v1_relat_1(sK7) = iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_1519]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1610,plain,
% 3.75/0.98      ( r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
% 3.75/0.98      | k1_funct_1(sK7,X0) = X1 ),
% 3.75/0.98      inference(global_propositional_subsumption,
% 3.75/0.98                [status(thm)],
% 3.75/0.98                [c_1337,c_29,c_421,c_1520]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1611,plain,
% 3.75/0.98      ( k1_funct_1(sK7,X0) = X1
% 3.75/0.98      | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top ),
% 3.75/0.98      inference(renaming,[status(thm)],[c_1610]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_3802,plain,
% 3.75/0.98      ( k1_funct_1(sK7,sK3(X0,sK4,sK7,X1)) = X1
% 3.75/0.98      | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
% 3.75/0.98      | v1_xboole_0(X0) = iProver_top
% 3.75/0.98      | v1_xboole_0(sK4) = iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_3794,c_1611]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_3819,plain,
% 3.75/0.98      ( k1_funct_1(sK7,sK3(sK6,sK4,sK7,sK8)) = sK8
% 3.75/0.98      | v1_xboole_0(sK4) = iProver_top
% 3.75/0.98      | v1_xboole_0(sK6) = iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_2843,c_3802]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_23,plain,
% 3.75/0.98      ( ~ m1_subset_1(X0,X1)
% 3.75/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 3.75/0.98      | m1_subset_1(sK3(X4,X3,X2,X0),X3)
% 3.75/0.98      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 3.75/0.98      | v1_xboole_0(X1)
% 3.75/0.98      | v1_xboole_0(X3)
% 3.75/0.98      | v1_xboole_0(X4) ),
% 3.75/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1344,plain,
% 3.75/0.98      ( m1_subset_1(X0,X1) != iProver_top
% 3.75/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 3.75/0.98      | m1_subset_1(sK3(X4,X3,X2,X0),X3) = iProver_top
% 3.75/0.98      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 3.75/0.98      | v1_xboole_0(X1) = iProver_top
% 3.75/0.98      | v1_xboole_0(X3) = iProver_top
% 3.75/0.98      | v1_xboole_0(X4) = iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_2622,plain,
% 3.75/0.98      ( m1_subset_1(sK3(sK6,sK4,sK7,sK8),sK4) = iProver_top
% 3.75/0.98      | m1_subset_1(sK8,sK5) != iProver_top
% 3.75/0.98      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 3.75/0.98      | v1_xboole_0(sK5) = iProver_top
% 3.75/0.98      | v1_xboole_0(sK4) = iProver_top
% 3.75/0.98      | v1_xboole_0(sK6) = iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_1342,c_1344]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_3057,plain,
% 3.75/0.98      ( m1_subset_1(sK3(sK6,sK4,sK7,sK8),sK4) = iProver_top
% 3.75/0.98      | m1_subset_1(sK8,sK5) != iProver_top
% 3.75/0.98      | v1_xboole_0(sK4) = iProver_top
% 3.75/0.98      | v1_xboole_0(sK6) = iProver_top ),
% 3.75/0.98      inference(global_propositional_subsumption,
% 3.75/0.98                [status(thm)],
% 3.75/0.98                [c_2622,c_29,c_30,c_1483,c_1945]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_3059,plain,
% 3.75/0.98      ( m1_subset_1(sK3(sK6,sK4,sK7,sK8),sK4)
% 3.75/0.98      | ~ m1_subset_1(sK8,sK5)
% 3.75/0.98      | v1_xboole_0(sK4)
% 3.75/0.98      | v1_xboole_0(sK6) ),
% 3.75/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_3057]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(contradiction,plain,
% 3.75/0.98      ( $false ),
% 3.75/0.98      inference(minisat,
% 3.75/0.98                [status(thm)],
% 3.75/0.98                [c_11779,c_10378,c_6562,c_6539,c_5993,c_5982,c_4439,
% 3.75/0.98                 c_4436,c_4019,c_3819,c_3059,c_1944,c_1520,c_1519,c_1482,
% 3.75/0.98                 c_25,c_29,c_26]) ).
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.75/0.98  
% 3.75/0.98  ------                               Statistics
% 3.75/0.98  
% 3.75/0.98  ------ General
% 3.75/0.98  
% 3.75/0.98  abstr_ref_over_cycles:                  0
% 3.75/0.98  abstr_ref_under_cycles:                 0
% 3.75/0.98  gc_basic_clause_elim:                   0
% 3.75/0.98  forced_gc_time:                         0
% 3.75/0.98  parsing_time:                           0.008
% 3.75/0.98  unif_index_cands_time:                  0.
% 3.75/0.98  unif_index_add_time:                    0.
% 3.75/0.98  orderings_time:                         0.
% 3.75/0.98  out_proof_time:                         0.013
% 3.75/0.98  total_time:                             0.437
% 3.75/0.98  num_of_symbols:                         54
% 3.75/0.98  num_of_terms:                           17002
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing
% 3.75/0.98  
% 3.75/0.98  num_of_splits:                          0
% 3.75/0.98  num_of_split_atoms:                     0
% 3.75/0.98  num_of_reused_defs:                     0
% 3.75/0.98  num_eq_ax_congr_red:                    49
% 3.75/0.98  num_of_sem_filtered_clauses:            1
% 3.75/0.98  num_of_subtypes:                        0
% 3.75/0.98  monotx_restored_types:                  0
% 3.75/0.98  sat_num_of_epr_types:                   0
% 3.75/0.98  sat_num_of_non_cyclic_types:            0
% 3.75/0.98  sat_guarded_non_collapsed_types:        0
% 3.75/0.98  num_pure_diseq_elim:                    0
% 3.75/0.98  simp_replaced_by:                       0
% 3.75/0.98  res_preprocessed:                       128
% 3.75/0.98  prep_upred:                             0
% 3.75/0.98  prep_unflattend:                        21
% 3.75/0.98  smt_new_axioms:                         0
% 3.75/0.98  pred_elim_cands:                        5
% 3.75/0.98  pred_elim:                              2
% 3.75/0.98  pred_elim_cl:                           3
% 3.75/0.98  pred_elim_cycles:                       6
% 3.75/0.98  merged_defs:                            0
% 3.75/0.98  merged_defs_ncl:                        0
% 3.75/0.98  bin_hyper_res:                          0
% 3.75/0.98  prep_cycles:                            4
% 3.75/0.98  pred_elim_time:                         0.007
% 3.75/0.98  splitting_time:                         0.
% 3.75/0.98  sem_filter_time:                        0.
% 3.75/0.98  monotx_time:                            0.001
% 3.75/0.98  subtype_inf_time:                       0.
% 3.75/0.98  
% 3.75/0.98  ------ Problem properties
% 3.75/0.98  
% 3.75/0.98  clauses:                                25
% 3.75/0.98  conjectures:                            3
% 3.75/0.98  epr:                                    2
% 3.75/0.98  horn:                                   19
% 3.75/0.98  ground:                                 2
% 3.75/0.98  unary:                                  2
% 3.75/0.98  binary:                                 8
% 3.75/0.98  lits:                                   83
% 3.75/0.98  lits_eq:                                3
% 3.75/0.98  fd_pure:                                0
% 3.75/0.98  fd_pseudo:                              0
% 3.75/0.98  fd_cond:                                0
% 3.75/0.98  fd_pseudo_cond:                         1
% 3.75/0.98  ac_symbols:                             0
% 3.75/0.98  
% 3.75/0.98  ------ Propositional Solver
% 3.75/0.98  
% 3.75/0.98  prop_solver_calls:                      32
% 3.75/0.98  prop_fast_solver_calls:                 1589
% 3.75/0.98  smt_solver_calls:                       0
% 3.75/0.98  smt_fast_solver_calls:                  0
% 3.75/0.98  prop_num_of_clauses:                    5998
% 3.75/0.98  prop_preprocess_simplified:             12222
% 3.75/0.98  prop_fo_subsumed:                       62
% 3.75/0.98  prop_solver_time:                       0.
% 3.75/0.98  smt_solver_time:                        0.
% 3.75/0.98  smt_fast_solver_time:                   0.
% 3.75/0.98  prop_fast_solver_time:                  0.
% 3.75/0.98  prop_unsat_core_time:                   0.
% 3.75/0.98  
% 3.75/0.98  ------ QBF
% 3.75/0.98  
% 3.75/0.98  qbf_q_res:                              0
% 3.75/0.98  qbf_num_tautologies:                    0
% 3.75/0.98  qbf_prep_cycles:                        0
% 3.75/0.98  
% 3.75/0.98  ------ BMC1
% 3.75/0.98  
% 3.75/0.98  bmc1_current_bound:                     -1
% 3.75/0.98  bmc1_last_solved_bound:                 -1
% 3.75/0.98  bmc1_unsat_core_size:                   -1
% 3.75/0.98  bmc1_unsat_core_parents_size:           -1
% 3.75/0.98  bmc1_merge_next_fun:                    0
% 3.75/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.75/0.98  
% 3.75/0.98  ------ Instantiation
% 3.75/0.98  
% 3.75/0.98  inst_num_of_clauses:                    1317
% 3.75/0.98  inst_num_in_passive:                    622
% 3.75/0.98  inst_num_in_active:                     672
% 3.75/0.98  inst_num_in_unprocessed:                22
% 3.75/0.98  inst_num_of_loops:                      836
% 3.75/0.98  inst_num_of_learning_restarts:          0
% 3.75/0.98  inst_num_moves_active_passive:          160
% 3.75/0.98  inst_lit_activity:                      0
% 3.75/0.98  inst_lit_activity_moves:                0
% 3.75/0.98  inst_num_tautologies:                   0
% 3.75/0.98  inst_num_prop_implied:                  0
% 3.75/0.98  inst_num_existing_simplified:           0
% 3.75/0.98  inst_num_eq_res_simplified:             0
% 3.75/0.98  inst_num_child_elim:                    0
% 3.75/0.98  inst_num_of_dismatching_blockings:      717
% 3.75/0.98  inst_num_of_non_proper_insts:           1304
% 3.75/0.98  inst_num_of_duplicates:                 0
% 3.75/0.98  inst_inst_num_from_inst_to_res:         0
% 3.75/0.98  inst_dismatching_checking_time:         0.
% 3.75/0.98  
% 3.75/0.98  ------ Resolution
% 3.75/0.98  
% 3.75/0.98  res_num_of_clauses:                     0
% 3.75/0.98  res_num_in_passive:                     0
% 3.75/0.98  res_num_in_active:                      0
% 3.75/0.98  res_num_of_loops:                       132
% 3.75/0.98  res_forward_subset_subsumed:            54
% 3.75/0.98  res_backward_subset_subsumed:           0
% 3.75/0.98  res_forward_subsumed:                   0
% 3.75/0.98  res_backward_subsumed:                  0
% 3.75/0.98  res_forward_subsumption_resolution:     0
% 3.75/0.98  res_backward_subsumption_resolution:    0
% 3.75/0.98  res_clause_to_clause_subsumption:       2428
% 3.75/0.98  res_orphan_elimination:                 0
% 3.75/0.98  res_tautology_del:                      88
% 3.75/0.98  res_num_eq_res_simplified:              0
% 3.75/0.98  res_num_sel_changes:                    0
% 3.75/0.98  res_moves_from_active_to_pass:          0
% 3.75/0.98  
% 3.75/0.98  ------ Superposition
% 3.75/0.98  
% 3.75/0.98  sup_time_total:                         0.
% 3.75/0.98  sup_time_generating:                    0.
% 3.75/0.98  sup_time_sim_full:                      0.
% 3.75/0.98  sup_time_sim_immed:                     0.
% 3.75/0.98  
% 3.75/0.98  sup_num_of_clauses:                     551
% 3.75/0.98  sup_num_in_active:                      153
% 3.75/0.98  sup_num_in_passive:                     398
% 3.75/0.98  sup_num_of_loops:                       166
% 3.75/0.98  sup_fw_superposition:                   373
% 3.75/0.98  sup_bw_superposition:                   379
% 3.75/0.98  sup_immediate_simplified:               155
% 3.75/0.98  sup_given_eliminated:                   1
% 3.75/0.98  comparisons_done:                       0
% 3.75/0.98  comparisons_avoided:                    0
% 3.75/0.98  
% 3.75/0.98  ------ Simplifications
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  sim_fw_subset_subsumed:                 60
% 3.75/0.98  sim_bw_subset_subsumed:                 5
% 3.75/0.98  sim_fw_subsumed:                        57
% 3.75/0.98  sim_bw_subsumed:                        34
% 3.75/0.98  sim_fw_subsumption_res:                 0
% 3.75/0.98  sim_bw_subsumption_res:                 0
% 3.75/0.98  sim_tautology_del:                      16
% 3.75/0.98  sim_eq_tautology_del:                   3
% 3.75/0.98  sim_eq_res_simp:                        0
% 3.75/0.98  sim_fw_demodulated:                     1
% 3.75/0.98  sim_bw_demodulated:                     2
% 3.75/0.98  sim_light_normalised:                   17
% 3.75/0.98  sim_joinable_taut:                      0
% 3.75/0.98  sim_joinable_simp:                      0
% 3.75/0.98  sim_ac_normalised:                      0
% 3.75/0.98  sim_smt_subsumption:                    0
% 3.75/0.98  
%------------------------------------------------------------------------------
