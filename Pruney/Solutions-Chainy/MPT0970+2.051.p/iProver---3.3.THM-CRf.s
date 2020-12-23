%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:55 EST 2020

% Result     : Theorem 15.19s
% Output     : CNFRefutation 15.19s
% Verified   : 
% Statistics : Number of formulae       :  328 (13163 expanded)
%              Number of clauses        :  256 (4684 expanded)
%              Number of leaves         :   22 (3263 expanded)
%              Depth                    :   47
%              Number of atoms          :  984 (63222 expanded)
%              Number of equality atoms :  589 (22192 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f42,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK7(X3)) = X3
        & r2_hidden(sK7(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(X0,X1,X2) != X1
        & ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X2,X4) = X3
                & r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(sK4,sK5,sK6) != sK5
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK6,X4) = X3
              & r2_hidden(X4,sK4) )
          | ~ r2_hidden(X3,sK5) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK6,sK4,sK5)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( k2_relset_1(sK4,sK5,sK6) != sK5
    & ! [X3] :
        ( ( k1_funct_1(sK6,sK7(X3)) = X3
          & r2_hidden(sK7(X3),sK4) )
        | ~ r2_hidden(X3,sK5) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK6,sK4,sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f26,f42,f41])).

fof(f74,plain,(
    ! [X3] :
      ( k1_funct_1(sK6,sK7(X3)) = X3
      | ~ r2_hidden(X3,sK5) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f31])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f49])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f38,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
              ( k1_funct_1(X0,X3) != sK1(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK1(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK1(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
                  & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X5)) = X5
                    & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f38,f37,f36])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
      | r2_hidden(sK1(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f72,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f75,plain,(
    k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f56,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f80,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f57,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f78,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f79,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK1(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f71,plain,(
    v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f73,plain,(
    ! [X3] :
      ( r2_hidden(sK7(X3),sK4)
      | ~ r2_hidden(X3,sK5) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f55,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f81,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | k1_funct_1(X0,X3) != sK1(X0,X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(sK1(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1315,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | k1_funct_1(sK6,sK7(X0)) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1311,plain,
    ( k1_funct_1(sK6,sK7(X0)) = X0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1709,plain,
    ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1315,c_1311])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1314,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1985,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1315,c_1314])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1313,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1538,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1313])).

cnf(c_2149,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1985,c_1538])).

cnf(c_2207,plain,
    ( k1_funct_1(sK6,sK7(sK0(sK5,k1_xboole_0))) = sK0(sK5,k1_xboole_0)
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1709,c_2149])).

cnf(c_12,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_659,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
    | k2_relat_1(X0) = X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_31])).

cnf(c_660,plain,
    ( r2_hidden(sK1(sK6,X0),X0)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
    | k2_relat_1(sK6) = X0 ),
    inference(unflattening,[status(thm)],[c_659])).

cnf(c_1306,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_660])).

cnf(c_661,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_660])).

cnf(c_997,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1396,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) = k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_997])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_398,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(X0)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_29])).

cnf(c_399,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_1391,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_399])).

cnf(c_1510,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK4,sK5))
    | v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1391])).

cnf(c_1511,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1510])).

cnf(c_10,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1579,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1580,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1579])).

cnf(c_2978,plain,
    ( r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | k2_relat_1(sK6) = X0
    | k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1306,c_661,c_1396,c_1511,c_1580])).

cnf(c_2979,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_2978])).

cnf(c_2982,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2979,c_1314])).

cnf(c_6546,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
    | k2_relat_1(sK6) = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2982,c_1538])).

cnf(c_6694,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k1_funct_1(sK6,sK7(sK0(sK5,k1_xboole_0))) = sK0(sK5,k1_xboole_0)
    | k2_relat_1(sK6) = sK5 ),
    inference(superposition,[status(thm)],[c_2207,c_6546])).

cnf(c_26,negated_conjecture,
    ( k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_464,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_29])).

cnf(c_465,plain,
    ( k2_relset_1(X0,X1,sK6) = k2_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_1364,plain,
    ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(equality_resolution,[status(thm)],[c_465])).

cnf(c_1499,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_997])).

cnf(c_998,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1495,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_998])).

cnf(c_1558,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1495])).

cnf(c_1697,plain,
    ( k2_relat_1(sK6) != sK5
    | sK5 = k2_relat_1(sK6)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1558])).

cnf(c_1427,plain,
    ( k2_relset_1(sK4,sK5,sK6) != X0
    | k2_relset_1(sK4,sK5,sK6) = sK5
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_998])).

cnf(c_1835,plain,
    ( k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6)
    | k2_relset_1(sK4,sK5,sK6) = sK5
    | sK5 != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1427])).

cnf(c_14783,plain,
    ( k1_funct_1(sK6,sK7(sK0(sK5,k1_xboole_0))) = sK0(sK5,k1_xboole_0)
    | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6694,c_26,c_1364,c_1499,c_1697,c_1835])).

cnf(c_14784,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k1_funct_1(sK6,sK7(sK0(sK5,k1_xboole_0))) = sK0(sK5,k1_xboole_0) ),
    inference(renaming,[status(thm)],[c_14783])).

cnf(c_17,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_9,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_325,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_17,c_9])).

cnf(c_413,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_325,c_29])).

cnf(c_414,plain,
    ( r1_tarski(k2_relat_1(sK6),X0)
    | ~ v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_1308,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | r1_tarski(k2_relat_1(sK6),X1) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_414])).

cnf(c_1644,plain,
    ( v1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_399,c_1396,c_1510,c_1579])).

cnf(c_1656,plain,
    ( r1_tarski(k2_relat_1(sK6),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1644,c_414])).

cnf(c_1677,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | r1_tarski(k2_relat_1(sK6),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1656])).

cnf(c_3741,plain,
    ( r1_tarski(k2_relat_1(sK6),X1) = iProver_top
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1308,c_1677])).

cnf(c_3742,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | r1_tarski(k2_relat_1(sK6),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_3741])).

cnf(c_3747,plain,
    ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3742])).

cnf(c_2146,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | r1_tarski(X3,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1985,c_1314])).

cnf(c_16392,plain,
    ( r2_hidden(sK0(k2_relat_1(sK6),X0),X1) = iProver_top
    | r1_tarski(k2_relat_1(sK6),X0) = iProver_top
    | r1_tarski(sK5,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3747,c_2146])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1316,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_18001,plain,
    ( r1_tarski(k2_relat_1(sK6),X0) = iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16392,c_1316])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_692,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X0)) = X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_31])).

cnf(c_693,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK3(sK6,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_692])).

cnf(c_1304,plain,
    ( k1_funct_1(sK6,sK3(sK6,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_693])).

cnf(c_694,plain,
    ( k1_funct_1(sK6,sK3(sK6,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_693])).

cnf(c_2450,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | k1_funct_1(sK6,sK3(sK6,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1304,c_694,c_1396,c_1511,c_1580])).

cnf(c_2451,plain,
    ( k1_funct_1(sK6,sK3(sK6,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2450])).

cnf(c_2454,plain,
    ( k1_funct_1(sK6,sK3(sK6,sK0(k2_relat_1(sK6),X0))) = sK0(k2_relat_1(sK6),X0)
    | r1_tarski(k2_relat_1(sK6),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1315,c_2451])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_707,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_31])).

cnf(c_708,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_707])).

cnf(c_1303,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_708])).

cnf(c_1655,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1644,c_708])).

cnf(c_1680,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1655])).

cnf(c_2212,plain,
    ( r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1303,c_1680])).

cnf(c_2213,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2212])).

cnf(c_2216,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),X1) = iProver_top
    | r1_tarski(k2_relat_1(sK6),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2213,c_1314])).

cnf(c_2798,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r1_tarski(k2_relat_1(sK6),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2216,c_1538])).

cnf(c_2816,plain,
    ( k1_funct_1(sK6,sK3(sK6,sK0(k2_relat_1(sK6),k1_xboole_0))) = sK0(k2_relat_1(sK6),k1_xboole_0)
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2454,c_2798])).

cnf(c_11754,plain,
    ( k1_funct_1(sK6,sK3(sK6,sK0(k2_relat_1(sK6),k1_xboole_0))) = sK0(k2_relat_1(sK6),k1_xboole_0)
    | r1_tarski(k1_relat_1(sK6),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1315,c_2816])).

cnf(c_13,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK1(X0,X1),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_641,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK1(X0,X1),X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_31])).

cnf(c_642,plain,
    ( r2_hidden(sK2(sK6,X0),k1_relat_1(sK6))
    | r2_hidden(sK1(sK6,X0),X0)
    | ~ v1_relat_1(sK6)
    | k2_relat_1(sK6) = X0 ),
    inference(unflattening,[status(thm)],[c_641])).

cnf(c_1307,plain,
    ( k2_relat_1(sK6) = X0
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(c_1657,plain,
    ( r2_hidden(sK2(sK6,X0),k1_relat_1(sK6))
    | r2_hidden(sK1(sK6,X0),X0)
    | k2_relat_1(sK6) = X0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1644,c_642])).

cnf(c_1674,plain,
    ( k2_relat_1(sK6) = X0
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1657])).

cnf(c_3244,plain,
    ( r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | k2_relat_1(sK6) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1307,c_1674])).

cnf(c_3245,plain,
    ( k2_relat_1(sK6) = X0
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_3244])).

cnf(c_3255,plain,
    ( k2_relat_1(sK6) = X0
    | r2_hidden(sK2(sK6,X0),X1) = iProver_top
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK6),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3245,c_1314])).

cnf(c_6159,plain,
    ( k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK6),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3255,c_1538])).

cnf(c_6191,plain,
    ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
    | k2_relat_1(sK6) = sK5
    | r1_tarski(k1_relat_1(sK6),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6159,c_1311])).

cnf(c_1431,plain,
    ( sK5 != X0
    | sK5 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_998])).

cnf(c_1498,plain,
    ( sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_1431])).

cnf(c_999,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_473,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_29])).

cnf(c_474,plain,
    ( k1_relset_1(X0,X1,sK6) = k1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_473])).

cnf(c_1721,plain,
    ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
    inference(resolution,[status(thm)],[c_474,c_997])).

cnf(c_2645,plain,
    ( r1_tarski(k1_relset_1(sK4,sK5,sK6),X0)
    | ~ r1_tarski(k1_relat_1(sK6),X0) ),
    inference(resolution,[status(thm)],[c_999,c_1721])).

cnf(c_2646,plain,
    ( r1_tarski(k1_relset_1(sK4,sK5,sK6),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK6),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2645])).

cnf(c_2648,plain,
    ( r1_tarski(k1_relset_1(sK4,sK5,sK6),k1_xboole_0) = iProver_top
    | r1_tarski(k1_relat_1(sK6),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2646])).

cnf(c_2933,plain,
    ( k2_relat_1(sK6) != X0
    | sK5 != X0
    | sK5 = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1495])).

cnf(c_2934,plain,
    ( k2_relat_1(sK6) != k1_xboole_0
    | sK5 = k2_relat_1(sK6)
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2933])).

cnf(c_3254,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r2_hidden(sK2(sK6,k1_xboole_0),k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3245,c_1538])).

cnf(c_3303,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r2_hidden(sK2(sK6,k1_xboole_0),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK6),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3254,c_1314])).

cnf(c_3315,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK6),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3303,c_1538])).

cnf(c_3336,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_998,c_997])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_428,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_29])).

cnf(c_429,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | k1_relset_1(X0,X1,sK6) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_779,plain,
    ( k1_relset_1(X0,X1,sK6) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK6 != sK6
    | sK5 != X1
    | sK4 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_429])).

cnf(c_780,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_779])).

cnf(c_848,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | k1_xboole_0 = sK5 ),
    inference(equality_resolution_simp,[status(thm)],[c_780])).

cnf(c_5670,plain,
    ( sK4 = k1_relset_1(sK4,sK5,sK6)
    | k1_xboole_0 = sK5 ),
    inference(resolution,[status(thm)],[c_3336,c_848])).

cnf(c_2347,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,X1)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_999])).

cnf(c_5719,plain,
    ( ~ r1_tarski(k1_relset_1(sK4,sK5,sK6),X0)
    | r1_tarski(sK4,X0)
    | sK4 != k1_relset_1(sK4,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_2347])).

cnf(c_5720,plain,
    ( sK4 != k1_relset_1(sK4,sK5,sK6)
    | r1_tarski(k1_relset_1(sK4,sK5,sK6),X0) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5719])).

cnf(c_5722,plain,
    ( sK4 != k1_relset_1(sK4,sK5,sK6)
    | r1_tarski(k1_relset_1(sK4,sK5,sK6),k1_xboole_0) != iProver_top
    | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5720])).

cnf(c_28,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(sK7(X0),sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1310,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK7(X0),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1986,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK7(X0),X1) = iProver_top
    | r1_tarski(sK4,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1310,c_1314])).

cnf(c_2281,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1986,c_1538])).

cnf(c_6190,plain,
    ( k2_relat_1(sK6) = sK5
    | r1_tarski(k1_relat_1(sK6),k1_xboole_0) != iProver_top
    | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6159,c_2281])).

cnf(c_6344,plain,
    ( r1_tarski(k1_relat_1(sK6),k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6191,c_26,c_1364,c_1498,c_1499,c_1697,c_1835,c_2648,c_2934,c_3315,c_5670,c_5722,c_6190])).

cnf(c_11784,plain,
    ( k1_funct_1(sK6,sK3(sK6,sK0(k2_relat_1(sK6),k1_xboole_0))) = sK0(k2_relat_1(sK6),k1_xboole_0)
    | r1_tarski(k1_relat_1(sK6),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_11754])).

cnf(c_11813,plain,
    ( k1_funct_1(sK6,sK3(sK6,sK0(k2_relat_1(sK6),k1_xboole_0))) = sK0(k2_relat_1(sK6),k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11754,c_26,c_1364,c_1498,c_1499,c_1697,c_1835,c_2648,c_2934,c_3315,c_5670,c_5722,c_6190,c_11784])).

cnf(c_2147,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k2_zfmisc_1(sK0(X0,X1),X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1985,c_1313])).

cnf(c_2575,plain,
    ( k1_funct_1(sK6,sK3(sK6,sK0(k2_relat_1(sK6),k2_zfmisc_1(sK0(k2_relat_1(sK6),X0),X1)))) = sK0(k2_relat_1(sK6),k2_zfmisc_1(sK0(k2_relat_1(sK6),X0),X1))
    | r1_tarski(k2_relat_1(sK6),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2454,c_2147])).

cnf(c_2796,plain,
    ( k1_funct_1(sK6,sK7(k1_funct_1(sK6,X0))) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r1_tarski(k2_relat_1(sK6),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2216,c_1311])).

cnf(c_1693,plain,
    ( r1_tarski(k2_relat_1(sK6),sK5)
    | ~ v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_414])).

cnf(c_1694,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | r1_tarski(k2_relat_1(sK6),sK5) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1693])).

cnf(c_4287,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | k1_funct_1(sK6,sK7(k1_funct_1(sK6,X0))) = k1_funct_1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2796,c_1396,c_1511,c_1580,c_1694])).

cnf(c_4288,plain,
    ( k1_funct_1(sK6,sK7(k1_funct_1(sK6,X0))) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4287])).

cnf(c_4293,plain,
    ( k1_funct_1(sK6,sK7(k1_funct_1(sK6,sK0(k1_relat_1(sK6),X0)))) = k1_funct_1(sK6,sK0(k1_relat_1(sK6),X0))
    | r1_tarski(k1_relat_1(sK6),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1315,c_4288])).

cnf(c_6348,plain,
    ( k1_funct_1(sK6,sK7(k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0)))) = k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_4293,c_6344])).

cnf(c_3309,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK6),k2_zfmisc_1(sK2(sK6,k1_xboole_0),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3303,c_1313])).

cnf(c_4330,plain,
    ( k1_funct_1(sK6,sK7(k1_funct_1(sK6,sK0(k1_relat_1(sK6),k2_zfmisc_1(sK2(sK6,k1_xboole_0),X0))))) = k1_funct_1(sK6,sK0(k1_relat_1(sK6),k2_zfmisc_1(sK2(sK6,k1_xboole_0),X0)))
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4293,c_3309])).

cnf(c_23303,plain,
    ( k1_funct_1(sK6,sK0(k1_relat_1(sK6),k2_zfmisc_1(sK2(sK6,k1_xboole_0),k1_xboole_0))) = k1_funct_1(sK6,sK7(k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0))))
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_4330])).

cnf(c_23380,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r2_hidden(k1_funct_1(sK6,sK7(k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0)))),X0) = iProver_top
    | r2_hidden(sK0(k1_relat_1(sK6),k2_zfmisc_1(sK2(sK6,k1_xboole_0),k1_xboole_0)),k1_relat_1(sK6)) != iProver_top
    | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_23303,c_2216])).

cnf(c_25033,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r2_hidden(k1_funct_1(sK6,sK7(k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0)))),X0) = iProver_top
    | r2_hidden(sK0(k1_relat_1(sK6),k1_xboole_0),k1_relat_1(sK6)) != iProver_top
    | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_23380])).

cnf(c_4276,plain,
    ( r2_hidden(sK0(k1_relat_1(sK6),X0),k1_relat_1(sK6))
    | r1_tarski(k1_relat_1(sK6),X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4277,plain,
    ( r2_hidden(sK0(k1_relat_1(sK6),X0),k1_relat_1(sK6)) = iProver_top
    | r1_tarski(k1_relat_1(sK6),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4276])).

cnf(c_4279,plain,
    ( r2_hidden(sK0(k1_relat_1(sK6),k1_xboole_0),k1_relat_1(sK6)) = iProver_top
    | r1_tarski(k1_relat_1(sK6),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4277])).

cnf(c_25220,plain,
    ( r2_hidden(k1_funct_1(sK6,sK7(k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0)))),X0) = iProver_top
    | k2_relat_1(sK6) = k1_xboole_0
    | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25033,c_26,c_1364,c_1498,c_1499,c_1697,c_1835,c_2648,c_2934,c_3315,c_4279,c_5670,c_5722,c_6190])).

cnf(c_25221,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r2_hidden(k1_funct_1(sK6,sK7(k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0)))),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_25220])).

cnf(c_25226,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r1_tarski(k2_relat_1(sK6),k2_zfmisc_1(k1_funct_1(sK6,sK7(k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0)))),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_25221,c_1313])).

cnf(c_25276,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r1_tarski(k2_relat_1(sK6),k2_zfmisc_1(k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0)),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6348,c_25226])).

cnf(c_2455,plain,
    ( k1_funct_1(sK6,sK3(sK6,k1_funct_1(sK6,X0))) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2213,c_2451])).

cnf(c_6945,plain,
    ( k1_funct_1(sK6,sK3(sK6,k1_funct_1(sK6,sK0(k1_relat_1(sK6),X0)))) = k1_funct_1(sK6,sK0(k1_relat_1(sK6),X0))
    | r1_tarski(k1_relat_1(sK6),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1315,c_2455])).

cnf(c_6994,plain,
    ( k1_funct_1(sK6,sK3(sK6,k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0)))) = k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_6945,c_6344])).

cnf(c_2793,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r1_tarski(k2_relat_1(sK6),k2_zfmisc_1(k1_funct_1(sK6,X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2216,c_1313])).

cnf(c_10631,plain,
    ( r2_hidden(sK3(sK6,k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0))),k1_relat_1(sK6)) != iProver_top
    | r1_tarski(k2_relat_1(sK6),k2_zfmisc_1(k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0)),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6994,c_2793])).

cnf(c_11687,plain,
    ( r2_hidden(k1_funct_1(sK6,sK0(k1_relat_1(sK6),X0)),k2_relat_1(sK6))
    | ~ r2_hidden(sK0(k1_relat_1(sK6),X0),k1_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_708])).

cnf(c_11688,plain,
    ( r2_hidden(k1_funct_1(sK6,sK0(k1_relat_1(sK6),X0)),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK0(k1_relat_1(sK6),X0),k1_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11687])).

cnf(c_11690,plain,
    ( r2_hidden(k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0)),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK0(k1_relat_1(sK6),k1_xboole_0),k1_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11688])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_677,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_31])).

cnf(c_678,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | r2_hidden(sK3(sK6,X0),k1_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_677])).

cnf(c_17440,plain,
    ( r2_hidden(sK3(sK6,k1_funct_1(sK6,sK0(k1_relat_1(sK6),X0))),k1_relat_1(sK6))
    | ~ r2_hidden(k1_funct_1(sK6,sK0(k1_relat_1(sK6),X0)),k2_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_678])).

cnf(c_17441,plain,
    ( r2_hidden(sK3(sK6,k1_funct_1(sK6,sK0(k1_relat_1(sK6),X0))),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(k1_funct_1(sK6,sK0(k1_relat_1(sK6),X0)),k2_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17440])).

cnf(c_17443,plain,
    ( r2_hidden(sK3(sK6,k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0))),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0)),k2_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_17441])).

cnf(c_26380,plain,
    ( r1_tarski(k2_relat_1(sK6),k2_zfmisc_1(k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0)),X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25276,c_26,c_1364,c_1396,c_1498,c_1499,c_1511,c_1580,c_1697,c_1835,c_2648,c_2934,c_3315,c_4279,c_5670,c_5722,c_6190,c_10631,c_11690,c_17443])).

cnf(c_26394,plain,
    ( r1_tarski(k2_relat_1(sK6),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_26380])).

cnf(c_26556,plain,
    ( k1_funct_1(sK6,sK3(sK6,sK0(k2_relat_1(sK6),k2_zfmisc_1(sK0(k2_relat_1(sK6),k1_xboole_0),X0)))) = sK0(k2_relat_1(sK6),k2_zfmisc_1(sK0(k2_relat_1(sK6),k1_xboole_0),X0)) ),
    inference(superposition,[status(thm)],[c_2575,c_26394])).

cnf(c_26845,plain,
    ( sK0(k2_relat_1(sK6),k2_zfmisc_1(sK0(k2_relat_1(sK6),k1_xboole_0),k1_xboole_0)) = k1_funct_1(sK6,sK3(sK6,sK0(k2_relat_1(sK6),k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_3,c_26556])).

cnf(c_26868,plain,
    ( r2_hidden(k1_funct_1(sK6,sK3(sK6,sK0(k2_relat_1(sK6),k1_xboole_0))),k2_relat_1(sK6)) = iProver_top
    | r1_tarski(k2_relat_1(sK6),k2_zfmisc_1(sK0(k2_relat_1(sK6),k1_xboole_0),k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_26845,c_1315])).

cnf(c_1710,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1315,c_1538])).

cnf(c_1715,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1710])).

cnf(c_4520,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(sK6),X1)
    | k2_relat_1(sK6) != X0 ),
    inference(instantiation,[status(thm)],[c_999])).

cnf(c_4521,plain,
    ( k2_relat_1(sK6) != X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(sK6),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4520])).

cnf(c_4523,plain,
    ( k2_relat_1(sK6) != k1_xboole_0
    | r1_tarski(k2_relat_1(sK6),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4521])).

cnf(c_2148,plain,
    ( k1_funct_1(sK6,sK7(sK0(X0,X1))) = sK0(X0,X1)
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1985,c_1311])).

cnf(c_16395,plain,
    ( k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),X0))) = sK0(k2_relat_1(sK6),X0)
    | r1_tarski(k2_relat_1(sK6),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3747,c_2148])).

cnf(c_17088,plain,
    ( k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),k1_xboole_0))) = sK0(k2_relat_1(sK6),k1_xboole_0)
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16395,c_2798])).

cnf(c_17615,plain,
    ( k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),k1_xboole_0))) = sK0(k2_relat_1(sK6),k1_xboole_0)
    | r1_tarski(k1_relat_1(sK6),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1315,c_17088])).

cnf(c_17651,plain,
    ( k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),k1_xboole_0))) = sK0(k2_relat_1(sK6),k1_xboole_0)
    | r1_tarski(k1_relat_1(sK6),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_17615])).

cnf(c_17854,plain,
    ( k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),k1_xboole_0))) = sK0(k2_relat_1(sK6),k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17615,c_26,c_1364,c_1498,c_1499,c_1697,c_1835,c_2648,c_2934,c_3315,c_5670,c_5722,c_6190,c_17651])).

cnf(c_2987,plain,
    ( k1_funct_1(sK6,sK2(sK6,k1_xboole_0)) = sK1(sK6,k1_xboole_0)
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2979,c_1538])).

cnf(c_2993,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r2_hidden(sK2(sK6,k1_xboole_0),k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK1(sK6,k1_xboole_0),k2_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2987,c_2213])).

cnf(c_13029,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r2_hidden(sK1(sK6,k1_xboole_0),k2_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2993,c_3254])).

cnf(c_13033,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r2_hidden(sK1(sK6,k1_xboole_0),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13029,c_1314])).

cnf(c_13213,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r1_tarski(k2_relat_1(sK6),k2_zfmisc_1(sK1(sK6,k1_xboole_0),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13033,c_1313])).

cnf(c_17100,plain,
    ( k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),k2_zfmisc_1(sK1(sK6,k1_xboole_0),X0)))) = sK0(k2_relat_1(sK6),k2_zfmisc_1(sK1(sK6,k1_xboole_0),X0))
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_16395,c_13213])).

cnf(c_22625,plain,
    ( sK0(k2_relat_1(sK6),k2_zfmisc_1(sK1(sK6,k1_xboole_0),k1_xboole_0)) = k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),k1_xboole_0)))
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_17100])).

cnf(c_22699,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r2_hidden(k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),k1_xboole_0))),k2_relat_1(sK6)) = iProver_top
    | r1_tarski(k2_relat_1(sK6),k2_zfmisc_1(sK1(sK6,k1_xboole_0),k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_22625,c_1315])).

cnf(c_13230,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r1_tarski(k2_relat_1(sK6),k2_zfmisc_1(sK1(sK6,k1_xboole_0),k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_13213])).

cnf(c_22981,plain,
    ( r2_hidden(k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),k1_xboole_0))),k2_relat_1(sK6)) = iProver_top
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_22699,c_13230])).

cnf(c_22982,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r2_hidden(k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),k1_xboole_0))),k2_relat_1(sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_22981])).

cnf(c_22986,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r2_hidden(k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),k1_xboole_0))),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_22982,c_1314])).

cnf(c_23065,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r1_tarski(k2_relat_1(sK6),k2_zfmisc_1(k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),k1_xboole_0))),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_22986,c_1313])).

cnf(c_23107,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r1_tarski(k2_relat_1(sK6),k2_zfmisc_1(sK0(k2_relat_1(sK6),k1_xboole_0),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17854,c_23065])).

cnf(c_23117,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r1_tarski(k2_relat_1(sK6),k2_zfmisc_1(sK0(k2_relat_1(sK6),k1_xboole_0),k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_23107])).

cnf(c_27411,plain,
    ( r2_hidden(k1_funct_1(sK6,sK3(sK6,sK0(k2_relat_1(sK6),k1_xboole_0))),k2_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_26868,c_1715,c_4523,c_23117,c_26394])).

cnf(c_27416,plain,
    ( r2_hidden(k1_funct_1(sK6,sK3(sK6,sK0(k2_relat_1(sK6),k1_xboole_0))),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_27411,c_1314])).

cnf(c_27431,plain,
    ( r1_tarski(k2_relat_1(sK6),k2_zfmisc_1(k1_funct_1(sK6,sK3(sK6,sK0(k2_relat_1(sK6),k1_xboole_0))),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_27416,c_1313])).

cnf(c_27932,plain,
    ( r1_tarski(k2_relat_1(sK6),k2_zfmisc_1(sK0(k2_relat_1(sK6),k1_xboole_0),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11813,c_27431])).

cnf(c_36841,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK0(k2_relat_1(sK6),k1_xboole_0),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18001,c_27932])).

cnf(c_37249,plain,
    ( k1_funct_1(sK6,sK7(sK0(sK5,k2_zfmisc_1(sK0(k2_relat_1(sK6),k1_xboole_0),X0)))) = sK0(sK5,k2_zfmisc_1(sK0(k2_relat_1(sK6),k1_xboole_0),X0)) ),
    inference(superposition,[status(thm)],[c_1709,c_36841])).

cnf(c_44334,plain,
    ( sK0(sK5,k2_zfmisc_1(sK0(k2_relat_1(sK6),k1_xboole_0),k1_xboole_0)) = k1_funct_1(sK6,sK7(sK0(sK5,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_3,c_37249])).

cnf(c_44356,plain,
    ( r2_hidden(k1_funct_1(sK6,sK7(sK0(sK5,k1_xboole_0))),k2_zfmisc_1(sK0(k2_relat_1(sK6),k1_xboole_0),k1_xboole_0)) != iProver_top
    | r1_tarski(sK5,k2_zfmisc_1(sK0(k2_relat_1(sK6),k1_xboole_0),k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_44334,c_1316])).

cnf(c_18003,plain,
    ( r1_tarski(k2_relat_1(sK6),X0) = iProver_top
    | r1_tarski(sK5,k2_zfmisc_1(sK0(k2_relat_1(sK6),X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16392,c_1313])).

cnf(c_18024,plain,
    ( r1_tarski(k2_relat_1(sK6),k1_xboole_0) = iProver_top
    | r1_tarski(sK5,k2_zfmisc_1(sK0(k2_relat_1(sK6),k1_xboole_0),k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_18003])).

cnf(c_46161,plain,
    ( r2_hidden(k1_funct_1(sK6,sK7(sK0(sK5,k1_xboole_0))),k2_zfmisc_1(sK0(k2_relat_1(sK6),k1_xboole_0),k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_44356,c_18024,c_26394])).

cnf(c_46170,plain,
    ( r2_hidden(k1_funct_1(sK6,sK7(sK0(sK5,k1_xboole_0))),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_46161])).

cnf(c_46721,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | r2_hidden(sK0(sK5,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14784,c_46170])).

cnf(c_1714,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1710])).

cnf(c_1716,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1714])).

cnf(c_2048,plain,
    ( r2_hidden(sK1(sK6,sK5),sK5)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k2_relat_1(sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_660])).

cnf(c_2050,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k2_relat_1(sK6) = sK5
    | r2_hidden(sK1(sK6,sK5),sK5) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2048])).

cnf(c_3040,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),sK5)
    | r2_hidden(sK7(sK1(sK6,sK5)),sK4) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_3041,plain,
    ( r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3040])).

cnf(c_3039,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),sK5)
    | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_3043,plain,
    ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
    | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3039])).

cnf(c_1437,plain,
    ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
    inference(equality_resolution,[status(thm)],[c_474])).

cnf(c_4910,plain,
    ( k1_relat_1(sK6) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_848,c_1437])).

cnf(c_6346,plain,
    ( ~ r1_tarski(k1_relat_1(sK6),k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6344])).

cnf(c_10600,plain,
    ( sK1(sK6,sK5) = sK1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_997])).

cnf(c_17459,plain,
    ( sK7(sK1(sK6,sK5)) = sK7(sK1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_997])).

cnf(c_18185,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_18001,c_2798])).

cnf(c_18480,plain,
    ( r1_tarski(k1_relat_1(sK6),X0) = iProver_top
    | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1315,c_18185])).

cnf(c_18517,plain,
    ( r1_tarski(k1_relat_1(sK6),X0)
    | ~ r1_tarski(sK5,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_18480])).

cnf(c_18519,plain,
    ( r1_tarski(k1_relat_1(sK6),k1_xboole_0)
    | ~ r1_tarski(sK5,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_18517])).

cnf(c_19437,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK5,X1)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_999])).

cnf(c_19439,plain,
    ( r1_tarski(sK5,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_19437])).

cnf(c_6938,plain,
    ( sK1(sK6,sK5) != X0
    | sK1(sK6,sK5) = k1_funct_1(sK6,X1)
    | k1_funct_1(sK6,X1) != X0 ),
    inference(instantiation,[status(thm)],[c_998])).

cnf(c_10599,plain,
    ( sK1(sK6,sK5) != sK1(sK6,sK5)
    | sK1(sK6,sK5) = k1_funct_1(sK6,X0)
    | k1_funct_1(sK6,X0) != sK1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_6938])).

cnf(c_24992,plain,
    ( sK1(sK6,sK5) != sK1(sK6,sK5)
    | sK1(sK6,sK5) = k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
    | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) != sK1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_10599])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(sK1(X1,X2),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | sK1(X1,X2) != k1_funct_1(X1,X0)
    | k2_relat_1(X1) = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_722,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(sK1(X1,X2),X2)
    | ~ v1_relat_1(X1)
    | sK1(X1,X2) != k1_funct_1(X1,X0)
    | k2_relat_1(X1) = X2
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_31])).

cnf(c_723,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | ~ r2_hidden(sK1(sK6,X1),X1)
    | ~ v1_relat_1(sK6)
    | sK1(sK6,X1) != k1_funct_1(sK6,X0)
    | k2_relat_1(sK6) = X1 ),
    inference(unflattening,[status(thm)],[c_722])).

cnf(c_3045,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | ~ r2_hidden(sK1(sK6,sK5),sK5)
    | ~ v1_relat_1(sK6)
    | sK1(sK6,sK5) != k1_funct_1(sK6,X0)
    | k2_relat_1(sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_723])).

cnf(c_37996,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),sK5)
    | ~ r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | sK1(sK6,sK5) != k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
    | k2_relat_1(sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_3045])).

cnf(c_37997,plain,
    ( sK1(sK6,sK5) != k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
    | k2_relat_1(sK6) = sK5
    | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37996])).

cnf(c_1000,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_6928,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK7(sK1(sK6,sK5)),sK4)
    | X0 != sK7(sK1(sK6,sK5))
    | X1 != sK4 ),
    inference(instantiation,[status(thm)],[c_1000])).

cnf(c_17458,plain,
    ( r2_hidden(sK7(sK1(sK6,sK5)),X0)
    | ~ r2_hidden(sK7(sK1(sK6,sK5)),sK4)
    | X0 != sK4
    | sK7(sK1(sK6,sK5)) != sK7(sK1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_6928])).

cnf(c_44718,plain,
    ( r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6))
    | ~ r2_hidden(sK7(sK1(sK6,sK5)),sK4)
    | sK7(sK1(sK6,sK5)) != sK7(sK1(sK6,sK5))
    | k1_relat_1(sK6) != sK4 ),
    inference(instantiation,[status(thm)],[c_17458])).

cnf(c_44719,plain,
    ( sK7(sK1(sK6,sK5)) != sK7(sK1(sK6,sK5))
    | k1_relat_1(sK6) != sK4
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44718])).

cnf(c_47317,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_46721,c_26,c_1364,c_1396,c_1499,c_1511,c_1580,c_1697,c_1716,c_1835,c_2050,c_3041,c_3043,c_4910,c_6346,c_10600,c_17459,c_18519,c_19439,c_24992,c_37997,c_44719])).

cnf(c_47323,plain,
    ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_47317,c_2213])).

cnf(c_7354,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),X0)
    | r2_hidden(sK1(sK6,sK5),X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_13810,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),X0)
    | r2_hidden(sK1(sK6,sK5),sK5)
    | ~ r1_tarski(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_7354])).

cnf(c_17755,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6))
    | r2_hidden(sK1(sK6,sK5),sK5)
    | ~ r1_tarski(k2_relat_1(sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_13810])).

cnf(c_17756,plain,
    ( r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK1(sK6,sK5),sK5) = iProver_top
    | r1_tarski(k2_relat_1(sK6),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17755])).

cnf(c_1696,plain,
    ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6))
    | r2_hidden(sK1(sK6,sK5),sK5)
    | ~ v1_relat_1(sK6)
    | k2_relat_1(sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_642])).

cnf(c_1699,plain,
    ( k2_relat_1(sK6) = sK5
    | r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK1(sK6,sK5),sK5) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1696])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_47323,c_44719,c_37997,c_24992,c_19439,c_18519,c_17756,c_17459,c_10600,c_6346,c_4910,c_3043,c_3041,c_1835,c_1716,c_1697,c_1699,c_1694,c_1580,c_1511,c_1499,c_1396,c_1364,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:39:54 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.19/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.19/2.49  
% 15.19/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.19/2.49  
% 15.19/2.49  ------  iProver source info
% 15.19/2.49  
% 15.19/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.19/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.19/2.49  git: non_committed_changes: false
% 15.19/2.49  git: last_make_outside_of_git: false
% 15.19/2.49  
% 15.19/2.49  ------ 
% 15.19/2.49  ------ Parsing...
% 15.19/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.19/2.49  
% 15.19/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 15.19/2.49  
% 15.19/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.19/2.49  
% 15.19/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.19/2.49  ------ Proving...
% 15.19/2.49  ------ Problem Properties 
% 15.19/2.49  
% 15.19/2.49  
% 15.19/2.49  clauses                                 24
% 15.19/2.49  conjectures                             3
% 15.19/2.49  EPR                                     1
% 15.19/2.49  Horn                                    18
% 15.19/2.49  unary                                   5
% 15.19/2.49  binary                                  7
% 15.19/2.49  lits                                    60
% 15.19/2.49  lits eq                                 28
% 15.19/2.49  fd_pure                                 0
% 15.19/2.49  fd_pseudo                               0
% 15.19/2.49  fd_cond                                 4
% 15.19/2.49  fd_pseudo_cond                          0
% 15.19/2.49  AC symbols                              0
% 15.19/2.49  
% 15.19/2.49  ------ Input Options Time Limit: Unbounded
% 15.19/2.49  
% 15.19/2.49  
% 15.19/2.49  ------ 
% 15.19/2.49  Current options:
% 15.19/2.49  ------ 
% 15.19/2.49  
% 15.19/2.49  
% 15.19/2.49  
% 15.19/2.49  
% 15.19/2.49  ------ Proving...
% 15.19/2.49  
% 15.19/2.49  
% 15.19/2.49  % SZS status Theorem for theBenchmark.p
% 15.19/2.49  
% 15.19/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.19/2.49  
% 15.19/2.49  fof(f1,axiom,(
% 15.19/2.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 15.19/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.19/2.49  
% 15.19/2.49  fof(f15,plain,(
% 15.19/2.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 15.19/2.49    inference(ennf_transformation,[],[f1])).
% 15.19/2.49  
% 15.19/2.49  fof(f27,plain,(
% 15.19/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 15.19/2.49    inference(nnf_transformation,[],[f15])).
% 15.19/2.49  
% 15.19/2.49  fof(f28,plain,(
% 15.19/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.19/2.49    inference(rectify,[],[f27])).
% 15.19/2.49  
% 15.19/2.49  fof(f29,plain,(
% 15.19/2.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 15.19/2.49    introduced(choice_axiom,[])).
% 15.19/2.49  
% 15.19/2.49  fof(f30,plain,(
% 15.19/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.19/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 15.19/2.49  
% 15.19/2.49  fof(f45,plain,(
% 15.19/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 15.19/2.49    inference(cnf_transformation,[],[f30])).
% 15.19/2.49  
% 15.19/2.49  fof(f12,conjecture,(
% 15.19/2.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 15.19/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.19/2.49  
% 15.19/2.49  fof(f13,negated_conjecture,(
% 15.19/2.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 15.19/2.49    inference(negated_conjecture,[],[f12])).
% 15.19/2.49  
% 15.19/2.49  fof(f25,plain,(
% 15.19/2.49    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 15.19/2.49    inference(ennf_transformation,[],[f13])).
% 15.19/2.49  
% 15.19/2.49  fof(f26,plain,(
% 15.19/2.49    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 15.19/2.49    inference(flattening,[],[f25])).
% 15.19/2.49  
% 15.19/2.49  fof(f42,plain,(
% 15.19/2.49    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK7(X3)) = X3 & r2_hidden(sK7(X3),X0)))) )),
% 15.19/2.49    introduced(choice_axiom,[])).
% 15.19/2.49  
% 15.19/2.49  fof(f41,plain,(
% 15.19/2.49    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK4,sK5,sK6) != sK5 & ! [X3] : (? [X4] : (k1_funct_1(sK6,X4) = X3 & r2_hidden(X4,sK4)) | ~r2_hidden(X3,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6))),
% 15.19/2.49    introduced(choice_axiom,[])).
% 15.19/2.49  
% 15.19/2.49  fof(f43,plain,(
% 15.19/2.49    k2_relset_1(sK4,sK5,sK6) != sK5 & ! [X3] : ((k1_funct_1(sK6,sK7(X3)) = X3 & r2_hidden(sK7(X3),sK4)) | ~r2_hidden(X3,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6)),
% 15.19/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f26,f42,f41])).
% 15.19/2.49  
% 15.19/2.49  fof(f74,plain,(
% 15.19/2.49    ( ! [X3] : (k1_funct_1(sK6,sK7(X3)) = X3 | ~r2_hidden(X3,sK5)) )),
% 15.19/2.49    inference(cnf_transformation,[],[f43])).
% 15.19/2.49  
% 15.19/2.49  fof(f44,plain,(
% 15.19/2.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 15.19/2.49    inference(cnf_transformation,[],[f30])).
% 15.19/2.49  
% 15.19/2.49  fof(f2,axiom,(
% 15.19/2.49    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 15.19/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.19/2.49  
% 15.19/2.49  fof(f31,plain,(
% 15.19/2.49    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 15.19/2.49    inference(nnf_transformation,[],[f2])).
% 15.19/2.49  
% 15.19/2.49  fof(f32,plain,(
% 15.19/2.49    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 15.19/2.49    inference(flattening,[],[f31])).
% 15.19/2.49  
% 15.19/2.49  fof(f49,plain,(
% 15.19/2.49    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 15.19/2.49    inference(cnf_transformation,[],[f32])).
% 15.19/2.49  
% 15.19/2.49  fof(f76,plain,(
% 15.19/2.49    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 15.19/2.49    inference(equality_resolution,[],[f49])).
% 15.19/2.49  
% 15.19/2.49  fof(f3,axiom,(
% 15.19/2.49    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 15.19/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.19/2.49  
% 15.19/2.49  fof(f50,plain,(
% 15.19/2.49    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 15.19/2.49    inference(cnf_transformation,[],[f3])).
% 15.19/2.49  
% 15.19/2.49  fof(f7,axiom,(
% 15.19/2.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 15.19/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.19/2.49  
% 15.19/2.49  fof(f18,plain,(
% 15.19/2.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.19/2.49    inference(ennf_transformation,[],[f7])).
% 15.19/2.49  
% 15.19/2.49  fof(f19,plain,(
% 15.19/2.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.19/2.49    inference(flattening,[],[f18])).
% 15.19/2.49  
% 15.19/2.49  fof(f34,plain,(
% 15.19/2.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.19/2.49    inference(nnf_transformation,[],[f19])).
% 15.19/2.49  
% 15.19/2.49  fof(f35,plain,(
% 15.19/2.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.19/2.49    inference(rectify,[],[f34])).
% 15.19/2.49  
% 15.19/2.49  fof(f38,plain,(
% 15.19/2.49    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 15.19/2.49    introduced(choice_axiom,[])).
% 15.19/2.49  
% 15.19/2.49  fof(f37,plain,(
% 15.19/2.49    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 15.19/2.49    introduced(choice_axiom,[])).
% 15.19/2.49  
% 15.19/2.49  fof(f36,plain,(
% 15.19/2.49    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 15.19/2.49    introduced(choice_axiom,[])).
% 15.19/2.49  
% 15.19/2.49  fof(f39,plain,(
% 15.19/2.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.19/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f38,f37,f36])).
% 15.19/2.49  
% 15.19/2.49  fof(f59,plain,(
% 15.19/2.49    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) | r2_hidden(sK1(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.19/2.49    inference(cnf_transformation,[],[f39])).
% 15.19/2.49  
% 15.19/2.49  fof(f70,plain,(
% 15.19/2.49    v1_funct_1(sK6)),
% 15.19/2.49    inference(cnf_transformation,[],[f43])).
% 15.19/2.49  
% 15.19/2.49  fof(f4,axiom,(
% 15.19/2.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 15.19/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.19/2.49  
% 15.19/2.49  fof(f16,plain,(
% 15.19/2.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 15.19/2.49    inference(ennf_transformation,[],[f4])).
% 15.19/2.49  
% 15.19/2.49  fof(f51,plain,(
% 15.19/2.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 15.19/2.49    inference(cnf_transformation,[],[f16])).
% 15.19/2.49  
% 15.19/2.49  fof(f72,plain,(
% 15.19/2.49    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 15.19/2.49    inference(cnf_transformation,[],[f43])).
% 15.19/2.49  
% 15.19/2.49  fof(f6,axiom,(
% 15.19/2.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 15.19/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.19/2.49  
% 15.19/2.49  fof(f54,plain,(
% 15.19/2.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 15.19/2.49    inference(cnf_transformation,[],[f6])).
% 15.19/2.49  
% 15.19/2.49  fof(f75,plain,(
% 15.19/2.49    k2_relset_1(sK4,sK5,sK6) != sK5),
% 15.19/2.49    inference(cnf_transformation,[],[f43])).
% 15.19/2.49  
% 15.19/2.49  fof(f10,axiom,(
% 15.19/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 15.19/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.19/2.49  
% 15.19/2.49  fof(f22,plain,(
% 15.19/2.49    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.19/2.49    inference(ennf_transformation,[],[f10])).
% 15.19/2.49  
% 15.19/2.49  fof(f63,plain,(
% 15.19/2.49    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.19/2.49    inference(cnf_transformation,[],[f22])).
% 15.19/2.49  
% 15.19/2.49  fof(f8,axiom,(
% 15.19/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 15.19/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.19/2.49  
% 15.19/2.49  fof(f14,plain,(
% 15.19/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 15.19/2.49    inference(pure_predicate_removal,[],[f8])).
% 15.19/2.49  
% 15.19/2.49  fof(f20,plain,(
% 15.19/2.49    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.19/2.49    inference(ennf_transformation,[],[f14])).
% 15.19/2.49  
% 15.19/2.49  fof(f61,plain,(
% 15.19/2.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.19/2.49    inference(cnf_transformation,[],[f20])).
% 15.19/2.49  
% 15.19/2.49  fof(f5,axiom,(
% 15.19/2.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 15.19/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.19/2.49  
% 15.19/2.49  fof(f17,plain,(
% 15.19/2.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 15.19/2.49    inference(ennf_transformation,[],[f5])).
% 15.19/2.49  
% 15.19/2.49  fof(f33,plain,(
% 15.19/2.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 15.19/2.49    inference(nnf_transformation,[],[f17])).
% 15.19/2.49  
% 15.19/2.49  fof(f52,plain,(
% 15.19/2.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 15.19/2.49    inference(cnf_transformation,[],[f33])).
% 15.19/2.49  
% 15.19/2.49  fof(f46,plain,(
% 15.19/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 15.19/2.49    inference(cnf_transformation,[],[f30])).
% 15.19/2.49  
% 15.19/2.49  fof(f56,plain,(
% 15.19/2.49    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.19/2.49    inference(cnf_transformation,[],[f39])).
% 15.19/2.49  
% 15.19/2.49  fof(f80,plain,(
% 15.19/2.49    ( ! [X0,X5] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.19/2.49    inference(equality_resolution,[],[f56])).
% 15.19/2.49  
% 15.19/2.49  fof(f57,plain,(
% 15.19/2.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.19/2.49    inference(cnf_transformation,[],[f39])).
% 15.19/2.49  
% 15.19/2.49  fof(f78,plain,(
% 15.19/2.49    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.19/2.49    inference(equality_resolution,[],[f57])).
% 15.19/2.49  
% 15.19/2.49  fof(f79,plain,(
% 15.19/2.49    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.19/2.49    inference(equality_resolution,[],[f78])).
% 15.19/2.49  
% 15.19/2.49  fof(f58,plain,(
% 15.19/2.49    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | r2_hidden(sK1(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.19/2.49    inference(cnf_transformation,[],[f39])).
% 15.19/2.49  
% 15.19/2.49  fof(f9,axiom,(
% 15.19/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 15.19/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.19/2.49  
% 15.19/2.49  fof(f21,plain,(
% 15.19/2.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.19/2.49    inference(ennf_transformation,[],[f9])).
% 15.19/2.49  
% 15.19/2.49  fof(f62,plain,(
% 15.19/2.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.19/2.49    inference(cnf_transformation,[],[f21])).
% 15.19/2.49  
% 15.19/2.49  fof(f71,plain,(
% 15.19/2.49    v1_funct_2(sK6,sK4,sK5)),
% 15.19/2.49    inference(cnf_transformation,[],[f43])).
% 15.19/2.49  
% 15.19/2.49  fof(f11,axiom,(
% 15.19/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 15.19/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.19/2.49  
% 15.19/2.49  fof(f23,plain,(
% 15.19/2.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.19/2.49    inference(ennf_transformation,[],[f11])).
% 15.19/2.49  
% 15.19/2.49  fof(f24,plain,(
% 15.19/2.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.19/2.49    inference(flattening,[],[f23])).
% 15.19/2.49  
% 15.19/2.49  fof(f40,plain,(
% 15.19/2.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.19/2.49    inference(nnf_transformation,[],[f24])).
% 15.19/2.49  
% 15.19/2.49  fof(f64,plain,(
% 15.19/2.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.19/2.49    inference(cnf_transformation,[],[f40])).
% 15.19/2.49  
% 15.19/2.49  fof(f73,plain,(
% 15.19/2.49    ( ! [X3] : (r2_hidden(sK7(X3),sK4) | ~r2_hidden(X3,sK5)) )),
% 15.19/2.49    inference(cnf_transformation,[],[f43])).
% 15.19/2.49  
% 15.19/2.49  fof(f55,plain,(
% 15.19/2.49    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.19/2.49    inference(cnf_transformation,[],[f39])).
% 15.19/2.49  
% 15.19/2.49  fof(f81,plain,(
% 15.19/2.49    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.19/2.49    inference(equality_resolution,[],[f55])).
% 15.19/2.49  
% 15.19/2.49  fof(f60,plain,(
% 15.19/2.49    ( ! [X0,X3,X1] : (k2_relat_1(X0) = X1 | k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(sK1(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.19/2.49    inference(cnf_transformation,[],[f39])).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1,plain,
% 15.19/2.49      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 15.19/2.49      inference(cnf_transformation,[],[f45]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1315,plain,
% 15.19/2.49      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 15.19/2.49      | r1_tarski(X0,X1) = iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_27,negated_conjecture,
% 15.19/2.49      ( ~ r2_hidden(X0,sK5) | k1_funct_1(sK6,sK7(X0)) = X0 ),
% 15.19/2.49      inference(cnf_transformation,[],[f74]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1311,plain,
% 15.19/2.49      ( k1_funct_1(sK6,sK7(X0)) = X0 | r2_hidden(X0,sK5) != iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1709,plain,
% 15.19/2.49      ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
% 15.19/2.49      | r1_tarski(sK5,X0) = iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_1315,c_1311]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_2,plain,
% 15.19/2.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 15.19/2.49      inference(cnf_transformation,[],[f44]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1314,plain,
% 15.19/2.49      ( r2_hidden(X0,X1) != iProver_top
% 15.19/2.49      | r2_hidden(X0,X2) = iProver_top
% 15.19/2.49      | r1_tarski(X1,X2) != iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1985,plain,
% 15.19/2.49      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 15.19/2.49      | r1_tarski(X0,X2) != iProver_top
% 15.19/2.49      | r1_tarski(X0,X1) = iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_1315,c_1314]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_3,plain,
% 15.19/2.49      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 15.19/2.49      inference(cnf_transformation,[],[f76]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_6,plain,
% 15.19/2.49      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 15.19/2.49      inference(cnf_transformation,[],[f50]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1313,plain,
% 15.19/2.49      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1538,plain,
% 15.19/2.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_3,c_1313]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_2149,plain,
% 15.19/2.49      ( r1_tarski(X0,X1) = iProver_top
% 15.19/2.49      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_1985,c_1538]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_2207,plain,
% 15.19/2.49      ( k1_funct_1(sK6,sK7(sK0(sK5,k1_xboole_0))) = sK0(sK5,k1_xboole_0)
% 15.19/2.49      | r1_tarski(sK5,X0) = iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_1709,c_2149]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_12,plain,
% 15.19/2.49      ( r2_hidden(sK1(X0,X1),X1)
% 15.19/2.49      | ~ v1_funct_1(X0)
% 15.19/2.49      | ~ v1_relat_1(X0)
% 15.19/2.49      | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
% 15.19/2.49      | k2_relat_1(X0) = X1 ),
% 15.19/2.49      inference(cnf_transformation,[],[f59]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_31,negated_conjecture,
% 15.19/2.49      ( v1_funct_1(sK6) ),
% 15.19/2.49      inference(cnf_transformation,[],[f70]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_659,plain,
% 15.19/2.49      ( r2_hidden(sK1(X0,X1),X1)
% 15.19/2.49      | ~ v1_relat_1(X0)
% 15.19/2.49      | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
% 15.19/2.49      | k2_relat_1(X0) = X1
% 15.19/2.49      | sK6 != X0 ),
% 15.19/2.49      inference(resolution_lifted,[status(thm)],[c_12,c_31]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_660,plain,
% 15.19/2.49      ( r2_hidden(sK1(sK6,X0),X0)
% 15.19/2.49      | ~ v1_relat_1(sK6)
% 15.19/2.49      | k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
% 15.19/2.49      | k2_relat_1(sK6) = X0 ),
% 15.19/2.49      inference(unflattening,[status(thm)],[c_659]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1306,plain,
% 15.19/2.49      ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
% 15.19/2.49      | k2_relat_1(sK6) = X0
% 15.19/2.49      | r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 15.19/2.49      | v1_relat_1(sK6) != iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_660]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_661,plain,
% 15.19/2.49      ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
% 15.19/2.49      | k2_relat_1(sK6) = X0
% 15.19/2.49      | r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 15.19/2.49      | v1_relat_1(sK6) != iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_660]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_997,plain,( X0 = X0 ),theory(equality) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1396,plain,
% 15.19/2.49      ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) = k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_997]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_7,plain,
% 15.19/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.19/2.49      | ~ v1_relat_1(X1)
% 15.19/2.49      | v1_relat_1(X0) ),
% 15.19/2.49      inference(cnf_transformation,[],[f51]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_29,negated_conjecture,
% 15.19/2.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 15.19/2.49      inference(cnf_transformation,[],[f72]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_398,plain,
% 15.19/2.49      ( ~ v1_relat_1(X0)
% 15.19/2.49      | v1_relat_1(X1)
% 15.19/2.49      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(X0)
% 15.19/2.49      | sK6 != X1 ),
% 15.19/2.49      inference(resolution_lifted,[status(thm)],[c_7,c_29]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_399,plain,
% 15.19/2.49      ( ~ v1_relat_1(X0)
% 15.19/2.49      | v1_relat_1(sK6)
% 15.19/2.49      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(X0) ),
% 15.19/2.49      inference(unflattening,[status(thm)],[c_398]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1391,plain,
% 15.19/2.49      ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 15.19/2.49      | v1_relat_1(sK6)
% 15.19/2.49      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_399]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1510,plain,
% 15.19/2.49      ( ~ v1_relat_1(k2_zfmisc_1(sK4,sK5))
% 15.19/2.49      | v1_relat_1(sK6)
% 15.19/2.49      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_1391]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1511,plain,
% 15.19/2.49      ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 15.19/2.49      | v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
% 15.19/2.49      | v1_relat_1(sK6) = iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_1510]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_10,plain,
% 15.19/2.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 15.19/2.49      inference(cnf_transformation,[],[f54]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1579,plain,
% 15.19/2.49      ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_10]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1580,plain,
% 15.19/2.49      ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_1579]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_2978,plain,
% 15.19/2.49      ( r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 15.19/2.49      | k2_relat_1(sK6) = X0
% 15.19/2.49      | k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0) ),
% 15.19/2.49      inference(global_propositional_subsumption,
% 15.19/2.49                [status(thm)],
% 15.19/2.49                [c_1306,c_661,c_1396,c_1511,c_1580]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_2979,plain,
% 15.19/2.49      ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
% 15.19/2.49      | k2_relat_1(sK6) = X0
% 15.19/2.49      | r2_hidden(sK1(sK6,X0),X0) = iProver_top ),
% 15.19/2.49      inference(renaming,[status(thm)],[c_2978]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_2982,plain,
% 15.19/2.49      ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
% 15.19/2.49      | k2_relat_1(sK6) = X0
% 15.19/2.49      | r2_hidden(sK1(sK6,X0),X1) = iProver_top
% 15.19/2.49      | r1_tarski(X0,X1) != iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_2979,c_1314]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_6546,plain,
% 15.19/2.49      ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
% 15.19/2.49      | k2_relat_1(sK6) = X0
% 15.19/2.49      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_2982,c_1538]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_6694,plain,
% 15.19/2.49      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 15.19/2.49      | k1_funct_1(sK6,sK7(sK0(sK5,k1_xboole_0))) = sK0(sK5,k1_xboole_0)
% 15.19/2.49      | k2_relat_1(sK6) = sK5 ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_2207,c_6546]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_26,negated_conjecture,
% 15.19/2.49      ( k2_relset_1(sK4,sK5,sK6) != sK5 ),
% 15.19/2.49      inference(cnf_transformation,[],[f75]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_19,plain,
% 15.19/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.19/2.49      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 15.19/2.49      inference(cnf_transformation,[],[f63]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_464,plain,
% 15.19/2.49      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 15.19/2.49      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 15.19/2.49      | sK6 != X2 ),
% 15.19/2.49      inference(resolution_lifted,[status(thm)],[c_19,c_29]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_465,plain,
% 15.19/2.49      ( k2_relset_1(X0,X1,sK6) = k2_relat_1(sK6)
% 15.19/2.49      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 15.19/2.49      inference(unflattening,[status(thm)],[c_464]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1364,plain,
% 15.19/2.49      ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 15.19/2.49      inference(equality_resolution,[status(thm)],[c_465]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1499,plain,
% 15.19/2.49      ( sK5 = sK5 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_997]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_998,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1495,plain,
% 15.19/2.49      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_998]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1558,plain,
% 15.19/2.49      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_1495]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1697,plain,
% 15.19/2.49      ( k2_relat_1(sK6) != sK5 | sK5 = k2_relat_1(sK6) | sK5 != sK5 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_1558]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1427,plain,
% 15.19/2.49      ( k2_relset_1(sK4,sK5,sK6) != X0
% 15.19/2.49      | k2_relset_1(sK4,sK5,sK6) = sK5
% 15.19/2.49      | sK5 != X0 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_998]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1835,plain,
% 15.19/2.49      ( k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6)
% 15.19/2.49      | k2_relset_1(sK4,sK5,sK6) = sK5
% 15.19/2.49      | sK5 != k2_relat_1(sK6) ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_1427]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_14783,plain,
% 15.19/2.49      ( k1_funct_1(sK6,sK7(sK0(sK5,k1_xboole_0))) = sK0(sK5,k1_xboole_0)
% 15.19/2.49      | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5) ),
% 15.19/2.49      inference(global_propositional_subsumption,
% 15.19/2.49                [status(thm)],
% 15.19/2.49                [c_6694,c_26,c_1364,c_1499,c_1697,c_1835]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_14784,plain,
% 15.19/2.49      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 15.19/2.49      | k1_funct_1(sK6,sK7(sK0(sK5,k1_xboole_0))) = sK0(sK5,k1_xboole_0) ),
% 15.19/2.49      inference(renaming,[status(thm)],[c_14783]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_17,plain,
% 15.19/2.49      ( v5_relat_1(X0,X1)
% 15.19/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 15.19/2.49      inference(cnf_transformation,[],[f61]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_9,plain,
% 15.19/2.49      ( ~ v5_relat_1(X0,X1)
% 15.19/2.49      | r1_tarski(k2_relat_1(X0),X1)
% 15.19/2.49      | ~ v1_relat_1(X0) ),
% 15.19/2.49      inference(cnf_transformation,[],[f52]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_325,plain,
% 15.19/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.19/2.49      | r1_tarski(k2_relat_1(X0),X2)
% 15.19/2.49      | ~ v1_relat_1(X0) ),
% 15.19/2.49      inference(resolution,[status(thm)],[c_17,c_9]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_413,plain,
% 15.19/2.49      ( r1_tarski(k2_relat_1(X0),X1)
% 15.19/2.49      | ~ v1_relat_1(X0)
% 15.19/2.49      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 15.19/2.49      | sK6 != X0 ),
% 15.19/2.49      inference(resolution_lifted,[status(thm)],[c_325,c_29]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_414,plain,
% 15.19/2.49      ( r1_tarski(k2_relat_1(sK6),X0)
% 15.19/2.49      | ~ v1_relat_1(sK6)
% 15.19/2.49      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 15.19/2.49      inference(unflattening,[status(thm)],[c_413]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1308,plain,
% 15.19/2.49      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 15.19/2.49      | r1_tarski(k2_relat_1(sK6),X1) = iProver_top
% 15.19/2.49      | v1_relat_1(sK6) != iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_414]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1644,plain,
% 15.19/2.49      ( v1_relat_1(sK6) ),
% 15.19/2.49      inference(global_propositional_subsumption,
% 15.19/2.49                [status(thm)],
% 15.19/2.49                [c_399,c_1396,c_1510,c_1579]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1656,plain,
% 15.19/2.49      ( r1_tarski(k2_relat_1(sK6),X0)
% 15.19/2.49      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 15.19/2.49      inference(backward_subsumption_resolution,
% 15.19/2.49                [status(thm)],
% 15.19/2.49                [c_1644,c_414]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1677,plain,
% 15.19/2.49      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 15.19/2.49      | r1_tarski(k2_relat_1(sK6),X1) = iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_1656]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_3741,plain,
% 15.19/2.49      ( r1_tarski(k2_relat_1(sK6),X1) = iProver_top
% 15.19/2.49      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 15.19/2.49      inference(global_propositional_subsumption,
% 15.19/2.49                [status(thm)],
% 15.19/2.49                [c_1308,c_1677]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_3742,plain,
% 15.19/2.49      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 15.19/2.49      | r1_tarski(k2_relat_1(sK6),X1) = iProver_top ),
% 15.19/2.49      inference(renaming,[status(thm)],[c_3741]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_3747,plain,
% 15.19/2.49      ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
% 15.19/2.49      inference(equality_resolution,[status(thm)],[c_3742]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_2146,plain,
% 15.19/2.49      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 15.19/2.49      | r1_tarski(X0,X3) != iProver_top
% 15.19/2.49      | r1_tarski(X3,X2) != iProver_top
% 15.19/2.49      | r1_tarski(X0,X1) = iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_1985,c_1314]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_16392,plain,
% 15.19/2.49      ( r2_hidden(sK0(k2_relat_1(sK6),X0),X1) = iProver_top
% 15.19/2.49      | r1_tarski(k2_relat_1(sK6),X0) = iProver_top
% 15.19/2.49      | r1_tarski(sK5,X1) != iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_3747,c_2146]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_0,plain,
% 15.19/2.50      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 15.19/2.50      inference(cnf_transformation,[],[f46]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_1316,plain,
% 15.19/2.50      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 15.19/2.50      | r1_tarski(X0,X1) = iProver_top ),
% 15.19/2.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_18001,plain,
% 15.19/2.50      ( r1_tarski(k2_relat_1(sK6),X0) = iProver_top
% 15.19/2.50      | r1_tarski(sK5,X0) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_16392,c_1316]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_15,plain,
% 15.19/2.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 15.19/2.50      | ~ v1_funct_1(X1)
% 15.19/2.50      | ~ v1_relat_1(X1)
% 15.19/2.50      | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
% 15.19/2.50      inference(cnf_transformation,[],[f80]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_692,plain,
% 15.19/2.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 15.19/2.50      | ~ v1_relat_1(X1)
% 15.19/2.50      | k1_funct_1(X1,sK3(X1,X0)) = X0
% 15.19/2.50      | sK6 != X1 ),
% 15.19/2.50      inference(resolution_lifted,[status(thm)],[c_15,c_31]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_693,plain,
% 15.19/2.50      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 15.19/2.50      | ~ v1_relat_1(sK6)
% 15.19/2.50      | k1_funct_1(sK6,sK3(sK6,X0)) = X0 ),
% 15.19/2.50      inference(unflattening,[status(thm)],[c_692]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_1304,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK3(sK6,X0)) = X0
% 15.19/2.50      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 15.19/2.50      | v1_relat_1(sK6) != iProver_top ),
% 15.19/2.50      inference(predicate_to_equality,[status(thm)],[c_693]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_694,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK3(sK6,X0)) = X0
% 15.19/2.50      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 15.19/2.50      | v1_relat_1(sK6) != iProver_top ),
% 15.19/2.50      inference(predicate_to_equality,[status(thm)],[c_693]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_2450,plain,
% 15.19/2.50      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 15.19/2.50      | k1_funct_1(sK6,sK3(sK6,X0)) = X0 ),
% 15.19/2.50      inference(global_propositional_subsumption,
% 15.19/2.50                [status(thm)],
% 15.19/2.50                [c_1304,c_694,c_1396,c_1511,c_1580]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_2451,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK3(sK6,X0)) = X0
% 15.19/2.50      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
% 15.19/2.50      inference(renaming,[status(thm)],[c_2450]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_2454,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK3(sK6,sK0(k2_relat_1(sK6),X0))) = sK0(k2_relat_1(sK6),X0)
% 15.19/2.50      | r1_tarski(k2_relat_1(sK6),X0) = iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_1315,c_2451]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_14,plain,
% 15.19/2.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 15.19/2.50      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 15.19/2.50      | ~ v1_funct_1(X1)
% 15.19/2.50      | ~ v1_relat_1(X1) ),
% 15.19/2.50      inference(cnf_transformation,[],[f79]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_707,plain,
% 15.19/2.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 15.19/2.50      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 15.19/2.50      | ~ v1_relat_1(X1)
% 15.19/2.50      | sK6 != X1 ),
% 15.19/2.50      inference(resolution_lifted,[status(thm)],[c_14,c_31]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_708,plain,
% 15.19/2.50      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 15.19/2.50      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
% 15.19/2.50      | ~ v1_relat_1(sK6) ),
% 15.19/2.50      inference(unflattening,[status(thm)],[c_707]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_1303,plain,
% 15.19/2.50      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 15.19/2.50      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
% 15.19/2.50      | v1_relat_1(sK6) != iProver_top ),
% 15.19/2.50      inference(predicate_to_equality,[status(thm)],[c_708]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_1655,plain,
% 15.19/2.50      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 15.19/2.50      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) ),
% 15.19/2.50      inference(backward_subsumption_resolution,
% 15.19/2.50                [status(thm)],
% 15.19/2.50                [c_1644,c_708]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_1680,plain,
% 15.19/2.50      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 15.19/2.50      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top ),
% 15.19/2.50      inference(predicate_to_equality,[status(thm)],[c_1655]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_2212,plain,
% 15.19/2.50      ( r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
% 15.19/2.50      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 15.19/2.50      inference(global_propositional_subsumption,
% 15.19/2.50                [status(thm)],
% 15.19/2.50                [c_1303,c_1680]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_2213,plain,
% 15.19/2.50      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 15.19/2.50      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top ),
% 15.19/2.50      inference(renaming,[status(thm)],[c_2212]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_2216,plain,
% 15.19/2.50      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 15.19/2.50      | r2_hidden(k1_funct_1(sK6,X0),X1) = iProver_top
% 15.19/2.50      | r1_tarski(k2_relat_1(sK6),X1) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_2213,c_1314]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_2798,plain,
% 15.19/2.50      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 15.19/2.50      | r1_tarski(k2_relat_1(sK6),k1_xboole_0) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_2216,c_1538]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_2816,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK3(sK6,sK0(k2_relat_1(sK6),k1_xboole_0))) = sK0(k2_relat_1(sK6),k1_xboole_0)
% 15.19/2.50      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_2454,c_2798]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_11754,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK3(sK6,sK0(k2_relat_1(sK6),k1_xboole_0))) = sK0(k2_relat_1(sK6),k1_xboole_0)
% 15.19/2.50      | r1_tarski(k1_relat_1(sK6),X0) = iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_1315,c_2816]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_13,plain,
% 15.19/2.50      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 15.19/2.50      | r2_hidden(sK1(X0,X1),X1)
% 15.19/2.50      | ~ v1_funct_1(X0)
% 15.19/2.50      | ~ v1_relat_1(X0)
% 15.19/2.50      | k2_relat_1(X0) = X1 ),
% 15.19/2.50      inference(cnf_transformation,[],[f58]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_641,plain,
% 15.19/2.50      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 15.19/2.50      | r2_hidden(sK1(X0,X1),X1)
% 15.19/2.50      | ~ v1_relat_1(X0)
% 15.19/2.50      | k2_relat_1(X0) = X1
% 15.19/2.50      | sK6 != X0 ),
% 15.19/2.50      inference(resolution_lifted,[status(thm)],[c_13,c_31]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_642,plain,
% 15.19/2.50      ( r2_hidden(sK2(sK6,X0),k1_relat_1(sK6))
% 15.19/2.50      | r2_hidden(sK1(sK6,X0),X0)
% 15.19/2.50      | ~ v1_relat_1(sK6)
% 15.19/2.50      | k2_relat_1(sK6) = X0 ),
% 15.19/2.50      inference(unflattening,[status(thm)],[c_641]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_1307,plain,
% 15.19/2.50      ( k2_relat_1(sK6) = X0
% 15.19/2.50      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 15.19/2.50      | r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 15.19/2.50      | v1_relat_1(sK6) != iProver_top ),
% 15.19/2.50      inference(predicate_to_equality,[status(thm)],[c_642]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_1657,plain,
% 15.19/2.50      ( r2_hidden(sK2(sK6,X0),k1_relat_1(sK6))
% 15.19/2.50      | r2_hidden(sK1(sK6,X0),X0)
% 15.19/2.50      | k2_relat_1(sK6) = X0 ),
% 15.19/2.50      inference(backward_subsumption_resolution,
% 15.19/2.50                [status(thm)],
% 15.19/2.50                [c_1644,c_642]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_1674,plain,
% 15.19/2.50      ( k2_relat_1(sK6) = X0
% 15.19/2.50      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 15.19/2.50      | r2_hidden(sK1(sK6,X0),X0) = iProver_top ),
% 15.19/2.50      inference(predicate_to_equality,[status(thm)],[c_1657]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_3244,plain,
% 15.19/2.50      ( r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 15.19/2.50      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 15.19/2.50      | k2_relat_1(sK6) = X0 ),
% 15.19/2.50      inference(global_propositional_subsumption,
% 15.19/2.50                [status(thm)],
% 15.19/2.50                [c_1307,c_1674]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_3245,plain,
% 15.19/2.50      ( k2_relat_1(sK6) = X0
% 15.19/2.50      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 15.19/2.50      | r2_hidden(sK1(sK6,X0),X0) = iProver_top ),
% 15.19/2.50      inference(renaming,[status(thm)],[c_3244]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_3255,plain,
% 15.19/2.50      ( k2_relat_1(sK6) = X0
% 15.19/2.50      | r2_hidden(sK2(sK6,X0),X1) = iProver_top
% 15.19/2.50      | r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 15.19/2.50      | r1_tarski(k1_relat_1(sK6),X1) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_3245,c_1314]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_6159,plain,
% 15.19/2.50      ( k2_relat_1(sK6) = X0
% 15.19/2.50      | r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 15.19/2.50      | r1_tarski(k1_relat_1(sK6),k1_xboole_0) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_3255,c_1538]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_6191,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
% 15.19/2.50      | k2_relat_1(sK6) = sK5
% 15.19/2.50      | r1_tarski(k1_relat_1(sK6),k1_xboole_0) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_6159,c_1311]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_1431,plain,
% 15.19/2.50      ( sK5 != X0 | sK5 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_998]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_1498,plain,
% 15.19/2.50      ( sK5 != sK5 | sK5 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_1431]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_999,plain,
% 15.19/2.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 15.19/2.50      theory(equality) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_18,plain,
% 15.19/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.19/2.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 15.19/2.50      inference(cnf_transformation,[],[f62]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_473,plain,
% 15.19/2.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 15.19/2.50      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 15.19/2.50      | sK6 != X2 ),
% 15.19/2.50      inference(resolution_lifted,[status(thm)],[c_18,c_29]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_474,plain,
% 15.19/2.50      ( k1_relset_1(X0,X1,sK6) = k1_relat_1(sK6)
% 15.19/2.50      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 15.19/2.50      inference(unflattening,[status(thm)],[c_473]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_1721,plain,
% 15.19/2.50      ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
% 15.19/2.50      inference(resolution,[status(thm)],[c_474,c_997]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_2645,plain,
% 15.19/2.50      ( r1_tarski(k1_relset_1(sK4,sK5,sK6),X0)
% 15.19/2.50      | ~ r1_tarski(k1_relat_1(sK6),X0) ),
% 15.19/2.50      inference(resolution,[status(thm)],[c_999,c_1721]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_2646,plain,
% 15.19/2.50      ( r1_tarski(k1_relset_1(sK4,sK5,sK6),X0) = iProver_top
% 15.19/2.50      | r1_tarski(k1_relat_1(sK6),X0) != iProver_top ),
% 15.19/2.50      inference(predicate_to_equality,[status(thm)],[c_2645]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_2648,plain,
% 15.19/2.50      ( r1_tarski(k1_relset_1(sK4,sK5,sK6),k1_xboole_0) = iProver_top
% 15.19/2.50      | r1_tarski(k1_relat_1(sK6),k1_xboole_0) != iProver_top ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_2646]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_2933,plain,
% 15.19/2.50      ( k2_relat_1(sK6) != X0 | sK5 != X0 | sK5 = k2_relat_1(sK6) ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_1495]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_2934,plain,
% 15.19/2.50      ( k2_relat_1(sK6) != k1_xboole_0
% 15.19/2.50      | sK5 = k2_relat_1(sK6)
% 15.19/2.50      | sK5 != k1_xboole_0 ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_2933]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_3254,plain,
% 15.19/2.50      ( k2_relat_1(sK6) = k1_xboole_0
% 15.19/2.50      | r2_hidden(sK2(sK6,k1_xboole_0),k1_relat_1(sK6)) = iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_3245,c_1538]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_3303,plain,
% 15.19/2.50      ( k2_relat_1(sK6) = k1_xboole_0
% 15.19/2.50      | r2_hidden(sK2(sK6,k1_xboole_0),X0) = iProver_top
% 15.19/2.50      | r1_tarski(k1_relat_1(sK6),X0) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_3254,c_1314]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_3315,plain,
% 15.19/2.50      ( k2_relat_1(sK6) = k1_xboole_0
% 15.19/2.50      | r1_tarski(k1_relat_1(sK6),k1_xboole_0) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_3303,c_1538]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_3336,plain,
% 15.19/2.50      ( X0 != X1 | X1 = X0 ),
% 15.19/2.50      inference(resolution,[status(thm)],[c_998,c_997]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_30,negated_conjecture,
% 15.19/2.50      ( v1_funct_2(sK6,sK4,sK5) ),
% 15.19/2.50      inference(cnf_transformation,[],[f71]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_25,plain,
% 15.19/2.50      ( ~ v1_funct_2(X0,X1,X2)
% 15.19/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.19/2.50      | k1_relset_1(X1,X2,X0) = X1
% 15.19/2.50      | k1_xboole_0 = X2 ),
% 15.19/2.50      inference(cnf_transformation,[],[f64]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_428,plain,
% 15.19/2.50      ( ~ v1_funct_2(X0,X1,X2)
% 15.19/2.50      | k1_relset_1(X1,X2,X0) = X1
% 15.19/2.50      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 15.19/2.50      | sK6 != X0
% 15.19/2.50      | k1_xboole_0 = X2 ),
% 15.19/2.50      inference(resolution_lifted,[status(thm)],[c_25,c_29]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_429,plain,
% 15.19/2.50      ( ~ v1_funct_2(sK6,X0,X1)
% 15.19/2.50      | k1_relset_1(X0,X1,sK6) = X0
% 15.19/2.50      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 15.19/2.50      | k1_xboole_0 = X1 ),
% 15.19/2.50      inference(unflattening,[status(thm)],[c_428]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_779,plain,
% 15.19/2.50      ( k1_relset_1(X0,X1,sK6) = X0
% 15.19/2.50      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 15.19/2.50      | sK6 != sK6
% 15.19/2.50      | sK5 != X1
% 15.19/2.50      | sK4 != X0
% 15.19/2.50      | k1_xboole_0 = X1 ),
% 15.19/2.50      inference(resolution_lifted,[status(thm)],[c_30,c_429]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_780,plain,
% 15.19/2.50      ( k1_relset_1(sK4,sK5,sK6) = sK4
% 15.19/2.50      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 15.19/2.50      | k1_xboole_0 = sK5 ),
% 15.19/2.50      inference(unflattening,[status(thm)],[c_779]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_848,plain,
% 15.19/2.50      ( k1_relset_1(sK4,sK5,sK6) = sK4 | k1_xboole_0 = sK5 ),
% 15.19/2.50      inference(equality_resolution_simp,[status(thm)],[c_780]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_5670,plain,
% 15.19/2.50      ( sK4 = k1_relset_1(sK4,sK5,sK6) | k1_xboole_0 = sK5 ),
% 15.19/2.50      inference(resolution,[status(thm)],[c_3336,c_848]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_2347,plain,
% 15.19/2.50      ( ~ r1_tarski(X0,X1) | r1_tarski(sK4,X1) | sK4 != X0 ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_999]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_5719,plain,
% 15.19/2.50      ( ~ r1_tarski(k1_relset_1(sK4,sK5,sK6),X0)
% 15.19/2.50      | r1_tarski(sK4,X0)
% 15.19/2.50      | sK4 != k1_relset_1(sK4,sK5,sK6) ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_2347]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_5720,plain,
% 15.19/2.50      ( sK4 != k1_relset_1(sK4,sK5,sK6)
% 15.19/2.50      | r1_tarski(k1_relset_1(sK4,sK5,sK6),X0) != iProver_top
% 15.19/2.50      | r1_tarski(sK4,X0) = iProver_top ),
% 15.19/2.50      inference(predicate_to_equality,[status(thm)],[c_5719]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_5722,plain,
% 15.19/2.50      ( sK4 != k1_relset_1(sK4,sK5,sK6)
% 15.19/2.50      | r1_tarski(k1_relset_1(sK4,sK5,sK6),k1_xboole_0) != iProver_top
% 15.19/2.50      | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_5720]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_28,negated_conjecture,
% 15.19/2.50      ( ~ r2_hidden(X0,sK5) | r2_hidden(sK7(X0),sK4) ),
% 15.19/2.50      inference(cnf_transformation,[],[f73]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_1310,plain,
% 15.19/2.50      ( r2_hidden(X0,sK5) != iProver_top
% 15.19/2.50      | r2_hidden(sK7(X0),sK4) = iProver_top ),
% 15.19/2.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_1986,plain,
% 15.19/2.50      ( r2_hidden(X0,sK5) != iProver_top
% 15.19/2.50      | r2_hidden(sK7(X0),X1) = iProver_top
% 15.19/2.50      | r1_tarski(sK4,X1) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_1310,c_1314]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_2281,plain,
% 15.19/2.50      ( r2_hidden(X0,sK5) != iProver_top
% 15.19/2.50      | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_1986,c_1538]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_6190,plain,
% 15.19/2.50      ( k2_relat_1(sK6) = sK5
% 15.19/2.50      | r1_tarski(k1_relat_1(sK6),k1_xboole_0) != iProver_top
% 15.19/2.50      | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_6159,c_2281]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_6344,plain,
% 15.19/2.50      ( r1_tarski(k1_relat_1(sK6),k1_xboole_0) != iProver_top ),
% 15.19/2.50      inference(global_propositional_subsumption,
% 15.19/2.50                [status(thm)],
% 15.19/2.50                [c_6191,c_26,c_1364,c_1498,c_1499,c_1697,c_1835,c_2648,
% 15.19/2.50                 c_2934,c_3315,c_5670,c_5722,c_6190]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_11784,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK3(sK6,sK0(k2_relat_1(sK6),k1_xboole_0))) = sK0(k2_relat_1(sK6),k1_xboole_0)
% 15.19/2.50      | r1_tarski(k1_relat_1(sK6),k1_xboole_0) = iProver_top ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_11754]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_11813,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK3(sK6,sK0(k2_relat_1(sK6),k1_xboole_0))) = sK0(k2_relat_1(sK6),k1_xboole_0) ),
% 15.19/2.50      inference(global_propositional_subsumption,
% 15.19/2.50                [status(thm)],
% 15.19/2.50                [c_11754,c_26,c_1364,c_1498,c_1499,c_1697,c_1835,c_2648,
% 15.19/2.50                 c_2934,c_3315,c_5670,c_5722,c_6190,c_11784]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_2147,plain,
% 15.19/2.50      ( r1_tarski(X0,X1) = iProver_top
% 15.19/2.50      | r1_tarski(X0,k2_zfmisc_1(sK0(X0,X1),X2)) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_1985,c_1313]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_2575,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK3(sK6,sK0(k2_relat_1(sK6),k2_zfmisc_1(sK0(k2_relat_1(sK6),X0),X1)))) = sK0(k2_relat_1(sK6),k2_zfmisc_1(sK0(k2_relat_1(sK6),X0),X1))
% 15.19/2.50      | r1_tarski(k2_relat_1(sK6),X0) = iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_2454,c_2147]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_2796,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK7(k1_funct_1(sK6,X0))) = k1_funct_1(sK6,X0)
% 15.19/2.50      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 15.19/2.50      | r1_tarski(k2_relat_1(sK6),sK5) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_2216,c_1311]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_1693,plain,
% 15.19/2.50      ( r1_tarski(k2_relat_1(sK6),sK5)
% 15.19/2.50      | ~ v1_relat_1(sK6)
% 15.19/2.50      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_414]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_1694,plain,
% 15.19/2.50      ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 15.19/2.50      | r1_tarski(k2_relat_1(sK6),sK5) = iProver_top
% 15.19/2.50      | v1_relat_1(sK6) != iProver_top ),
% 15.19/2.50      inference(predicate_to_equality,[status(thm)],[c_1693]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_4287,plain,
% 15.19/2.50      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 15.19/2.50      | k1_funct_1(sK6,sK7(k1_funct_1(sK6,X0))) = k1_funct_1(sK6,X0) ),
% 15.19/2.50      inference(global_propositional_subsumption,
% 15.19/2.50                [status(thm)],
% 15.19/2.50                [c_2796,c_1396,c_1511,c_1580,c_1694]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_4288,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK7(k1_funct_1(sK6,X0))) = k1_funct_1(sK6,X0)
% 15.19/2.50      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 15.19/2.50      inference(renaming,[status(thm)],[c_4287]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_4293,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK7(k1_funct_1(sK6,sK0(k1_relat_1(sK6),X0)))) = k1_funct_1(sK6,sK0(k1_relat_1(sK6),X0))
% 15.19/2.50      | r1_tarski(k1_relat_1(sK6),X0) = iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_1315,c_4288]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_6348,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK7(k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0)))) = k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0)) ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_4293,c_6344]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_3309,plain,
% 15.19/2.50      ( k2_relat_1(sK6) = k1_xboole_0
% 15.19/2.50      | r1_tarski(k1_relat_1(sK6),k2_zfmisc_1(sK2(sK6,k1_xboole_0),X0)) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_3303,c_1313]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_4330,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK7(k1_funct_1(sK6,sK0(k1_relat_1(sK6),k2_zfmisc_1(sK2(sK6,k1_xboole_0),X0))))) = k1_funct_1(sK6,sK0(k1_relat_1(sK6),k2_zfmisc_1(sK2(sK6,k1_xboole_0),X0)))
% 15.19/2.50      | k2_relat_1(sK6) = k1_xboole_0 ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_4293,c_3309]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_23303,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK0(k1_relat_1(sK6),k2_zfmisc_1(sK2(sK6,k1_xboole_0),k1_xboole_0))) = k1_funct_1(sK6,sK7(k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0))))
% 15.19/2.50      | k2_relat_1(sK6) = k1_xboole_0 ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_3,c_4330]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_23380,plain,
% 15.19/2.50      ( k2_relat_1(sK6) = k1_xboole_0
% 15.19/2.50      | r2_hidden(k1_funct_1(sK6,sK7(k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0)))),X0) = iProver_top
% 15.19/2.50      | r2_hidden(sK0(k1_relat_1(sK6),k2_zfmisc_1(sK2(sK6,k1_xboole_0),k1_xboole_0)),k1_relat_1(sK6)) != iProver_top
% 15.19/2.50      | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_23303,c_2216]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_25033,plain,
% 15.19/2.50      ( k2_relat_1(sK6) = k1_xboole_0
% 15.19/2.50      | r2_hidden(k1_funct_1(sK6,sK7(k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0)))),X0) = iProver_top
% 15.19/2.50      | r2_hidden(sK0(k1_relat_1(sK6),k1_xboole_0),k1_relat_1(sK6)) != iProver_top
% 15.19/2.50      | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_3,c_23380]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_4276,plain,
% 15.19/2.50      ( r2_hidden(sK0(k1_relat_1(sK6),X0),k1_relat_1(sK6))
% 15.19/2.50      | r1_tarski(k1_relat_1(sK6),X0) ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_1]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_4277,plain,
% 15.19/2.50      ( r2_hidden(sK0(k1_relat_1(sK6),X0),k1_relat_1(sK6)) = iProver_top
% 15.19/2.50      | r1_tarski(k1_relat_1(sK6),X0) = iProver_top ),
% 15.19/2.50      inference(predicate_to_equality,[status(thm)],[c_4276]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_4279,plain,
% 15.19/2.50      ( r2_hidden(sK0(k1_relat_1(sK6),k1_xboole_0),k1_relat_1(sK6)) = iProver_top
% 15.19/2.50      | r1_tarski(k1_relat_1(sK6),k1_xboole_0) = iProver_top ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_4277]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_25220,plain,
% 15.19/2.50      ( r2_hidden(k1_funct_1(sK6,sK7(k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0)))),X0) = iProver_top
% 15.19/2.50      | k2_relat_1(sK6) = k1_xboole_0
% 15.19/2.50      | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
% 15.19/2.50      inference(global_propositional_subsumption,
% 15.19/2.50                [status(thm)],
% 15.19/2.50                [c_25033,c_26,c_1364,c_1498,c_1499,c_1697,c_1835,c_2648,
% 15.19/2.50                 c_2934,c_3315,c_4279,c_5670,c_5722,c_6190]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_25221,plain,
% 15.19/2.50      ( k2_relat_1(sK6) = k1_xboole_0
% 15.19/2.50      | r2_hidden(k1_funct_1(sK6,sK7(k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0)))),X0) = iProver_top
% 15.19/2.50      | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
% 15.19/2.50      inference(renaming,[status(thm)],[c_25220]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_25226,plain,
% 15.19/2.50      ( k2_relat_1(sK6) = k1_xboole_0
% 15.19/2.50      | r1_tarski(k2_relat_1(sK6),k2_zfmisc_1(k1_funct_1(sK6,sK7(k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0)))),X0)) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_25221,c_1313]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_25276,plain,
% 15.19/2.50      ( k2_relat_1(sK6) = k1_xboole_0
% 15.19/2.50      | r1_tarski(k2_relat_1(sK6),k2_zfmisc_1(k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0)),X0)) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_6348,c_25226]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_2455,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK3(sK6,k1_funct_1(sK6,X0))) = k1_funct_1(sK6,X0)
% 15.19/2.50      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_2213,c_2451]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_6945,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK3(sK6,k1_funct_1(sK6,sK0(k1_relat_1(sK6),X0)))) = k1_funct_1(sK6,sK0(k1_relat_1(sK6),X0))
% 15.19/2.50      | r1_tarski(k1_relat_1(sK6),X0) = iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_1315,c_2455]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_6994,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK3(sK6,k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0)))) = k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0)) ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_6945,c_6344]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_2793,plain,
% 15.19/2.50      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 15.19/2.50      | r1_tarski(k2_relat_1(sK6),k2_zfmisc_1(k1_funct_1(sK6,X0),X1)) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_2216,c_1313]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_10631,plain,
% 15.19/2.50      ( r2_hidden(sK3(sK6,k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0))),k1_relat_1(sK6)) != iProver_top
% 15.19/2.50      | r1_tarski(k2_relat_1(sK6),k2_zfmisc_1(k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0)),X0)) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_6994,c_2793]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_11687,plain,
% 15.19/2.50      ( r2_hidden(k1_funct_1(sK6,sK0(k1_relat_1(sK6),X0)),k2_relat_1(sK6))
% 15.19/2.50      | ~ r2_hidden(sK0(k1_relat_1(sK6),X0),k1_relat_1(sK6))
% 15.19/2.50      | ~ v1_relat_1(sK6) ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_708]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_11688,plain,
% 15.19/2.50      ( r2_hidden(k1_funct_1(sK6,sK0(k1_relat_1(sK6),X0)),k2_relat_1(sK6)) = iProver_top
% 15.19/2.50      | r2_hidden(sK0(k1_relat_1(sK6),X0),k1_relat_1(sK6)) != iProver_top
% 15.19/2.50      | v1_relat_1(sK6) != iProver_top ),
% 15.19/2.50      inference(predicate_to_equality,[status(thm)],[c_11687]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_11690,plain,
% 15.19/2.50      ( r2_hidden(k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0)),k2_relat_1(sK6)) = iProver_top
% 15.19/2.50      | r2_hidden(sK0(k1_relat_1(sK6),k1_xboole_0),k1_relat_1(sK6)) != iProver_top
% 15.19/2.50      | v1_relat_1(sK6) != iProver_top ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_11688]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_16,plain,
% 15.19/2.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 15.19/2.50      | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
% 15.19/2.50      | ~ v1_funct_1(X1)
% 15.19/2.50      | ~ v1_relat_1(X1) ),
% 15.19/2.50      inference(cnf_transformation,[],[f81]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_677,plain,
% 15.19/2.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 15.19/2.50      | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
% 15.19/2.50      | ~ v1_relat_1(X1)
% 15.19/2.50      | sK6 != X1 ),
% 15.19/2.50      inference(resolution_lifted,[status(thm)],[c_16,c_31]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_678,plain,
% 15.19/2.50      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 15.19/2.50      | r2_hidden(sK3(sK6,X0),k1_relat_1(sK6))
% 15.19/2.50      | ~ v1_relat_1(sK6) ),
% 15.19/2.50      inference(unflattening,[status(thm)],[c_677]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_17440,plain,
% 15.19/2.50      ( r2_hidden(sK3(sK6,k1_funct_1(sK6,sK0(k1_relat_1(sK6),X0))),k1_relat_1(sK6))
% 15.19/2.50      | ~ r2_hidden(k1_funct_1(sK6,sK0(k1_relat_1(sK6),X0)),k2_relat_1(sK6))
% 15.19/2.50      | ~ v1_relat_1(sK6) ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_678]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_17441,plain,
% 15.19/2.50      ( r2_hidden(sK3(sK6,k1_funct_1(sK6,sK0(k1_relat_1(sK6),X0))),k1_relat_1(sK6)) = iProver_top
% 15.19/2.50      | r2_hidden(k1_funct_1(sK6,sK0(k1_relat_1(sK6),X0)),k2_relat_1(sK6)) != iProver_top
% 15.19/2.50      | v1_relat_1(sK6) != iProver_top ),
% 15.19/2.50      inference(predicate_to_equality,[status(thm)],[c_17440]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_17443,plain,
% 15.19/2.50      ( r2_hidden(sK3(sK6,k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0))),k1_relat_1(sK6)) = iProver_top
% 15.19/2.50      | r2_hidden(k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0)),k2_relat_1(sK6)) != iProver_top
% 15.19/2.50      | v1_relat_1(sK6) != iProver_top ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_17441]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_26380,plain,
% 15.19/2.50      ( r1_tarski(k2_relat_1(sK6),k2_zfmisc_1(k1_funct_1(sK6,sK0(k1_relat_1(sK6),k1_xboole_0)),X0)) != iProver_top ),
% 15.19/2.50      inference(global_propositional_subsumption,
% 15.19/2.50                [status(thm)],
% 15.19/2.50                [c_25276,c_26,c_1364,c_1396,c_1498,c_1499,c_1511,c_1580,
% 15.19/2.50                 c_1697,c_1835,c_2648,c_2934,c_3315,c_4279,c_5670,c_5722,
% 15.19/2.50                 c_6190,c_10631,c_11690,c_17443]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_26394,plain,
% 15.19/2.50      ( r1_tarski(k2_relat_1(sK6),k1_xboole_0) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_3,c_26380]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_26556,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK3(sK6,sK0(k2_relat_1(sK6),k2_zfmisc_1(sK0(k2_relat_1(sK6),k1_xboole_0),X0)))) = sK0(k2_relat_1(sK6),k2_zfmisc_1(sK0(k2_relat_1(sK6),k1_xboole_0),X0)) ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_2575,c_26394]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_26845,plain,
% 15.19/2.50      ( sK0(k2_relat_1(sK6),k2_zfmisc_1(sK0(k2_relat_1(sK6),k1_xboole_0),k1_xboole_0)) = k1_funct_1(sK6,sK3(sK6,sK0(k2_relat_1(sK6),k1_xboole_0))) ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_3,c_26556]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_26868,plain,
% 15.19/2.50      ( r2_hidden(k1_funct_1(sK6,sK3(sK6,sK0(k2_relat_1(sK6),k1_xboole_0))),k2_relat_1(sK6)) = iProver_top
% 15.19/2.50      | r1_tarski(k2_relat_1(sK6),k2_zfmisc_1(sK0(k2_relat_1(sK6),k1_xboole_0),k1_xboole_0)) = iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_26845,c_1315]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_1710,plain,
% 15.19/2.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_1315,c_1538]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_1715,plain,
% 15.19/2.50      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_1710]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_4520,plain,
% 15.19/2.50      ( ~ r1_tarski(X0,X1)
% 15.19/2.50      | r1_tarski(k2_relat_1(sK6),X1)
% 15.19/2.50      | k2_relat_1(sK6) != X0 ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_999]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_4521,plain,
% 15.19/2.50      ( k2_relat_1(sK6) != X0
% 15.19/2.50      | r1_tarski(X0,X1) != iProver_top
% 15.19/2.50      | r1_tarski(k2_relat_1(sK6),X1) = iProver_top ),
% 15.19/2.50      inference(predicate_to_equality,[status(thm)],[c_4520]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_4523,plain,
% 15.19/2.50      ( k2_relat_1(sK6) != k1_xboole_0
% 15.19/2.50      | r1_tarski(k2_relat_1(sK6),k1_xboole_0) = iProver_top
% 15.19/2.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_4521]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_2148,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK7(sK0(X0,X1))) = sK0(X0,X1)
% 15.19/2.50      | r1_tarski(X0,X1) = iProver_top
% 15.19/2.50      | r1_tarski(X0,sK5) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_1985,c_1311]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_16395,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),X0))) = sK0(k2_relat_1(sK6),X0)
% 15.19/2.50      | r1_tarski(k2_relat_1(sK6),X0) = iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_3747,c_2148]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_17088,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),k1_xboole_0))) = sK0(k2_relat_1(sK6),k1_xboole_0)
% 15.19/2.50      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_16395,c_2798]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_17615,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),k1_xboole_0))) = sK0(k2_relat_1(sK6),k1_xboole_0)
% 15.19/2.50      | r1_tarski(k1_relat_1(sK6),X0) = iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_1315,c_17088]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_17651,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),k1_xboole_0))) = sK0(k2_relat_1(sK6),k1_xboole_0)
% 15.19/2.50      | r1_tarski(k1_relat_1(sK6),k1_xboole_0) = iProver_top ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_17615]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_17854,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),k1_xboole_0))) = sK0(k2_relat_1(sK6),k1_xboole_0) ),
% 15.19/2.50      inference(global_propositional_subsumption,
% 15.19/2.50                [status(thm)],
% 15.19/2.50                [c_17615,c_26,c_1364,c_1498,c_1499,c_1697,c_1835,c_2648,
% 15.19/2.50                 c_2934,c_3315,c_5670,c_5722,c_6190,c_17651]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_2987,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK2(sK6,k1_xboole_0)) = sK1(sK6,k1_xboole_0)
% 15.19/2.50      | k2_relat_1(sK6) = k1_xboole_0 ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_2979,c_1538]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_2993,plain,
% 15.19/2.50      ( k2_relat_1(sK6) = k1_xboole_0
% 15.19/2.50      | r2_hidden(sK2(sK6,k1_xboole_0),k1_relat_1(sK6)) != iProver_top
% 15.19/2.50      | r2_hidden(sK1(sK6,k1_xboole_0),k2_relat_1(sK6)) = iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_2987,c_2213]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_13029,plain,
% 15.19/2.50      ( k2_relat_1(sK6) = k1_xboole_0
% 15.19/2.50      | r2_hidden(sK1(sK6,k1_xboole_0),k2_relat_1(sK6)) = iProver_top ),
% 15.19/2.50      inference(global_propositional_subsumption,
% 15.19/2.50                [status(thm)],
% 15.19/2.50                [c_2993,c_3254]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_13033,plain,
% 15.19/2.50      ( k2_relat_1(sK6) = k1_xboole_0
% 15.19/2.50      | r2_hidden(sK1(sK6,k1_xboole_0),X0) = iProver_top
% 15.19/2.50      | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_13029,c_1314]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_13213,plain,
% 15.19/2.50      ( k2_relat_1(sK6) = k1_xboole_0
% 15.19/2.50      | r1_tarski(k2_relat_1(sK6),k2_zfmisc_1(sK1(sK6,k1_xboole_0),X0)) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_13033,c_1313]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_17100,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),k2_zfmisc_1(sK1(sK6,k1_xboole_0),X0)))) = sK0(k2_relat_1(sK6),k2_zfmisc_1(sK1(sK6,k1_xboole_0),X0))
% 15.19/2.50      | k2_relat_1(sK6) = k1_xboole_0 ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_16395,c_13213]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_22625,plain,
% 15.19/2.50      ( sK0(k2_relat_1(sK6),k2_zfmisc_1(sK1(sK6,k1_xboole_0),k1_xboole_0)) = k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),k1_xboole_0)))
% 15.19/2.50      | k2_relat_1(sK6) = k1_xboole_0 ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_3,c_17100]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_22699,plain,
% 15.19/2.50      ( k2_relat_1(sK6) = k1_xboole_0
% 15.19/2.50      | r2_hidden(k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),k1_xboole_0))),k2_relat_1(sK6)) = iProver_top
% 15.19/2.50      | r1_tarski(k2_relat_1(sK6),k2_zfmisc_1(sK1(sK6,k1_xboole_0),k1_xboole_0)) = iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_22625,c_1315]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_13230,plain,
% 15.19/2.50      ( k2_relat_1(sK6) = k1_xboole_0
% 15.19/2.50      | r1_tarski(k2_relat_1(sK6),k2_zfmisc_1(sK1(sK6,k1_xboole_0),k1_xboole_0)) != iProver_top ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_13213]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_22981,plain,
% 15.19/2.50      ( r2_hidden(k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),k1_xboole_0))),k2_relat_1(sK6)) = iProver_top
% 15.19/2.50      | k2_relat_1(sK6) = k1_xboole_0 ),
% 15.19/2.50      inference(global_propositional_subsumption,
% 15.19/2.50                [status(thm)],
% 15.19/2.50                [c_22699,c_13230]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_22982,plain,
% 15.19/2.50      ( k2_relat_1(sK6) = k1_xboole_0
% 15.19/2.50      | r2_hidden(k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),k1_xboole_0))),k2_relat_1(sK6)) = iProver_top ),
% 15.19/2.50      inference(renaming,[status(thm)],[c_22981]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_22986,plain,
% 15.19/2.50      ( k2_relat_1(sK6) = k1_xboole_0
% 15.19/2.50      | r2_hidden(k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),k1_xboole_0))),X0) = iProver_top
% 15.19/2.50      | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_22982,c_1314]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_23065,plain,
% 15.19/2.50      ( k2_relat_1(sK6) = k1_xboole_0
% 15.19/2.50      | r1_tarski(k2_relat_1(sK6),k2_zfmisc_1(k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),k1_xboole_0))),X0)) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_22986,c_1313]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_23107,plain,
% 15.19/2.50      ( k2_relat_1(sK6) = k1_xboole_0
% 15.19/2.50      | r1_tarski(k2_relat_1(sK6),k2_zfmisc_1(sK0(k2_relat_1(sK6),k1_xboole_0),X0)) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_17854,c_23065]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_23117,plain,
% 15.19/2.50      ( k2_relat_1(sK6) = k1_xboole_0
% 15.19/2.50      | r1_tarski(k2_relat_1(sK6),k2_zfmisc_1(sK0(k2_relat_1(sK6),k1_xboole_0),k1_xboole_0)) != iProver_top ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_23107]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_27411,plain,
% 15.19/2.50      ( r2_hidden(k1_funct_1(sK6,sK3(sK6,sK0(k2_relat_1(sK6),k1_xboole_0))),k2_relat_1(sK6)) = iProver_top ),
% 15.19/2.50      inference(global_propositional_subsumption,
% 15.19/2.50                [status(thm)],
% 15.19/2.50                [c_26868,c_1715,c_4523,c_23117,c_26394]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_27416,plain,
% 15.19/2.50      ( r2_hidden(k1_funct_1(sK6,sK3(sK6,sK0(k2_relat_1(sK6),k1_xboole_0))),X0) = iProver_top
% 15.19/2.50      | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_27411,c_1314]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_27431,plain,
% 15.19/2.50      ( r1_tarski(k2_relat_1(sK6),k2_zfmisc_1(k1_funct_1(sK6,sK3(sK6,sK0(k2_relat_1(sK6),k1_xboole_0))),X0)) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_27416,c_1313]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_27932,plain,
% 15.19/2.50      ( r1_tarski(k2_relat_1(sK6),k2_zfmisc_1(sK0(k2_relat_1(sK6),k1_xboole_0),X0)) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_11813,c_27431]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_36841,plain,
% 15.19/2.50      ( r1_tarski(sK5,k2_zfmisc_1(sK0(k2_relat_1(sK6),k1_xboole_0),X0)) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_18001,c_27932]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_37249,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK7(sK0(sK5,k2_zfmisc_1(sK0(k2_relat_1(sK6),k1_xboole_0),X0)))) = sK0(sK5,k2_zfmisc_1(sK0(k2_relat_1(sK6),k1_xboole_0),X0)) ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_1709,c_36841]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_44334,plain,
% 15.19/2.50      ( sK0(sK5,k2_zfmisc_1(sK0(k2_relat_1(sK6),k1_xboole_0),k1_xboole_0)) = k1_funct_1(sK6,sK7(sK0(sK5,k1_xboole_0))) ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_3,c_37249]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_44356,plain,
% 15.19/2.50      ( r2_hidden(k1_funct_1(sK6,sK7(sK0(sK5,k1_xboole_0))),k2_zfmisc_1(sK0(k2_relat_1(sK6),k1_xboole_0),k1_xboole_0)) != iProver_top
% 15.19/2.50      | r1_tarski(sK5,k2_zfmisc_1(sK0(k2_relat_1(sK6),k1_xboole_0),k1_xboole_0)) = iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_44334,c_1316]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_18003,plain,
% 15.19/2.50      ( r1_tarski(k2_relat_1(sK6),X0) = iProver_top
% 15.19/2.50      | r1_tarski(sK5,k2_zfmisc_1(sK0(k2_relat_1(sK6),X0),X1)) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_16392,c_1313]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_18024,plain,
% 15.19/2.50      ( r1_tarski(k2_relat_1(sK6),k1_xboole_0) = iProver_top
% 15.19/2.50      | r1_tarski(sK5,k2_zfmisc_1(sK0(k2_relat_1(sK6),k1_xboole_0),k1_xboole_0)) != iProver_top ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_18003]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_46161,plain,
% 15.19/2.50      ( r2_hidden(k1_funct_1(sK6,sK7(sK0(sK5,k1_xboole_0))),k2_zfmisc_1(sK0(k2_relat_1(sK6),k1_xboole_0),k1_xboole_0)) != iProver_top ),
% 15.19/2.50      inference(global_propositional_subsumption,
% 15.19/2.50                [status(thm)],
% 15.19/2.50                [c_44356,c_18024,c_26394]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_46170,plain,
% 15.19/2.50      ( r2_hidden(k1_funct_1(sK6,sK7(sK0(sK5,k1_xboole_0))),k1_xboole_0) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_3,c_46161]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_46721,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 15.19/2.50      | r2_hidden(sK0(sK5,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_14784,c_46170]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_1714,plain,
% 15.19/2.50      ( r1_tarski(k1_xboole_0,X0) ),
% 15.19/2.50      inference(predicate_to_equality_rev,[status(thm)],[c_1710]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_1716,plain,
% 15.19/2.50      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_1714]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_2048,plain,
% 15.19/2.50      ( r2_hidden(sK1(sK6,sK5),sK5)
% 15.19/2.50      | ~ v1_relat_1(sK6)
% 15.19/2.50      | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 15.19/2.50      | k2_relat_1(sK6) = sK5 ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_660]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_2050,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 15.19/2.50      | k2_relat_1(sK6) = sK5
% 15.19/2.50      | r2_hidden(sK1(sK6,sK5),sK5) = iProver_top
% 15.19/2.50      | v1_relat_1(sK6) != iProver_top ),
% 15.19/2.50      inference(predicate_to_equality,[status(thm)],[c_2048]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_3040,plain,
% 15.19/2.50      ( ~ r2_hidden(sK1(sK6,sK5),sK5)
% 15.19/2.50      | r2_hidden(sK7(sK1(sK6,sK5)),sK4) ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_28]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_3041,plain,
% 15.19/2.50      ( r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
% 15.19/2.50      | r2_hidden(sK7(sK1(sK6,sK5)),sK4) = iProver_top ),
% 15.19/2.50      inference(predicate_to_equality,[status(thm)],[c_3040]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_3039,plain,
% 15.19/2.50      ( ~ r2_hidden(sK1(sK6,sK5),sK5)
% 15.19/2.50      | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5) ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_27]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_3043,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
% 15.19/2.50      | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top ),
% 15.19/2.50      inference(predicate_to_equality,[status(thm)],[c_3039]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_1437,plain,
% 15.19/2.50      ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
% 15.19/2.50      inference(equality_resolution,[status(thm)],[c_474]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_4910,plain,
% 15.19/2.50      ( k1_relat_1(sK6) = sK4 | sK5 = k1_xboole_0 ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_848,c_1437]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_6346,plain,
% 15.19/2.50      ( ~ r1_tarski(k1_relat_1(sK6),k1_xboole_0) ),
% 15.19/2.50      inference(predicate_to_equality_rev,[status(thm)],[c_6344]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_10600,plain,
% 15.19/2.50      ( sK1(sK6,sK5) = sK1(sK6,sK5) ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_997]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_17459,plain,
% 15.19/2.50      ( sK7(sK1(sK6,sK5)) = sK7(sK1(sK6,sK5)) ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_997]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_18185,plain,
% 15.19/2.50      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 15.19/2.50      | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_18001,c_2798]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_18480,plain,
% 15.19/2.50      ( r1_tarski(k1_relat_1(sK6),X0) = iProver_top
% 15.19/2.50      | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_1315,c_18185]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_18517,plain,
% 15.19/2.50      ( r1_tarski(k1_relat_1(sK6),X0) | ~ r1_tarski(sK5,k1_xboole_0) ),
% 15.19/2.50      inference(predicate_to_equality_rev,[status(thm)],[c_18480]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_18519,plain,
% 15.19/2.50      ( r1_tarski(k1_relat_1(sK6),k1_xboole_0)
% 15.19/2.50      | ~ r1_tarski(sK5,k1_xboole_0) ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_18517]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_19437,plain,
% 15.19/2.50      ( ~ r1_tarski(X0,X1) | r1_tarski(sK5,X1) | sK5 != X0 ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_999]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_19439,plain,
% 15.19/2.50      ( r1_tarski(sK5,k1_xboole_0)
% 15.19/2.50      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 15.19/2.50      | sK5 != k1_xboole_0 ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_19437]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_6938,plain,
% 15.19/2.50      ( sK1(sK6,sK5) != X0
% 15.19/2.50      | sK1(sK6,sK5) = k1_funct_1(sK6,X1)
% 15.19/2.50      | k1_funct_1(sK6,X1) != X0 ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_998]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_10599,plain,
% 15.19/2.50      ( sK1(sK6,sK5) != sK1(sK6,sK5)
% 15.19/2.50      | sK1(sK6,sK5) = k1_funct_1(sK6,X0)
% 15.19/2.50      | k1_funct_1(sK6,X0) != sK1(sK6,sK5) ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_6938]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_24992,plain,
% 15.19/2.50      ( sK1(sK6,sK5) != sK1(sK6,sK5)
% 15.19/2.50      | sK1(sK6,sK5) = k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
% 15.19/2.50      | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) != sK1(sK6,sK5) ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_10599]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_11,plain,
% 15.19/2.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 15.19/2.50      | ~ r2_hidden(sK1(X1,X2),X2)
% 15.19/2.50      | ~ v1_funct_1(X1)
% 15.19/2.50      | ~ v1_relat_1(X1)
% 15.19/2.50      | sK1(X1,X2) != k1_funct_1(X1,X0)
% 15.19/2.50      | k2_relat_1(X1) = X2 ),
% 15.19/2.50      inference(cnf_transformation,[],[f60]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_722,plain,
% 15.19/2.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 15.19/2.50      | ~ r2_hidden(sK1(X1,X2),X2)
% 15.19/2.50      | ~ v1_relat_1(X1)
% 15.19/2.50      | sK1(X1,X2) != k1_funct_1(X1,X0)
% 15.19/2.50      | k2_relat_1(X1) = X2
% 15.19/2.50      | sK6 != X1 ),
% 15.19/2.50      inference(resolution_lifted,[status(thm)],[c_11,c_31]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_723,plain,
% 15.19/2.50      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 15.19/2.50      | ~ r2_hidden(sK1(sK6,X1),X1)
% 15.19/2.50      | ~ v1_relat_1(sK6)
% 15.19/2.50      | sK1(sK6,X1) != k1_funct_1(sK6,X0)
% 15.19/2.50      | k2_relat_1(sK6) = X1 ),
% 15.19/2.50      inference(unflattening,[status(thm)],[c_722]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_3045,plain,
% 15.19/2.50      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 15.19/2.50      | ~ r2_hidden(sK1(sK6,sK5),sK5)
% 15.19/2.50      | ~ v1_relat_1(sK6)
% 15.19/2.50      | sK1(sK6,sK5) != k1_funct_1(sK6,X0)
% 15.19/2.50      | k2_relat_1(sK6) = sK5 ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_723]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_37996,plain,
% 15.19/2.50      ( ~ r2_hidden(sK1(sK6,sK5),sK5)
% 15.19/2.50      | ~ r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6))
% 15.19/2.50      | ~ v1_relat_1(sK6)
% 15.19/2.50      | sK1(sK6,sK5) != k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
% 15.19/2.50      | k2_relat_1(sK6) = sK5 ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_3045]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_37997,plain,
% 15.19/2.50      ( sK1(sK6,sK5) != k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
% 15.19/2.50      | k2_relat_1(sK6) = sK5
% 15.19/2.50      | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
% 15.19/2.50      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top
% 15.19/2.50      | v1_relat_1(sK6) != iProver_top ),
% 15.19/2.50      inference(predicate_to_equality,[status(thm)],[c_37996]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_1000,plain,
% 15.19/2.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.19/2.50      theory(equality) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_6928,plain,
% 15.19/2.50      ( r2_hidden(X0,X1)
% 15.19/2.50      | ~ r2_hidden(sK7(sK1(sK6,sK5)),sK4)
% 15.19/2.50      | X0 != sK7(sK1(sK6,sK5))
% 15.19/2.50      | X1 != sK4 ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_1000]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_17458,plain,
% 15.19/2.50      ( r2_hidden(sK7(sK1(sK6,sK5)),X0)
% 15.19/2.50      | ~ r2_hidden(sK7(sK1(sK6,sK5)),sK4)
% 15.19/2.50      | X0 != sK4
% 15.19/2.50      | sK7(sK1(sK6,sK5)) != sK7(sK1(sK6,sK5)) ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_6928]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_44718,plain,
% 15.19/2.50      ( r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6))
% 15.19/2.50      | ~ r2_hidden(sK7(sK1(sK6,sK5)),sK4)
% 15.19/2.50      | sK7(sK1(sK6,sK5)) != sK7(sK1(sK6,sK5))
% 15.19/2.50      | k1_relat_1(sK6) != sK4 ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_17458]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_44719,plain,
% 15.19/2.50      ( sK7(sK1(sK6,sK5)) != sK7(sK1(sK6,sK5))
% 15.19/2.50      | k1_relat_1(sK6) != sK4
% 15.19/2.50      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) = iProver_top
% 15.19/2.50      | r2_hidden(sK7(sK1(sK6,sK5)),sK4) != iProver_top ),
% 15.19/2.50      inference(predicate_to_equality,[status(thm)],[c_44718]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_47317,plain,
% 15.19/2.50      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5) ),
% 15.19/2.50      inference(global_propositional_subsumption,
% 15.19/2.50                [status(thm)],
% 15.19/2.50                [c_46721,c_26,c_1364,c_1396,c_1499,c_1511,c_1580,c_1697,
% 15.19/2.50                 c_1716,c_1835,c_2050,c_3041,c_3043,c_4910,c_6346,
% 15.19/2.50                 c_10600,c_17459,c_18519,c_19439,c_24992,c_37997,c_44719]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_47323,plain,
% 15.19/2.50      ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) != iProver_top
% 15.19/2.50      | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top ),
% 15.19/2.50      inference(superposition,[status(thm)],[c_47317,c_2213]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_7354,plain,
% 15.19/2.50      ( ~ r2_hidden(sK1(sK6,sK5),X0)
% 15.19/2.50      | r2_hidden(sK1(sK6,sK5),X1)
% 15.19/2.50      | ~ r1_tarski(X0,X1) ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_2]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_13810,plain,
% 15.19/2.50      ( ~ r2_hidden(sK1(sK6,sK5),X0)
% 15.19/2.50      | r2_hidden(sK1(sK6,sK5),sK5)
% 15.19/2.50      | ~ r1_tarski(X0,sK5) ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_7354]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_17755,plain,
% 15.19/2.50      ( ~ r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6))
% 15.19/2.50      | r2_hidden(sK1(sK6,sK5),sK5)
% 15.19/2.50      | ~ r1_tarski(k2_relat_1(sK6),sK5) ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_13810]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_17756,plain,
% 15.19/2.50      ( r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) != iProver_top
% 15.19/2.50      | r2_hidden(sK1(sK6,sK5),sK5) = iProver_top
% 15.19/2.50      | r1_tarski(k2_relat_1(sK6),sK5) != iProver_top ),
% 15.19/2.50      inference(predicate_to_equality,[status(thm)],[c_17755]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_1696,plain,
% 15.19/2.50      ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6))
% 15.19/2.50      | r2_hidden(sK1(sK6,sK5),sK5)
% 15.19/2.50      | ~ v1_relat_1(sK6)
% 15.19/2.50      | k2_relat_1(sK6) = sK5 ),
% 15.19/2.50      inference(instantiation,[status(thm)],[c_642]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(c_1699,plain,
% 15.19/2.50      ( k2_relat_1(sK6) = sK5
% 15.19/2.50      | r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) = iProver_top
% 15.19/2.50      | r2_hidden(sK1(sK6,sK5),sK5) = iProver_top
% 15.19/2.50      | v1_relat_1(sK6) != iProver_top ),
% 15.19/2.50      inference(predicate_to_equality,[status(thm)],[c_1696]) ).
% 15.19/2.50  
% 15.19/2.50  cnf(contradiction,plain,
% 15.19/2.50      ( $false ),
% 15.19/2.50      inference(minisat,
% 15.19/2.50                [status(thm)],
% 15.19/2.50                [c_47323,c_44719,c_37997,c_24992,c_19439,c_18519,c_17756,
% 15.19/2.50                 c_17459,c_10600,c_6346,c_4910,c_3043,c_3041,c_1835,
% 15.19/2.50                 c_1716,c_1697,c_1699,c_1694,c_1580,c_1511,c_1499,c_1396,
% 15.19/2.50                 c_1364,c_26]) ).
% 15.19/2.50  
% 15.19/2.50  
% 15.19/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.19/2.50  
% 15.19/2.50  ------                               Statistics
% 15.19/2.50  
% 15.19/2.50  ------ Selected
% 15.19/2.50  
% 15.19/2.50  total_time:                             1.554
% 15.19/2.50  
%------------------------------------------------------------------------------
