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
% DateTime   : Thu Dec  3 12:00:50 EST 2020

% Result     : Theorem 15.35s
% Output     : CNFRefutation 15.35s
% Verified   : 
% Statistics : Number of formulae       :  201 (3179 expanded)
%              Number of clauses        :  142 (1009 expanded)
%              Number of leaves         :   20 ( 817 expanded)
%              Depth                    :   25
%              Number of atoms          :  711 (17047 expanded)
%              Number of equality atoms :  380 (6316 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f36,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK6(X3)) = X3
        & r2_hidden(sK6(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
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
   => ( k2_relset_1(sK3,sK4,sK5) != sK4
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK5,X4) = X3
              & r2_hidden(X4,sK3) )
          | ~ r2_hidden(X3,sK4) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK5,sK3,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( k2_relset_1(sK3,sK4,sK5) != sK4
    & ! [X3] :
        ( ( k1_funct_1(sK5,sK6(X3)) = X3
          & r2_hidden(sK6(X3),sK3) )
        | ~ r2_hidden(X3,sK4) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f24,f36,f35])).

fof(f62,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f63,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f66,plain,(
    k2_relset_1(sK3,sK4,sK5) != sK4 ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
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

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X5)) = X5
        & r2_hidden(sK2(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) = X2
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
              ( k1_funct_1(X0,X3) != sK0(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK0(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK0(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK0(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1)
                  & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK0(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK2(X0,X5)) = X5
                    & r2_hidden(sK2(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f32,f31,f30])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK0(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f65,plain,(
    ! [X3] :
      ( k1_funct_1(sK5,sK6(X3)) = X3
      | ~ r2_hidden(X3,sK4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1)
      | r2_hidden(sK0(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,(
    ! [X3] :
      ( r2_hidden(sK6(X3),sK3)
      | ~ r2_hidden(X3,sK4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f46,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f69,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f70,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | k1_funct_1(X0,X3) != sK0(X0,X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1129,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4070,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5))
    | X0 != sK1(sK5,sK4)
    | X1 != k1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1129])).

cnf(c_10693,plain,
    ( r2_hidden(sK1(sK5,sK4),X0)
    | ~ r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5))
    | X0 != k1_relat_1(sK5)
    | sK1(sK5,sK4) != sK1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_4070])).

cnf(c_50111,plain,
    ( ~ r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5))
    | r2_hidden(sK1(sK5,sK4),sK3)
    | sK1(sK5,sK4) != sK1(sK5,sK4)
    | sK3 != k1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_10693])).

cnf(c_50115,plain,
    ( sK1(sK5,sK4) != sK1(sK5,sK4)
    | sK3 != k1_relat_1(sK5)
    | r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5)) != iProver_top
    | r2_hidden(sK1(sK5,sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50111])).

cnf(c_3773,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK6(sK0(sK5,sK4)),sK3)
    | X0 != sK6(sK0(sK5,sK4))
    | X1 != sK3 ),
    inference(instantiation,[status(thm)],[c_1129])).

cnf(c_4402,plain,
    ( r2_hidden(sK6(sK0(sK5,sK4)),X0)
    | ~ r2_hidden(sK6(sK0(sK5,sK4)),sK3)
    | X0 != sK3
    | sK6(sK0(sK5,sK4)) != sK6(sK0(sK5,sK4)) ),
    inference(instantiation,[status(thm)],[c_3773])).

cnf(c_49947,plain,
    ( r2_hidden(sK6(sK0(sK5,sK4)),k1_relat_1(sK5))
    | ~ r2_hidden(sK6(sK0(sK5,sK4)),sK3)
    | sK6(sK0(sK5,sK4)) != sK6(sK0(sK5,sK4))
    | k1_relat_1(sK5) != sK3 ),
    inference(instantiation,[status(thm)],[c_4402])).

cnf(c_49950,plain,
    ( sK6(sK0(sK5,sK4)) != sK6(sK0(sK5,sK4))
    | k1_relat_1(sK5) != sK3
    | r2_hidden(sK6(sK0(sK5,sK4)),k1_relat_1(sK5)) = iProver_top
    | r2_hidden(sK6(sK0(sK5,sK4)),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49947])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_725,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_726,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_725])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_728,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_726,c_26])).

cnf(c_1721,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1725,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2147,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1721,c_1725])).

cnf(c_2596,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_728,c_2147])).

cnf(c_23,negated_conjecture,
    ( k2_relset_1(sK3,sK4,sK5) != sK4 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1853,plain,
    ( ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),sK4)
    | ~ r1_tarski(sK4,k2_relset_1(sK3,sK4,sK5))
    | k2_relset_1(sK3,sK4,sK5) = sK4 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1854,plain,
    ( k2_relset_1(sK3,sK4,sK5) = sK4
    | r1_tarski(k2_relset_1(sK3,sK4,sK5),sK4) != iProver_top
    | r1_tarski(sK4,k2_relset_1(sK3,sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1853])).

cnf(c_1122,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_1953,plain,
    ( ~ r1_tarski(X0,k2_relset_1(sK3,sK4,sK5))
    | r1_tarski(sK4,k2_relset_1(sK3,sK4,sK5))
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1122])).

cnf(c_1954,plain,
    ( sK4 != X0
    | r1_tarski(X0,k2_relset_1(sK3,sK4,sK5)) != iProver_top
    | r1_tarski(sK4,k2_relset_1(sK3,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1953])).

cnf(c_1956,plain,
    ( sK4 != k1_xboole_0
    | r1_tarski(sK4,k2_relset_1(sK3,sK4,sK5)) = iProver_top
    | r1_tarski(k1_xboole_0,k2_relset_1(sK3,sK4,sK5)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1954])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2107,plain,
    ( r1_tarski(k1_xboole_0,k2_relset_1(sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2110,plain,
    ( r1_tarski(k1_xboole_0,k2_relset_1(sK3,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2107])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1726,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1728,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2274,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relset_1(X1,X2,X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1726,c_1728])).

cnf(c_4427,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1721,c_2274])).

cnf(c_6622,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2596,c_23,c_1854,c_1956,c_2110,c_4427])).

cnf(c_8,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK0(X0,X1),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_397,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK0(X0,X1),X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_28])).

cnf(c_398,plain,
    ( r2_hidden(sK1(sK5,X0),k1_relat_1(sK5))
    | r2_hidden(sK0(sK5,X0),X0)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) = X0 ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_1720,plain,
    ( k2_relat_1(sK5) = X0
    | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
    | r2_hidden(sK0(sK5,X0),X0) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_31,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_399,plain,
    ( k2_relat_1(sK5) = X0
    | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
    | r2_hidden(sK0(sK5,X0),X0) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1816,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1817,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1816])).

cnf(c_4282,plain,
    ( r2_hidden(sK0(sK5,X0),X0) = iProver_top
    | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
    | k2_relat_1(sK5) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1720,c_31,c_399,c_1817])).

cnf(c_4283,plain,
    ( k2_relat_1(sK5) = X0
    | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
    | r2_hidden(sK0(sK5,X0),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_4282])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | k1_funct_1(sK5,sK6(X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1723,plain,
    ( k1_funct_1(sK5,sK6(X0)) = X0
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4286,plain,
    ( k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4)
    | k2_relat_1(sK5) = sK4
    | r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4283,c_1723])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1724,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2141,plain,
    ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1721,c_1724])).

cnf(c_2369,plain,
    ( k2_relat_1(sK5) != sK4 ),
    inference(superposition,[status(thm)],[c_2141,c_23])).

cnf(c_6057,plain,
    ( k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4)
    | r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4286,c_2369])).

cnf(c_6624,plain,
    ( k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4)
    | r2_hidden(sK1(sK5,sK4),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6622,c_6057])).

cnf(c_2816,plain,
    ( ~ r2_hidden(sK0(sK5,sK4),sK4)
    | k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_6627,plain,
    ( r2_hidden(sK1(sK5,sK4),sK3)
    | k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6624])).

cnf(c_7,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_415,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1)
    | k2_relat_1(X0) = X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_28])).

cnf(c_416,plain,
    ( r2_hidden(sK0(sK5,X0),X0)
    | ~ v1_relat_1(sK5)
    | k1_funct_1(sK5,sK1(sK5,X0)) = sK0(sK5,X0)
    | k2_relat_1(sK5) = X0 ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_1719,plain,
    ( k1_funct_1(sK5,sK1(sK5,X0)) = sK0(sK5,X0)
    | k2_relat_1(sK5) = X0
    | r2_hidden(sK0(sK5,X0),X0) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_416])).

cnf(c_417,plain,
    ( k1_funct_1(sK5,sK1(sK5,X0)) = sK0(sK5,X0)
    | k2_relat_1(sK5) = X0
    | r2_hidden(sK0(sK5,X0),X0) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_416])).

cnf(c_3834,plain,
    ( r2_hidden(sK0(sK5,X0),X0) = iProver_top
    | k2_relat_1(sK5) = X0
    | k1_funct_1(sK5,sK1(sK5,X0)) = sK0(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1719,c_31,c_417,c_1817])).

cnf(c_3835,plain,
    ( k1_funct_1(sK5,sK1(sK5,X0)) = sK0(sK5,X0)
    | k2_relat_1(sK5) = X0
    | r2_hidden(sK0(sK5,X0),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_3834])).

cnf(c_3838,plain,
    ( k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4)
    | k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4)
    | k2_relat_1(sK5) = sK4 ),
    inference(superposition,[status(thm)],[c_3835,c_1723])).

cnf(c_6146,plain,
    ( k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4)
    | k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3838,c_2369])).

cnf(c_6147,plain,
    ( k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4)
    | k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_6146])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_376,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_28])).

cnf(c_377,plain,
    ( ~ v1_funct_2(sK5,X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k1_funct_1(sK5,X2),X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_755,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k1_funct_1(sK5,X0),X2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK5 != sK5
    | sK4 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_377])).

cnf(c_756,plain,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(k1_funct_1(sK5,X0),sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_755])).

cnf(c_760,plain,
    ( r2_hidden(k1_funct_1(sK5,X0),sK4)
    | ~ r2_hidden(X0,sK3)
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_756,c_26])).

cnf(c_761,plain,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(k1_funct_1(sK5,X0),sK4)
    | k1_xboole_0 = sK4 ),
    inference(renaming,[status(thm)],[c_760])).

cnf(c_1711,plain,
    ( k1_xboole_0 = sK4
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_761])).

cnf(c_6150,plain,
    ( k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4)
    | sK4 = k1_xboole_0
    | r2_hidden(sK0(sK5,sK4),sK4) = iProver_top
    | r2_hidden(sK6(sK0(sK5,sK4)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6147,c_1711])).

cnf(c_25,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(sK6(X0),sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2817,plain,
    ( ~ r2_hidden(sK0(sK5,sK4),sK4)
    | r2_hidden(sK6(sK0(sK5,sK4)),sK3) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2818,plain,
    ( r2_hidden(sK0(sK5,sK4),sK4) != iProver_top
    | r2_hidden(sK6(sK0(sK5,sK4)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2817])).

cnf(c_19,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_736,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k1_funct_1(sK5,X0),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X1 != X4
    | X2 != X5
    | k1_relset_1(X4,X5,X3) != X4
    | sK5 != X3
    | k1_xboole_0 = X5
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_377])).

cnf(c_737,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k1_funct_1(sK5,X0),X2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,sK5) != X1
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_736])).

cnf(c_1712,plain,
    ( k1_relset_1(X0,X1,sK5) != X0
    | k1_xboole_0 = X1
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X2),X1) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_737])).

cnf(c_2063,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_728,c_1712])).

cnf(c_5362,plain,
    ( r2_hidden(k1_funct_1(sK5,X0),sK4) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2063,c_31,c_23,c_1854,c_1956,c_2110,c_4427])).

cnf(c_5363,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_5362])).

cnf(c_6148,plain,
    ( k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4)
    | r2_hidden(sK0(sK5,sK4),sK4) = iProver_top
    | r2_hidden(sK6(sK0(sK5,sK4)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6147,c_5363])).

cnf(c_2432,plain,
    ( r2_hidden(sK0(sK5,sK4),sK4)
    | ~ v1_relat_1(sK5)
    | k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4)
    | k2_relat_1(sK5) = sK4 ),
    inference(instantiation,[status(thm)],[c_416])).

cnf(c_2436,plain,
    ( k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4)
    | k2_relat_1(sK5) = sK4
    | r2_hidden(sK0(sK5,sK4),sK4) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2432])).

cnf(c_21892,plain,
    ( r2_hidden(sK0(sK5,sK4),sK4) = iProver_top
    | k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6148,c_31,c_1817,c_2369,c_2436])).

cnf(c_21893,plain,
    ( k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4)
    | r2_hidden(sK0(sK5,sK4),sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_21892])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_463,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_28])).

cnf(c_464,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_463])).

cnf(c_1716,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_464])).

cnf(c_1841,plain,
    ( r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))
    | ~ r2_hidden(X0,k1_relat_1(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_464,c_26,c_1816])).

cnf(c_1842,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) ),
    inference(renaming,[status(thm)],[c_1841])).

cnf(c_1843,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1842])).

cnf(c_2952,plain,
    ( r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1716,c_1843])).

cnf(c_2953,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2952])).

cnf(c_6149,plain,
    ( k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4)
    | r2_hidden(sK0(sK5,sK4),k2_relat_1(sK5)) = iProver_top
    | r2_hidden(sK6(sK0(sK5,sK4)),k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6147,c_2953])).

cnf(c_1121,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2814,plain,
    ( sK0(sK5,X0) != X1
    | sK0(sK5,X0) = k1_funct_1(sK5,X2)
    | k1_funct_1(sK5,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_1121])).

cnf(c_3954,plain,
    ( sK0(sK5,X0) != sK0(sK5,X0)
    | sK0(sK5,X0) = k1_funct_1(sK5,X1)
    | k1_funct_1(sK5,X1) != sK0(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_2814])).

cnf(c_5886,plain,
    ( sK0(sK5,sK4) != sK0(sK5,sK4)
    | sK0(sK5,sK4) = k1_funct_1(sK5,sK6(sK0(sK5,sK4)))
    | k1_funct_1(sK5,sK6(sK0(sK5,sK4))) != sK0(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_3954])).

cnf(c_1120,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3955,plain,
    ( sK0(sK5,X0) = sK0(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_1120])).

cnf(c_7956,plain,
    ( sK0(sK5,sK4) = sK0(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_3955])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(sK0(X1,X2),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | sK0(X1,X2) != k1_funct_1(X1,X0)
    | k2_relat_1(X1) = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_478,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(sK0(X1,X2),X2)
    | ~ v1_relat_1(X1)
    | sK0(X1,X2) != k1_funct_1(X1,X0)
    | k2_relat_1(X1) = X2
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_28])).

cnf(c_479,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | ~ r2_hidden(sK0(sK5,X1),X1)
    | ~ v1_relat_1(sK5)
    | sK0(sK5,X1) != k1_funct_1(sK5,X0)
    | k2_relat_1(sK5) = X1 ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_10471,plain,
    ( ~ r2_hidden(sK0(sK5,sK4),sK4)
    | ~ r2_hidden(sK6(sK0(sK5,sK4)),k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | sK0(sK5,sK4) != k1_funct_1(sK5,sK6(sK0(sK5,sK4)))
    | k2_relat_1(sK5) = sK4 ),
    inference(instantiation,[status(thm)],[c_479])).

cnf(c_10472,plain,
    ( sK0(sK5,sK4) != k1_funct_1(sK5,sK6(sK0(sK5,sK4)))
    | k2_relat_1(sK5) = sK4
    | r2_hidden(sK0(sK5,sK4),sK4) != iProver_top
    | r2_hidden(sK6(sK0(sK5,sK4)),k1_relat_1(sK5)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10471])).

cnf(c_22249,plain,
    ( k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4)
    | r2_hidden(sK6(sK0(sK5,sK4)),k1_relat_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6149,c_31,c_1817,c_2369,c_3838,c_5886,c_7956,c_10472,c_21893])).

cnf(c_22253,plain,
    ( k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4)
    | r2_hidden(sK6(sK0(sK5,sK4)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6622,c_22249])).

cnf(c_22779,plain,
    ( k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6150,c_2818,c_21893,c_22253])).

cnf(c_22781,plain,
    ( r2_hidden(sK1(sK5,sK4),sK3) != iProver_top
    | r2_hidden(sK0(sK5,sK4),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_22779,c_5363])).

cnf(c_22785,plain,
    ( ~ r2_hidden(sK1(sK5,sK4),sK3)
    | r2_hidden(sK0(sK5,sK4),sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_22781])).

cnf(c_30793,plain,
    ( k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6624,c_2816,c_6627,c_22785])).

cnf(c_2061,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1121])).

cnf(c_4188,plain,
    ( X0 != k1_relset_1(sK3,sK4,sK5)
    | sK3 = X0
    | sK3 != k1_relset_1(sK3,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2061])).

cnf(c_24176,plain,
    ( k1_relat_1(sK5) != k1_relset_1(sK3,sK4,sK5)
    | sK3 != k1_relset_1(sK3,sK4,sK5)
    | sK3 = k1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_4188])).

cnf(c_5239,plain,
    ( X0 != X1
    | X0 = k1_relset_1(sK3,sK4,sK5)
    | k1_relset_1(sK3,sK4,sK5) != X1 ),
    inference(instantiation,[status(thm)],[c_1121])).

cnf(c_13115,plain,
    ( X0 = k1_relset_1(sK3,sK4,sK5)
    | X0 != k1_relat_1(sK5)
    | k1_relset_1(sK3,sK4,sK5) != k1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_5239])).

cnf(c_19073,plain,
    ( k1_relset_1(sK3,sK4,sK5) != k1_relat_1(sK5)
    | k1_relat_1(sK5) = k1_relset_1(sK3,sK4,sK5)
    | k1_relat_1(sK5) != k1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_13115])).

cnf(c_10694,plain,
    ( sK1(sK5,sK4) = sK1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_1120])).

cnf(c_5055,plain,
    ( k1_relat_1(sK5) = k1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1120])).

cnf(c_4403,plain,
    ( sK6(sK0(sK5,sK4)) = sK6(sK0(sK5,sK4)) ),
    inference(instantiation,[status(thm)],[c_1120])).

cnf(c_2200,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2061])).

cnf(c_2640,plain,
    ( k1_relset_1(sK3,sK4,sK5) != sK3
    | sK3 = k1_relset_1(sK3,sK4,sK5)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2200])).

cnf(c_2433,plain,
    ( r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5))
    | r2_hidden(sK0(sK5,sK4),sK4)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) = sK4 ),
    inference(instantiation,[status(thm)],[c_398])).

cnf(c_2434,plain,
    ( k2_relat_1(sK5) = sK4
    | r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5)) = iProver_top
    | r2_hidden(sK0(sK5,sK4),sK4) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2433])).

cnf(c_2060,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1120])).

cnf(c_2054,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1120])).

cnf(c_1864,plain,
    ( sK4 != X0
    | sK4 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1121])).

cnf(c_2053,plain,
    ( sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1864])).

cnf(c_1898,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_50115,c_49950,c_30793,c_24176,c_22781,c_19073,c_10694,c_10472,c_7956,c_5886,c_5055,c_4427,c_4403,c_2818,c_2640,c_2596,c_2434,c_2369,c_2110,c_2060,c_2054,c_2053,c_1956,c_1898,c_1854,c_1817,c_728,c_23,c_31,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:53:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 15.35/2.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.35/2.48  
% 15.35/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.35/2.48  
% 15.35/2.48  ------  iProver source info
% 15.35/2.48  
% 15.35/2.48  git: date: 2020-06-30 10:37:57 +0100
% 15.35/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.35/2.48  git: non_committed_changes: false
% 15.35/2.48  git: last_make_outside_of_git: false
% 15.35/2.48  
% 15.35/2.48  ------ 
% 15.35/2.48  ------ Parsing...
% 15.35/2.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.35/2.48  
% 15.35/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 15.35/2.48  
% 15.35/2.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.35/2.48  
% 15.35/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.35/2.48  ------ Proving...
% 15.35/2.48  ------ Problem Properties 
% 15.35/2.48  
% 15.35/2.48  
% 15.35/2.48  clauses                                 24
% 15.35/2.48  conjectures                             4
% 15.35/2.48  EPR                                     3
% 15.35/2.48  Horn                                    18
% 15.35/2.48  unary                                   4
% 15.35/2.48  binary                                  9
% 15.35/2.48  lits                                    62
% 15.35/2.48  lits eq                                 21
% 15.35/2.48  fd_pure                                 0
% 15.35/2.48  fd_pseudo                               0
% 15.35/2.48  fd_cond                                 4
% 15.35/2.48  fd_pseudo_cond                          1
% 15.35/2.48  AC symbols                              0
% 15.35/2.48  
% 15.35/2.48  ------ Input Options Time Limit: Unbounded
% 15.35/2.48  
% 15.35/2.48  
% 15.35/2.48  ------ 
% 15.35/2.48  Current options:
% 15.35/2.48  ------ 
% 15.35/2.48  
% 15.35/2.48  
% 15.35/2.48  
% 15.35/2.48  
% 15.35/2.48  ------ Proving...
% 15.35/2.48  
% 15.35/2.48  
% 15.35/2.48  % SZS status Theorem for theBenchmark.p
% 15.35/2.48  
% 15.35/2.48  % SZS output start CNFRefutation for theBenchmark.p
% 15.35/2.48  
% 15.35/2.48  fof(f9,axiom,(
% 15.35/2.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 15.35/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.35/2.48  
% 15.35/2.48  fof(f19,plain,(
% 15.35/2.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.35/2.48    inference(ennf_transformation,[],[f9])).
% 15.35/2.48  
% 15.35/2.48  fof(f20,plain,(
% 15.35/2.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.35/2.48    inference(flattening,[],[f19])).
% 15.35/2.48  
% 15.35/2.48  fof(f34,plain,(
% 15.35/2.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.35/2.48    inference(nnf_transformation,[],[f20])).
% 15.35/2.48  
% 15.35/2.48  fof(f54,plain,(
% 15.35/2.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.35/2.48    inference(cnf_transformation,[],[f34])).
% 15.35/2.48  
% 15.35/2.48  fof(f11,conjecture,(
% 15.35/2.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 15.35/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.35/2.48  
% 15.35/2.48  fof(f12,negated_conjecture,(
% 15.35/2.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 15.35/2.48    inference(negated_conjecture,[],[f11])).
% 15.35/2.48  
% 15.35/2.48  fof(f23,plain,(
% 15.35/2.48    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 15.35/2.48    inference(ennf_transformation,[],[f12])).
% 15.35/2.48  
% 15.35/2.48  fof(f24,plain,(
% 15.35/2.48    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 15.35/2.48    inference(flattening,[],[f23])).
% 15.35/2.48  
% 15.35/2.48  fof(f36,plain,(
% 15.35/2.48    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK6(X3)) = X3 & r2_hidden(sK6(X3),X0)))) )),
% 15.35/2.48    introduced(choice_axiom,[])).
% 15.35/2.48  
% 15.35/2.48  fof(f35,plain,(
% 15.35/2.48    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK3,sK4,sK5) != sK4 & ! [X3] : (? [X4] : (k1_funct_1(sK5,X4) = X3 & r2_hidden(X4,sK3)) | ~r2_hidden(X3,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 15.35/2.48    introduced(choice_axiom,[])).
% 15.35/2.48  
% 15.35/2.48  fof(f37,plain,(
% 15.35/2.48    k2_relset_1(sK3,sK4,sK5) != sK4 & ! [X3] : ((k1_funct_1(sK5,sK6(X3)) = X3 & r2_hidden(sK6(X3),sK3)) | ~r2_hidden(X3,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 15.35/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f24,f36,f35])).
% 15.35/2.48  
% 15.35/2.48  fof(f62,plain,(
% 15.35/2.48    v1_funct_2(sK5,sK3,sK4)),
% 15.35/2.48    inference(cnf_transformation,[],[f37])).
% 15.35/2.48  
% 15.35/2.48  fof(f63,plain,(
% 15.35/2.48    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 15.35/2.48    inference(cnf_transformation,[],[f37])).
% 15.35/2.48  
% 15.35/2.48  fof(f7,axiom,(
% 15.35/2.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 15.35/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.35/2.48  
% 15.35/2.48  fof(f17,plain,(
% 15.35/2.48    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.35/2.48    inference(ennf_transformation,[],[f7])).
% 15.35/2.48  
% 15.35/2.48  fof(f52,plain,(
% 15.35/2.48    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.35/2.48    inference(cnf_transformation,[],[f17])).
% 15.35/2.48  
% 15.35/2.48  fof(f66,plain,(
% 15.35/2.48    k2_relset_1(sK3,sK4,sK5) != sK4),
% 15.35/2.48    inference(cnf_transformation,[],[f37])).
% 15.35/2.48  
% 15.35/2.48  fof(f1,axiom,(
% 15.35/2.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.35/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.35/2.48  
% 15.35/2.48  fof(f25,plain,(
% 15.35/2.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.35/2.48    inference(nnf_transformation,[],[f1])).
% 15.35/2.48  
% 15.35/2.48  fof(f26,plain,(
% 15.35/2.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.35/2.48    inference(flattening,[],[f25])).
% 15.35/2.48  
% 15.35/2.48  fof(f40,plain,(
% 15.35/2.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.35/2.48    inference(cnf_transformation,[],[f26])).
% 15.35/2.48  
% 15.35/2.48  fof(f2,axiom,(
% 15.35/2.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 15.35/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.35/2.48  
% 15.35/2.48  fof(f41,plain,(
% 15.35/2.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 15.35/2.48    inference(cnf_transformation,[],[f2])).
% 15.35/2.48  
% 15.35/2.48  fof(f6,axiom,(
% 15.35/2.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 15.35/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.35/2.48  
% 15.35/2.48  fof(f16,plain,(
% 15.35/2.48    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.35/2.48    inference(ennf_transformation,[],[f6])).
% 15.35/2.48  
% 15.35/2.48  fof(f51,plain,(
% 15.35/2.48    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.35/2.48    inference(cnf_transformation,[],[f16])).
% 15.35/2.48  
% 15.35/2.48  fof(f3,axiom,(
% 15.35/2.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.35/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.35/2.48  
% 15.35/2.48  fof(f27,plain,(
% 15.35/2.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.35/2.48    inference(nnf_transformation,[],[f3])).
% 15.35/2.48  
% 15.35/2.48  fof(f42,plain,(
% 15.35/2.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.35/2.48    inference(cnf_transformation,[],[f27])).
% 15.35/2.48  
% 15.35/2.48  fof(f4,axiom,(
% 15.35/2.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 15.35/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.35/2.48  
% 15.35/2.48  fof(f13,plain,(
% 15.35/2.48    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.35/2.48    inference(ennf_transformation,[],[f4])).
% 15.35/2.48  
% 15.35/2.48  fof(f14,plain,(
% 15.35/2.48    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.35/2.48    inference(flattening,[],[f13])).
% 15.35/2.48  
% 15.35/2.48  fof(f28,plain,(
% 15.35/2.48    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.35/2.48    inference(nnf_transformation,[],[f14])).
% 15.35/2.48  
% 15.35/2.48  fof(f29,plain,(
% 15.35/2.48    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.35/2.48    inference(rectify,[],[f28])).
% 15.35/2.48  
% 15.35/2.48  fof(f32,plain,(
% 15.35/2.48    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X5)) = X5 & r2_hidden(sK2(X0,X5),k1_relat_1(X0))))),
% 15.35/2.48    introduced(choice_axiom,[])).
% 15.35/2.48  
% 15.35/2.48  fof(f31,plain,(
% 15.35/2.48    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) = X2 & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))) )),
% 15.35/2.48    introduced(choice_axiom,[])).
% 15.35/2.48  
% 15.35/2.48  fof(f30,plain,(
% 15.35/2.48    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK0(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK0(X0,X1),X1))))),
% 15.35/2.48    introduced(choice_axiom,[])).
% 15.35/2.48  
% 15.35/2.48  fof(f33,plain,(
% 15.35/2.48    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1),X1)) & ((k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK2(X0,X5)) = X5 & r2_hidden(sK2(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.35/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f32,f31,f30])).
% 15.35/2.48  
% 15.35/2.48  fof(f47,plain,(
% 15.35/2.48    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | r2_hidden(sK0(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.35/2.48    inference(cnf_transformation,[],[f33])).
% 15.35/2.48  
% 15.35/2.48  fof(f61,plain,(
% 15.35/2.48    v1_funct_1(sK5)),
% 15.35/2.48    inference(cnf_transformation,[],[f37])).
% 15.35/2.48  
% 15.35/2.48  fof(f5,axiom,(
% 15.35/2.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 15.35/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.35/2.48  
% 15.35/2.48  fof(f15,plain,(
% 15.35/2.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.35/2.48    inference(ennf_transformation,[],[f5])).
% 15.35/2.48  
% 15.35/2.48  fof(f50,plain,(
% 15.35/2.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.35/2.48    inference(cnf_transformation,[],[f15])).
% 15.35/2.48  
% 15.35/2.48  fof(f65,plain,(
% 15.35/2.48    ( ! [X3] : (k1_funct_1(sK5,sK6(X3)) = X3 | ~r2_hidden(X3,sK4)) )),
% 15.35/2.48    inference(cnf_transformation,[],[f37])).
% 15.35/2.48  
% 15.35/2.48  fof(f8,axiom,(
% 15.35/2.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 15.35/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.35/2.48  
% 15.35/2.48  fof(f18,plain,(
% 15.35/2.48    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.35/2.48    inference(ennf_transformation,[],[f8])).
% 15.35/2.48  
% 15.35/2.48  fof(f53,plain,(
% 15.35/2.48    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.35/2.48    inference(cnf_transformation,[],[f18])).
% 15.35/2.48  
% 15.35/2.48  fof(f48,plain,(
% 15.35/2.48    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1) | r2_hidden(sK0(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.35/2.48    inference(cnf_transformation,[],[f33])).
% 15.35/2.48  
% 15.35/2.48  fof(f10,axiom,(
% 15.35/2.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 15.35/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.35/2.48  
% 15.35/2.48  fof(f21,plain,(
% 15.35/2.48    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 15.35/2.48    inference(ennf_transformation,[],[f10])).
% 15.35/2.48  
% 15.35/2.48  fof(f22,plain,(
% 15.35/2.48    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 15.35/2.48    inference(flattening,[],[f21])).
% 15.35/2.48  
% 15.35/2.48  fof(f60,plain,(
% 15.35/2.48    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 15.35/2.48    inference(cnf_transformation,[],[f22])).
% 15.35/2.48  
% 15.35/2.48  fof(f64,plain,(
% 15.35/2.48    ( ! [X3] : (r2_hidden(sK6(X3),sK3) | ~r2_hidden(X3,sK4)) )),
% 15.35/2.48    inference(cnf_transformation,[],[f37])).
% 15.35/2.48  
% 15.35/2.48  fof(f56,plain,(
% 15.35/2.48    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.35/2.48    inference(cnf_transformation,[],[f34])).
% 15.35/2.48  
% 15.35/2.48  fof(f46,plain,(
% 15.35/2.48    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.35/2.48    inference(cnf_transformation,[],[f33])).
% 15.35/2.48  
% 15.35/2.48  fof(f69,plain,(
% 15.35/2.48    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.35/2.48    inference(equality_resolution,[],[f46])).
% 15.35/2.48  
% 15.35/2.48  fof(f70,plain,(
% 15.35/2.48    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.35/2.48    inference(equality_resolution,[],[f69])).
% 15.35/2.48  
% 15.35/2.48  fof(f49,plain,(
% 15.35/2.48    ( ! [X0,X3,X1] : (k2_relat_1(X0) = X1 | k1_funct_1(X0,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(sK0(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.35/2.48    inference(cnf_transformation,[],[f33])).
% 15.35/2.48  
% 15.35/2.48  cnf(c_1129,plain,
% 15.35/2.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.35/2.48      theory(equality) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_4070,plain,
% 15.35/2.48      ( r2_hidden(X0,X1)
% 15.35/2.48      | ~ r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5))
% 15.35/2.48      | X0 != sK1(sK5,sK4)
% 15.35/2.48      | X1 != k1_relat_1(sK5) ),
% 15.35/2.48      inference(instantiation,[status(thm)],[c_1129]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_10693,plain,
% 15.35/2.48      ( r2_hidden(sK1(sK5,sK4),X0)
% 15.35/2.48      | ~ r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5))
% 15.35/2.48      | X0 != k1_relat_1(sK5)
% 15.35/2.48      | sK1(sK5,sK4) != sK1(sK5,sK4) ),
% 15.35/2.48      inference(instantiation,[status(thm)],[c_4070]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_50111,plain,
% 15.35/2.48      ( ~ r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5))
% 15.35/2.48      | r2_hidden(sK1(sK5,sK4),sK3)
% 15.35/2.48      | sK1(sK5,sK4) != sK1(sK5,sK4)
% 15.35/2.48      | sK3 != k1_relat_1(sK5) ),
% 15.35/2.48      inference(instantiation,[status(thm)],[c_10693]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_50115,plain,
% 15.35/2.48      ( sK1(sK5,sK4) != sK1(sK5,sK4)
% 15.35/2.48      | sK3 != k1_relat_1(sK5)
% 15.35/2.48      | r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5)) != iProver_top
% 15.35/2.48      | r2_hidden(sK1(sK5,sK4),sK3) = iProver_top ),
% 15.35/2.48      inference(predicate_to_equality,[status(thm)],[c_50111]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_3773,plain,
% 15.35/2.48      ( r2_hidden(X0,X1)
% 15.35/2.48      | ~ r2_hidden(sK6(sK0(sK5,sK4)),sK3)
% 15.35/2.48      | X0 != sK6(sK0(sK5,sK4))
% 15.35/2.48      | X1 != sK3 ),
% 15.35/2.48      inference(instantiation,[status(thm)],[c_1129]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_4402,plain,
% 15.35/2.48      ( r2_hidden(sK6(sK0(sK5,sK4)),X0)
% 15.35/2.48      | ~ r2_hidden(sK6(sK0(sK5,sK4)),sK3)
% 15.35/2.48      | X0 != sK3
% 15.35/2.48      | sK6(sK0(sK5,sK4)) != sK6(sK0(sK5,sK4)) ),
% 15.35/2.48      inference(instantiation,[status(thm)],[c_3773]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_49947,plain,
% 15.35/2.48      ( r2_hidden(sK6(sK0(sK5,sK4)),k1_relat_1(sK5))
% 15.35/2.48      | ~ r2_hidden(sK6(sK0(sK5,sK4)),sK3)
% 15.35/2.48      | sK6(sK0(sK5,sK4)) != sK6(sK0(sK5,sK4))
% 15.35/2.48      | k1_relat_1(sK5) != sK3 ),
% 15.35/2.48      inference(instantiation,[status(thm)],[c_4402]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_49950,plain,
% 15.35/2.48      ( sK6(sK0(sK5,sK4)) != sK6(sK0(sK5,sK4))
% 15.35/2.48      | k1_relat_1(sK5) != sK3
% 15.35/2.48      | r2_hidden(sK6(sK0(sK5,sK4)),k1_relat_1(sK5)) = iProver_top
% 15.35/2.48      | r2_hidden(sK6(sK0(sK5,sK4)),sK3) != iProver_top ),
% 15.35/2.48      inference(predicate_to_equality,[status(thm)],[c_49947]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_21,plain,
% 15.35/2.48      ( ~ v1_funct_2(X0,X1,X2)
% 15.35/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.35/2.48      | k1_relset_1(X1,X2,X0) = X1
% 15.35/2.48      | k1_xboole_0 = X2 ),
% 15.35/2.48      inference(cnf_transformation,[],[f54]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_27,negated_conjecture,
% 15.35/2.48      ( v1_funct_2(sK5,sK3,sK4) ),
% 15.35/2.48      inference(cnf_transformation,[],[f62]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_725,plain,
% 15.35/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.35/2.48      | k1_relset_1(X1,X2,X0) = X1
% 15.35/2.48      | sK5 != X0
% 15.35/2.48      | sK4 != X2
% 15.35/2.48      | sK3 != X1
% 15.35/2.48      | k1_xboole_0 = X2 ),
% 15.35/2.48      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_726,plain,
% 15.35/2.48      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 15.35/2.48      | k1_relset_1(sK3,sK4,sK5) = sK3
% 15.35/2.48      | k1_xboole_0 = sK4 ),
% 15.35/2.48      inference(unflattening,[status(thm)],[c_725]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_26,negated_conjecture,
% 15.35/2.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 15.35/2.48      inference(cnf_transformation,[],[f63]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_728,plain,
% 15.35/2.48      ( k1_relset_1(sK3,sK4,sK5) = sK3 | k1_xboole_0 = sK4 ),
% 15.35/2.48      inference(global_propositional_subsumption,
% 15.35/2.48                [status(thm)],
% 15.35/2.48                [c_726,c_26]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_1721,plain,
% 15.35/2.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 15.35/2.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_14,plain,
% 15.35/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.35/2.48      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 15.35/2.48      inference(cnf_transformation,[],[f52]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_1725,plain,
% 15.35/2.48      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 15.35/2.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.35/2.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_2147,plain,
% 15.35/2.48      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 15.35/2.48      inference(superposition,[status(thm)],[c_1721,c_1725]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_2596,plain,
% 15.35/2.48      ( k1_relat_1(sK5) = sK3 | sK4 = k1_xboole_0 ),
% 15.35/2.48      inference(superposition,[status(thm)],[c_728,c_2147]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_23,negated_conjecture,
% 15.35/2.48      ( k2_relset_1(sK3,sK4,sK5) != sK4 ),
% 15.35/2.48      inference(cnf_transformation,[],[f66]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_0,plain,
% 15.35/2.48      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 15.35/2.48      inference(cnf_transformation,[],[f40]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_1853,plain,
% 15.35/2.48      ( ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),sK4)
% 15.35/2.48      | ~ r1_tarski(sK4,k2_relset_1(sK3,sK4,sK5))
% 15.35/2.48      | k2_relset_1(sK3,sK4,sK5) = sK4 ),
% 15.35/2.48      inference(instantiation,[status(thm)],[c_0]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_1854,plain,
% 15.35/2.48      ( k2_relset_1(sK3,sK4,sK5) = sK4
% 15.35/2.48      | r1_tarski(k2_relset_1(sK3,sK4,sK5),sK4) != iProver_top
% 15.35/2.48      | r1_tarski(sK4,k2_relset_1(sK3,sK4,sK5)) != iProver_top ),
% 15.35/2.48      inference(predicate_to_equality,[status(thm)],[c_1853]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_1122,plain,
% 15.35/2.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 15.35/2.48      theory(equality) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_1953,plain,
% 15.35/2.48      ( ~ r1_tarski(X0,k2_relset_1(sK3,sK4,sK5))
% 15.35/2.48      | r1_tarski(sK4,k2_relset_1(sK3,sK4,sK5))
% 15.35/2.48      | sK4 != X0 ),
% 15.35/2.48      inference(instantiation,[status(thm)],[c_1122]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_1954,plain,
% 15.35/2.48      ( sK4 != X0
% 15.35/2.48      | r1_tarski(X0,k2_relset_1(sK3,sK4,sK5)) != iProver_top
% 15.35/2.48      | r1_tarski(sK4,k2_relset_1(sK3,sK4,sK5)) = iProver_top ),
% 15.35/2.48      inference(predicate_to_equality,[status(thm)],[c_1953]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_1956,plain,
% 15.35/2.48      ( sK4 != k1_xboole_0
% 15.35/2.48      | r1_tarski(sK4,k2_relset_1(sK3,sK4,sK5)) = iProver_top
% 15.35/2.48      | r1_tarski(k1_xboole_0,k2_relset_1(sK3,sK4,sK5)) != iProver_top ),
% 15.35/2.48      inference(instantiation,[status(thm)],[c_1954]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_3,plain,
% 15.35/2.48      ( r1_tarski(k1_xboole_0,X0) ),
% 15.35/2.48      inference(cnf_transformation,[],[f41]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_2107,plain,
% 15.35/2.48      ( r1_tarski(k1_xboole_0,k2_relset_1(sK3,sK4,sK5)) ),
% 15.35/2.48      inference(instantiation,[status(thm)],[c_3]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_2110,plain,
% 15.35/2.48      ( r1_tarski(k1_xboole_0,k2_relset_1(sK3,sK4,sK5)) = iProver_top ),
% 15.35/2.48      inference(predicate_to_equality,[status(thm)],[c_2107]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_13,plain,
% 15.35/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.35/2.48      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 15.35/2.48      inference(cnf_transformation,[],[f51]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_1726,plain,
% 15.35/2.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.35/2.48      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 15.35/2.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_5,plain,
% 15.35/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.35/2.48      inference(cnf_transformation,[],[f42]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_1728,plain,
% 15.35/2.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.35/2.48      | r1_tarski(X0,X1) = iProver_top ),
% 15.35/2.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_2274,plain,
% 15.35/2.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.35/2.48      | r1_tarski(k2_relset_1(X1,X2,X0),X2) = iProver_top ),
% 15.35/2.48      inference(superposition,[status(thm)],[c_1726,c_1728]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_4427,plain,
% 15.35/2.48      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),sK4) = iProver_top ),
% 15.35/2.48      inference(superposition,[status(thm)],[c_1721,c_2274]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_6622,plain,
% 15.35/2.48      ( k1_relat_1(sK5) = sK3 ),
% 15.35/2.48      inference(global_propositional_subsumption,
% 15.35/2.48                [status(thm)],
% 15.35/2.48                [c_2596,c_23,c_1854,c_1956,c_2110,c_4427]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_8,plain,
% 15.35/2.48      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 15.35/2.48      | r2_hidden(sK0(X0,X1),X1)
% 15.35/2.48      | ~ v1_relat_1(X0)
% 15.35/2.48      | ~ v1_funct_1(X0)
% 15.35/2.48      | k2_relat_1(X0) = X1 ),
% 15.35/2.48      inference(cnf_transformation,[],[f47]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_28,negated_conjecture,
% 15.35/2.48      ( v1_funct_1(sK5) ),
% 15.35/2.48      inference(cnf_transformation,[],[f61]) ).
% 15.35/2.48  
% 15.35/2.48  cnf(c_397,plain,
% 15.35/2.48      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 15.35/2.48      | r2_hidden(sK0(X0,X1),X1)
% 15.35/2.49      | ~ v1_relat_1(X0)
% 15.35/2.49      | k2_relat_1(X0) = X1
% 15.35/2.49      | sK5 != X0 ),
% 15.35/2.49      inference(resolution_lifted,[status(thm)],[c_8,c_28]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_398,plain,
% 15.35/2.49      ( r2_hidden(sK1(sK5,X0),k1_relat_1(sK5))
% 15.35/2.49      | r2_hidden(sK0(sK5,X0),X0)
% 15.35/2.49      | ~ v1_relat_1(sK5)
% 15.35/2.49      | k2_relat_1(sK5) = X0 ),
% 15.35/2.49      inference(unflattening,[status(thm)],[c_397]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_1720,plain,
% 15.35/2.49      ( k2_relat_1(sK5) = X0
% 15.35/2.49      | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
% 15.35/2.49      | r2_hidden(sK0(sK5,X0),X0) = iProver_top
% 15.35/2.49      | v1_relat_1(sK5) != iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_398]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_31,plain,
% 15.35/2.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_399,plain,
% 15.35/2.49      ( k2_relat_1(sK5) = X0
% 15.35/2.49      | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
% 15.35/2.49      | r2_hidden(sK0(sK5,X0),X0) = iProver_top
% 15.35/2.49      | v1_relat_1(sK5) != iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_398]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_12,plain,
% 15.35/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.35/2.49      | v1_relat_1(X0) ),
% 15.35/2.49      inference(cnf_transformation,[],[f50]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_1816,plain,
% 15.35/2.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 15.35/2.49      | v1_relat_1(sK5) ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_12]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_1817,plain,
% 15.35/2.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 15.35/2.49      | v1_relat_1(sK5) = iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_1816]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_4282,plain,
% 15.35/2.49      ( r2_hidden(sK0(sK5,X0),X0) = iProver_top
% 15.35/2.49      | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
% 15.35/2.49      | k2_relat_1(sK5) = X0 ),
% 15.35/2.49      inference(global_propositional_subsumption,
% 15.35/2.49                [status(thm)],
% 15.35/2.49                [c_1720,c_31,c_399,c_1817]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_4283,plain,
% 15.35/2.49      ( k2_relat_1(sK5) = X0
% 15.35/2.49      | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
% 15.35/2.49      | r2_hidden(sK0(sK5,X0),X0) = iProver_top ),
% 15.35/2.49      inference(renaming,[status(thm)],[c_4282]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_24,negated_conjecture,
% 15.35/2.49      ( ~ r2_hidden(X0,sK4) | k1_funct_1(sK5,sK6(X0)) = X0 ),
% 15.35/2.49      inference(cnf_transformation,[],[f65]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_1723,plain,
% 15.35/2.49      ( k1_funct_1(sK5,sK6(X0)) = X0 | r2_hidden(X0,sK4) != iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_4286,plain,
% 15.35/2.49      ( k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4)
% 15.35/2.49      | k2_relat_1(sK5) = sK4
% 15.35/2.49      | r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5)) = iProver_top ),
% 15.35/2.49      inference(superposition,[status(thm)],[c_4283,c_1723]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_15,plain,
% 15.35/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.35/2.49      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 15.35/2.49      inference(cnf_transformation,[],[f53]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_1724,plain,
% 15.35/2.49      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 15.35/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_2141,plain,
% 15.35/2.49      ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
% 15.35/2.49      inference(superposition,[status(thm)],[c_1721,c_1724]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_2369,plain,
% 15.35/2.49      ( k2_relat_1(sK5) != sK4 ),
% 15.35/2.49      inference(superposition,[status(thm)],[c_2141,c_23]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_6057,plain,
% 15.35/2.49      ( k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4)
% 15.35/2.49      | r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5)) = iProver_top ),
% 15.35/2.49      inference(global_propositional_subsumption,
% 15.35/2.49                [status(thm)],
% 15.35/2.49                [c_4286,c_2369]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_6624,plain,
% 15.35/2.49      ( k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4)
% 15.35/2.49      | r2_hidden(sK1(sK5,sK4),sK3) = iProver_top ),
% 15.35/2.49      inference(superposition,[status(thm)],[c_6622,c_6057]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_2816,plain,
% 15.35/2.49      ( ~ r2_hidden(sK0(sK5,sK4),sK4)
% 15.35/2.49      | k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4) ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_24]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_6627,plain,
% 15.35/2.49      ( r2_hidden(sK1(sK5,sK4),sK3)
% 15.35/2.49      | k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4) ),
% 15.35/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_6624]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_7,plain,
% 15.35/2.49      ( r2_hidden(sK0(X0,X1),X1)
% 15.35/2.49      | ~ v1_relat_1(X0)
% 15.35/2.49      | ~ v1_funct_1(X0)
% 15.35/2.49      | k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1)
% 15.35/2.49      | k2_relat_1(X0) = X1 ),
% 15.35/2.49      inference(cnf_transformation,[],[f48]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_415,plain,
% 15.35/2.49      ( r2_hidden(sK0(X0,X1),X1)
% 15.35/2.49      | ~ v1_relat_1(X0)
% 15.35/2.49      | k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1)
% 15.35/2.49      | k2_relat_1(X0) = X1
% 15.35/2.49      | sK5 != X0 ),
% 15.35/2.49      inference(resolution_lifted,[status(thm)],[c_7,c_28]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_416,plain,
% 15.35/2.49      ( r2_hidden(sK0(sK5,X0),X0)
% 15.35/2.49      | ~ v1_relat_1(sK5)
% 15.35/2.49      | k1_funct_1(sK5,sK1(sK5,X0)) = sK0(sK5,X0)
% 15.35/2.49      | k2_relat_1(sK5) = X0 ),
% 15.35/2.49      inference(unflattening,[status(thm)],[c_415]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_1719,plain,
% 15.35/2.49      ( k1_funct_1(sK5,sK1(sK5,X0)) = sK0(sK5,X0)
% 15.35/2.49      | k2_relat_1(sK5) = X0
% 15.35/2.49      | r2_hidden(sK0(sK5,X0),X0) = iProver_top
% 15.35/2.49      | v1_relat_1(sK5) != iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_416]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_417,plain,
% 15.35/2.49      ( k1_funct_1(sK5,sK1(sK5,X0)) = sK0(sK5,X0)
% 15.35/2.49      | k2_relat_1(sK5) = X0
% 15.35/2.49      | r2_hidden(sK0(sK5,X0),X0) = iProver_top
% 15.35/2.49      | v1_relat_1(sK5) != iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_416]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_3834,plain,
% 15.35/2.49      ( r2_hidden(sK0(sK5,X0),X0) = iProver_top
% 15.35/2.49      | k2_relat_1(sK5) = X0
% 15.35/2.49      | k1_funct_1(sK5,sK1(sK5,X0)) = sK0(sK5,X0) ),
% 15.35/2.49      inference(global_propositional_subsumption,
% 15.35/2.49                [status(thm)],
% 15.35/2.49                [c_1719,c_31,c_417,c_1817]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_3835,plain,
% 15.35/2.49      ( k1_funct_1(sK5,sK1(sK5,X0)) = sK0(sK5,X0)
% 15.35/2.49      | k2_relat_1(sK5) = X0
% 15.35/2.49      | r2_hidden(sK0(sK5,X0),X0) = iProver_top ),
% 15.35/2.49      inference(renaming,[status(thm)],[c_3834]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_3838,plain,
% 15.35/2.49      ( k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4)
% 15.35/2.49      | k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4)
% 15.35/2.49      | k2_relat_1(sK5) = sK4 ),
% 15.35/2.49      inference(superposition,[status(thm)],[c_3835,c_1723]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_6146,plain,
% 15.35/2.49      ( k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4)
% 15.35/2.49      | k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4) ),
% 15.35/2.49      inference(global_propositional_subsumption,
% 15.35/2.49                [status(thm)],
% 15.35/2.49                [c_3838,c_2369]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_6147,plain,
% 15.35/2.49      ( k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4)
% 15.35/2.49      | k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4) ),
% 15.35/2.49      inference(renaming,[status(thm)],[c_6146]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_22,plain,
% 15.35/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 15.35/2.49      | ~ r2_hidden(X3,X1)
% 15.35/2.49      | r2_hidden(k1_funct_1(X0,X3),X2)
% 15.35/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.35/2.49      | ~ v1_funct_1(X0)
% 15.35/2.49      | k1_xboole_0 = X2 ),
% 15.35/2.49      inference(cnf_transformation,[],[f60]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_376,plain,
% 15.35/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 15.35/2.49      | ~ r2_hidden(X3,X1)
% 15.35/2.49      | r2_hidden(k1_funct_1(X0,X3),X2)
% 15.35/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.35/2.49      | sK5 != X0
% 15.35/2.49      | k1_xboole_0 = X2 ),
% 15.35/2.49      inference(resolution_lifted,[status(thm)],[c_22,c_28]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_377,plain,
% 15.35/2.49      ( ~ v1_funct_2(sK5,X0,X1)
% 15.35/2.49      | ~ r2_hidden(X2,X0)
% 15.35/2.49      | r2_hidden(k1_funct_1(sK5,X2),X1)
% 15.35/2.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.35/2.49      | k1_xboole_0 = X1 ),
% 15.35/2.49      inference(unflattening,[status(thm)],[c_376]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_755,plain,
% 15.35/2.49      ( ~ r2_hidden(X0,X1)
% 15.35/2.49      | r2_hidden(k1_funct_1(sK5,X0),X2)
% 15.35/2.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.35/2.49      | sK5 != sK5
% 15.35/2.49      | sK4 != X2
% 15.35/2.49      | sK3 != X1
% 15.35/2.49      | k1_xboole_0 = X2 ),
% 15.35/2.49      inference(resolution_lifted,[status(thm)],[c_27,c_377]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_756,plain,
% 15.35/2.49      ( ~ r2_hidden(X0,sK3)
% 15.35/2.49      | r2_hidden(k1_funct_1(sK5,X0),sK4)
% 15.35/2.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 15.35/2.49      | k1_xboole_0 = sK4 ),
% 15.35/2.49      inference(unflattening,[status(thm)],[c_755]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_760,plain,
% 15.35/2.49      ( r2_hidden(k1_funct_1(sK5,X0),sK4)
% 15.35/2.49      | ~ r2_hidden(X0,sK3)
% 15.35/2.49      | k1_xboole_0 = sK4 ),
% 15.35/2.49      inference(global_propositional_subsumption,
% 15.35/2.49                [status(thm)],
% 15.35/2.49                [c_756,c_26]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_761,plain,
% 15.35/2.49      ( ~ r2_hidden(X0,sK3)
% 15.35/2.49      | r2_hidden(k1_funct_1(sK5,X0),sK4)
% 15.35/2.49      | k1_xboole_0 = sK4 ),
% 15.35/2.49      inference(renaming,[status(thm)],[c_760]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_1711,plain,
% 15.35/2.49      ( k1_xboole_0 = sK4
% 15.35/2.49      | r2_hidden(X0,sK3) != iProver_top
% 15.35/2.49      | r2_hidden(k1_funct_1(sK5,X0),sK4) = iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_761]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_6150,plain,
% 15.35/2.49      ( k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4)
% 15.35/2.49      | sK4 = k1_xboole_0
% 15.35/2.49      | r2_hidden(sK0(sK5,sK4),sK4) = iProver_top
% 15.35/2.49      | r2_hidden(sK6(sK0(sK5,sK4)),sK3) != iProver_top ),
% 15.35/2.49      inference(superposition,[status(thm)],[c_6147,c_1711]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_25,negated_conjecture,
% 15.35/2.49      ( ~ r2_hidden(X0,sK4) | r2_hidden(sK6(X0),sK3) ),
% 15.35/2.49      inference(cnf_transformation,[],[f64]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_2817,plain,
% 15.35/2.49      ( ~ r2_hidden(sK0(sK5,sK4),sK4)
% 15.35/2.49      | r2_hidden(sK6(sK0(sK5,sK4)),sK3) ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_25]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_2818,plain,
% 15.35/2.49      ( r2_hidden(sK0(sK5,sK4),sK4) != iProver_top
% 15.35/2.49      | r2_hidden(sK6(sK0(sK5,sK4)),sK3) = iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_2817]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_19,plain,
% 15.35/2.49      ( v1_funct_2(X0,X1,X2)
% 15.35/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.35/2.49      | k1_relset_1(X1,X2,X0) != X1
% 15.35/2.49      | k1_xboole_0 = X2 ),
% 15.35/2.49      inference(cnf_transformation,[],[f56]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_736,plain,
% 15.35/2.49      ( ~ r2_hidden(X0,X1)
% 15.35/2.49      | r2_hidden(k1_funct_1(sK5,X0),X2)
% 15.35/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 15.35/2.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.35/2.49      | X1 != X4
% 15.35/2.49      | X2 != X5
% 15.35/2.49      | k1_relset_1(X4,X5,X3) != X4
% 15.35/2.49      | sK5 != X3
% 15.35/2.49      | k1_xboole_0 = X5
% 15.35/2.49      | k1_xboole_0 = X2 ),
% 15.35/2.49      inference(resolution_lifted,[status(thm)],[c_19,c_377]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_737,plain,
% 15.35/2.49      ( ~ r2_hidden(X0,X1)
% 15.35/2.49      | r2_hidden(k1_funct_1(sK5,X0),X2)
% 15.35/2.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.35/2.49      | k1_relset_1(X1,X2,sK5) != X1
% 15.35/2.49      | k1_xboole_0 = X2 ),
% 15.35/2.49      inference(unflattening,[status(thm)],[c_736]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_1712,plain,
% 15.35/2.49      ( k1_relset_1(X0,X1,sK5) != X0
% 15.35/2.49      | k1_xboole_0 = X1
% 15.35/2.49      | r2_hidden(X2,X0) != iProver_top
% 15.35/2.49      | r2_hidden(k1_funct_1(sK5,X2),X1) = iProver_top
% 15.35/2.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_737]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_2063,plain,
% 15.35/2.49      ( sK4 = k1_xboole_0
% 15.35/2.49      | r2_hidden(X0,sK3) != iProver_top
% 15.35/2.49      | r2_hidden(k1_funct_1(sK5,X0),sK4) = iProver_top
% 15.35/2.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
% 15.35/2.49      inference(superposition,[status(thm)],[c_728,c_1712]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_5362,plain,
% 15.35/2.49      ( r2_hidden(k1_funct_1(sK5,X0),sK4) = iProver_top
% 15.35/2.49      | r2_hidden(X0,sK3) != iProver_top ),
% 15.35/2.49      inference(global_propositional_subsumption,
% 15.35/2.49                [status(thm)],
% 15.35/2.49                [c_2063,c_31,c_23,c_1854,c_1956,c_2110,c_4427]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_5363,plain,
% 15.35/2.49      ( r2_hidden(X0,sK3) != iProver_top
% 15.35/2.49      | r2_hidden(k1_funct_1(sK5,X0),sK4) = iProver_top ),
% 15.35/2.49      inference(renaming,[status(thm)],[c_5362]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_6148,plain,
% 15.35/2.49      ( k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4)
% 15.35/2.49      | r2_hidden(sK0(sK5,sK4),sK4) = iProver_top
% 15.35/2.49      | r2_hidden(sK6(sK0(sK5,sK4)),sK3) != iProver_top ),
% 15.35/2.49      inference(superposition,[status(thm)],[c_6147,c_5363]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_2432,plain,
% 15.35/2.49      ( r2_hidden(sK0(sK5,sK4),sK4)
% 15.35/2.49      | ~ v1_relat_1(sK5)
% 15.35/2.49      | k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4)
% 15.35/2.49      | k2_relat_1(sK5) = sK4 ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_416]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_2436,plain,
% 15.35/2.49      ( k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4)
% 15.35/2.49      | k2_relat_1(sK5) = sK4
% 15.35/2.49      | r2_hidden(sK0(sK5,sK4),sK4) = iProver_top
% 15.35/2.49      | v1_relat_1(sK5) != iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_2432]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_21892,plain,
% 15.35/2.49      ( r2_hidden(sK0(sK5,sK4),sK4) = iProver_top
% 15.35/2.49      | k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4) ),
% 15.35/2.49      inference(global_propositional_subsumption,
% 15.35/2.49                [status(thm)],
% 15.35/2.49                [c_6148,c_31,c_1817,c_2369,c_2436]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_21893,plain,
% 15.35/2.49      ( k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4)
% 15.35/2.49      | r2_hidden(sK0(sK5,sK4),sK4) = iProver_top ),
% 15.35/2.49      inference(renaming,[status(thm)],[c_21892]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_9,plain,
% 15.35/2.49      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 15.35/2.49      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 15.35/2.49      | ~ v1_relat_1(X1)
% 15.35/2.49      | ~ v1_funct_1(X1) ),
% 15.35/2.49      inference(cnf_transformation,[],[f70]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_463,plain,
% 15.35/2.49      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 15.35/2.49      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 15.35/2.49      | ~ v1_relat_1(X1)
% 15.35/2.49      | sK5 != X1 ),
% 15.35/2.49      inference(resolution_lifted,[status(thm)],[c_9,c_28]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_464,plain,
% 15.35/2.49      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 15.35/2.49      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))
% 15.35/2.49      | ~ v1_relat_1(sK5) ),
% 15.35/2.49      inference(unflattening,[status(thm)],[c_463]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_1716,plain,
% 15.35/2.49      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 15.35/2.49      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
% 15.35/2.49      | v1_relat_1(sK5) != iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_464]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_1841,plain,
% 15.35/2.49      ( r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))
% 15.35/2.49      | ~ r2_hidden(X0,k1_relat_1(sK5)) ),
% 15.35/2.49      inference(global_propositional_subsumption,
% 15.35/2.49                [status(thm)],
% 15.35/2.49                [c_464,c_26,c_1816]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_1842,plain,
% 15.35/2.49      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 15.35/2.49      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) ),
% 15.35/2.49      inference(renaming,[status(thm)],[c_1841]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_1843,plain,
% 15.35/2.49      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 15.35/2.49      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_1842]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_2952,plain,
% 15.35/2.49      ( r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
% 15.35/2.49      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 15.35/2.49      inference(global_propositional_subsumption,
% 15.35/2.49                [status(thm)],
% 15.35/2.49                [c_1716,c_1843]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_2953,plain,
% 15.35/2.49      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 15.35/2.49      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top ),
% 15.35/2.49      inference(renaming,[status(thm)],[c_2952]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_6149,plain,
% 15.35/2.49      ( k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4)
% 15.35/2.49      | r2_hidden(sK0(sK5,sK4),k2_relat_1(sK5)) = iProver_top
% 15.35/2.49      | r2_hidden(sK6(sK0(sK5,sK4)),k1_relat_1(sK5)) != iProver_top ),
% 15.35/2.49      inference(superposition,[status(thm)],[c_6147,c_2953]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_1121,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_2814,plain,
% 15.35/2.49      ( sK0(sK5,X0) != X1
% 15.35/2.49      | sK0(sK5,X0) = k1_funct_1(sK5,X2)
% 15.35/2.49      | k1_funct_1(sK5,X2) != X1 ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_1121]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_3954,plain,
% 15.35/2.49      ( sK0(sK5,X0) != sK0(sK5,X0)
% 15.35/2.49      | sK0(sK5,X0) = k1_funct_1(sK5,X1)
% 15.35/2.49      | k1_funct_1(sK5,X1) != sK0(sK5,X0) ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_2814]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_5886,plain,
% 15.35/2.49      ( sK0(sK5,sK4) != sK0(sK5,sK4)
% 15.35/2.49      | sK0(sK5,sK4) = k1_funct_1(sK5,sK6(sK0(sK5,sK4)))
% 15.35/2.49      | k1_funct_1(sK5,sK6(sK0(sK5,sK4))) != sK0(sK5,sK4) ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_3954]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_1120,plain,( X0 = X0 ),theory(equality) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_3955,plain,
% 15.35/2.49      ( sK0(sK5,X0) = sK0(sK5,X0) ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_1120]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_7956,plain,
% 15.35/2.49      ( sK0(sK5,sK4) = sK0(sK5,sK4) ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_3955]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_6,plain,
% 15.35/2.49      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 15.35/2.49      | ~ r2_hidden(sK0(X1,X2),X2)
% 15.35/2.49      | ~ v1_relat_1(X1)
% 15.35/2.49      | ~ v1_funct_1(X1)
% 15.35/2.49      | sK0(X1,X2) != k1_funct_1(X1,X0)
% 15.35/2.49      | k2_relat_1(X1) = X2 ),
% 15.35/2.49      inference(cnf_transformation,[],[f49]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_478,plain,
% 15.35/2.49      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 15.35/2.49      | ~ r2_hidden(sK0(X1,X2),X2)
% 15.35/2.49      | ~ v1_relat_1(X1)
% 15.35/2.49      | sK0(X1,X2) != k1_funct_1(X1,X0)
% 15.35/2.49      | k2_relat_1(X1) = X2
% 15.35/2.49      | sK5 != X1 ),
% 15.35/2.49      inference(resolution_lifted,[status(thm)],[c_6,c_28]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_479,plain,
% 15.35/2.49      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 15.35/2.49      | ~ r2_hidden(sK0(sK5,X1),X1)
% 15.35/2.49      | ~ v1_relat_1(sK5)
% 15.35/2.49      | sK0(sK5,X1) != k1_funct_1(sK5,X0)
% 15.35/2.49      | k2_relat_1(sK5) = X1 ),
% 15.35/2.49      inference(unflattening,[status(thm)],[c_478]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_10471,plain,
% 15.35/2.49      ( ~ r2_hidden(sK0(sK5,sK4),sK4)
% 15.35/2.49      | ~ r2_hidden(sK6(sK0(sK5,sK4)),k1_relat_1(sK5))
% 15.35/2.49      | ~ v1_relat_1(sK5)
% 15.35/2.49      | sK0(sK5,sK4) != k1_funct_1(sK5,sK6(sK0(sK5,sK4)))
% 15.35/2.49      | k2_relat_1(sK5) = sK4 ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_479]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_10472,plain,
% 15.35/2.49      ( sK0(sK5,sK4) != k1_funct_1(sK5,sK6(sK0(sK5,sK4)))
% 15.35/2.49      | k2_relat_1(sK5) = sK4
% 15.35/2.49      | r2_hidden(sK0(sK5,sK4),sK4) != iProver_top
% 15.35/2.49      | r2_hidden(sK6(sK0(sK5,sK4)),k1_relat_1(sK5)) != iProver_top
% 15.35/2.49      | v1_relat_1(sK5) != iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_10471]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_22249,plain,
% 15.35/2.49      ( k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4)
% 15.35/2.49      | r2_hidden(sK6(sK0(sK5,sK4)),k1_relat_1(sK5)) != iProver_top ),
% 15.35/2.49      inference(global_propositional_subsumption,
% 15.35/2.49                [status(thm)],
% 15.35/2.49                [c_6149,c_31,c_1817,c_2369,c_3838,c_5886,c_7956,c_10472,
% 15.35/2.49                 c_21893]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_22253,plain,
% 15.35/2.49      ( k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4)
% 15.35/2.49      | r2_hidden(sK6(sK0(sK5,sK4)),sK3) != iProver_top ),
% 15.35/2.49      inference(superposition,[status(thm)],[c_6622,c_22249]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_22779,plain,
% 15.35/2.49      ( k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4) ),
% 15.35/2.49      inference(global_propositional_subsumption,
% 15.35/2.49                [status(thm)],
% 15.35/2.49                [c_6150,c_2818,c_21893,c_22253]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_22781,plain,
% 15.35/2.49      ( r2_hidden(sK1(sK5,sK4),sK3) != iProver_top
% 15.35/2.49      | r2_hidden(sK0(sK5,sK4),sK4) = iProver_top ),
% 15.35/2.49      inference(superposition,[status(thm)],[c_22779,c_5363]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_22785,plain,
% 15.35/2.49      ( ~ r2_hidden(sK1(sK5,sK4),sK3) | r2_hidden(sK0(sK5,sK4),sK4) ),
% 15.35/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_22781]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_30793,plain,
% 15.35/2.49      ( k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4) ),
% 15.35/2.49      inference(global_propositional_subsumption,
% 15.35/2.49                [status(thm)],
% 15.35/2.49                [c_6624,c_2816,c_6627,c_22785]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_2061,plain,
% 15.35/2.49      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_1121]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_4188,plain,
% 15.35/2.49      ( X0 != k1_relset_1(sK3,sK4,sK5)
% 15.35/2.49      | sK3 = X0
% 15.35/2.49      | sK3 != k1_relset_1(sK3,sK4,sK5) ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_2061]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_24176,plain,
% 15.35/2.49      ( k1_relat_1(sK5) != k1_relset_1(sK3,sK4,sK5)
% 15.35/2.49      | sK3 != k1_relset_1(sK3,sK4,sK5)
% 15.35/2.49      | sK3 = k1_relat_1(sK5) ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_4188]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_5239,plain,
% 15.35/2.49      ( X0 != X1
% 15.35/2.49      | X0 = k1_relset_1(sK3,sK4,sK5)
% 15.35/2.49      | k1_relset_1(sK3,sK4,sK5) != X1 ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_1121]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_13115,plain,
% 15.35/2.49      ( X0 = k1_relset_1(sK3,sK4,sK5)
% 15.35/2.49      | X0 != k1_relat_1(sK5)
% 15.35/2.49      | k1_relset_1(sK3,sK4,sK5) != k1_relat_1(sK5) ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_5239]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_19073,plain,
% 15.35/2.49      ( k1_relset_1(sK3,sK4,sK5) != k1_relat_1(sK5)
% 15.35/2.49      | k1_relat_1(sK5) = k1_relset_1(sK3,sK4,sK5)
% 15.35/2.49      | k1_relat_1(sK5) != k1_relat_1(sK5) ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_13115]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_10694,plain,
% 15.35/2.49      ( sK1(sK5,sK4) = sK1(sK5,sK4) ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_1120]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_5055,plain,
% 15.35/2.49      ( k1_relat_1(sK5) = k1_relat_1(sK5) ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_1120]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_4403,plain,
% 15.35/2.49      ( sK6(sK0(sK5,sK4)) = sK6(sK0(sK5,sK4)) ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_1120]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_2200,plain,
% 15.35/2.49      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_2061]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_2640,plain,
% 15.35/2.49      ( k1_relset_1(sK3,sK4,sK5) != sK3
% 15.35/2.49      | sK3 = k1_relset_1(sK3,sK4,sK5)
% 15.35/2.49      | sK3 != sK3 ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_2200]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_2433,plain,
% 15.35/2.49      ( r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5))
% 15.35/2.49      | r2_hidden(sK0(sK5,sK4),sK4)
% 15.35/2.49      | ~ v1_relat_1(sK5)
% 15.35/2.49      | k2_relat_1(sK5) = sK4 ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_398]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_2434,plain,
% 15.35/2.49      ( k2_relat_1(sK5) = sK4
% 15.35/2.49      | r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5)) = iProver_top
% 15.35/2.49      | r2_hidden(sK0(sK5,sK4),sK4) = iProver_top
% 15.35/2.49      | v1_relat_1(sK5) != iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_2433]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_2060,plain,
% 15.35/2.49      ( sK3 = sK3 ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_1120]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_2054,plain,
% 15.35/2.49      ( sK4 = sK4 ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_1120]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_1864,plain,
% 15.35/2.49      ( sK4 != X0 | sK4 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_1121]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_2053,plain,
% 15.35/2.49      ( sK4 != sK4 | sK4 = k1_xboole_0 | k1_xboole_0 != sK4 ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_1864]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_1898,plain,
% 15.35/2.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 15.35/2.49      | k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_14]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(contradiction,plain,
% 15.35/2.49      ( $false ),
% 15.35/2.49      inference(minisat,
% 15.35/2.49                [status(thm)],
% 15.35/2.49                [c_50115,c_49950,c_30793,c_24176,c_22781,c_19073,c_10694,
% 15.35/2.49                 c_10472,c_7956,c_5886,c_5055,c_4427,c_4403,c_2818,
% 15.35/2.49                 c_2640,c_2596,c_2434,c_2369,c_2110,c_2060,c_2054,c_2053,
% 15.35/2.49                 c_1956,c_1898,c_1854,c_1817,c_728,c_23,c_31,c_26]) ).
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.35/2.49  
% 15.35/2.49  ------                               Statistics
% 15.35/2.49  
% 15.35/2.49  ------ Selected
% 15.35/2.49  
% 15.35/2.49  total_time:                             1.617
% 15.35/2.49  
%------------------------------------------------------------------------------
