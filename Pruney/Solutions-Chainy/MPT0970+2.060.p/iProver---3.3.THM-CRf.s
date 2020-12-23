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
% DateTime   : Thu Dec  3 12:00:57 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :  149 (2011 expanded)
%              Number of clauses        :   95 ( 686 expanded)
%              Number of leaves         :   15 ( 476 expanded)
%              Depth                    :   23
%              Number of atoms          :  451 (9592 expanded)
%              Number of equality atoms :  229 (3430 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f33,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK5(X3)) = X3
        & r2_hidden(sK5(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
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
   => ( k2_relset_1(sK2,sK3,sK4) != sK3
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK4,X4) = X3
              & r2_hidden(X4,sK2) )
          | ~ r2_hidden(X3,sK3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( k2_relset_1(sK2,sK3,sK4) != sK3
    & ! [X3] :
        ( ( k1_funct_1(sK4,sK5(X3)) = X3
          & r2_hidden(sK5(X3),sK2) )
        | ~ r2_hidden(X3,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f22,f33,f32])).

fof(f57,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f31,plain,(
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

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,X1) = k1_xboole_0
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f56,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f61,plain,(
    k2_relset_1(sK2,sK3,sK4) != sK3 ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
              | ~ r2_hidden(X3,X1) )
          | k2_relset_1(X0,X1,X2) != X1 )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
              | ~ r2_hidden(X3,X1) )
          | k2_relset_1(X0,X1,X2) != X1 )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ? [X5] :
              ( ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X2)
              & r2_hidden(X5,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f26])).

fof(f29,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(X6,sK1(X1,X2)),X2)
        & r2_hidden(sK1(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
     => r2_hidden(k4_tarski(sK0(X2,X3),X3),X2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(sK0(X2,X3),X3),X2)
              | ~ r2_hidden(X3,X1) )
          | k2_relset_1(X0,X1,X2) != X1 )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(X6,sK1(X1,X2)),X2)
            & r2_hidden(sK1(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f29,f28])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | r2_hidden(sK1(X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,(
    ! [X3] :
      ( r2_hidden(sK5(X3),sK2)
      | ~ r2_hidden(X3,sK3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f60,plain,(
    ! [X3] :
      ( k1_funct_1(sK4,sK5(X3)) = X3
      | ~ r2_hidden(X3,sK3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f48,plain,(
    ! [X6,X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_hidden(k4_tarski(X6,sK1(X1,X2)),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_362,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_24])).

cnf(c_363,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_586,plain,
    ( k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != sK4
    | sK3 != X1
    | sK2 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_363])).

cnf(c_587,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_586])).

cnf(c_653,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_587])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_407,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_24])).

cnf(c_408,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_1168,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_408])).

cnf(c_1382,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_653,c_1168])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_991,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_319,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = k1_xboole_0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_26])).

cnf(c_320,plain,
    ( r2_hidden(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_319])).

cnf(c_984,plain,
    ( k1_funct_1(sK4,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_320])).

cnf(c_321,plain,
    ( k1_funct_1(sK4,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_320])).

cnf(c_738,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1126,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_738])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_347,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_24])).

cnf(c_348,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_347])).

cnf(c_1121,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_348])).

cnf(c_1209,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1121])).

cnf(c_1210,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1209])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1315,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1316,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1315])).

cnf(c_1697,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) = iProver_top
    | k1_funct_1(sK4,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_984,c_321,c_1126,c_1210,c_1316])).

cnf(c_1698,plain,
    ( k1_funct_1(sK4,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1697])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_989,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1705,plain,
    ( k1_funct_1(sK4,X0) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1698,c_989])).

cnf(c_1786,plain,
    ( k1_funct_1(sK4,k1_relat_1(sK4)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_991,c_1705])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_286,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_26])).

cnf(c_287,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_986,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_287])).

cnf(c_288,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_287])).

cnf(c_1536,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_986,c_288,c_1126,c_1210,c_1316])).

cnf(c_1537,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_1536])).

cnf(c_1815,plain,
    ( r2_hidden(k4_tarski(k1_relat_1(sK4),k1_xboole_0),sK4) = iProver_top
    | r2_hidden(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1786,c_1537])).

cnf(c_1566,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ r1_tarski(k1_relat_1(sK4),X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1662,plain,
    ( ~ r2_hidden(k1_relat_1(sK4),k1_relat_1(sK4))
    | ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_1566])).

cnf(c_1664,plain,
    ( r2_hidden(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1662])).

cnf(c_1663,plain,
    ( r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1666,plain,
    ( r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1663])).

cnf(c_1864,plain,
    ( r2_hidden(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1815,c_1664,c_1666])).

cnf(c_1910,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1382,c_1864])).

cnf(c_21,negated_conjecture,
    ( k2_relset_1(sK2,sK3,sK4) != sK3 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_14,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
    | k2_relset_1(X2,X0,X1) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_449,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | k2_relset_1(X2,X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X2,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_24])).

cnf(c_450,plain,
    ( r2_hidden(sK1(X0,sK4),X0)
    | k2_relset_1(X1,X0,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_449])).

cnf(c_1179,plain,
    ( r2_hidden(sK1(sK3,sK4),sK3)
    | k2_relset_1(sK2,sK3,sK4) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_450])).

cnf(c_1180,plain,
    ( k2_relset_1(sK2,sK3,sK4) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | r2_hidden(sK1(sK3,sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1179])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(sK5(X0),sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1269,plain,
    ( ~ r2_hidden(sK1(sK3,sK4),sK3)
    | r2_hidden(sK5(sK1(sK3,sK4)),sK2) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1270,plain,
    ( r2_hidden(sK1(sK3,sK4),sK3) != iProver_top
    | r2_hidden(sK5(sK1(sK3,sK4)),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1269])).

cnf(c_980,plain,
    ( k2_relset_1(X0,X1,sK4) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | r2_hidden(sK1(X1,sK4),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_450])).

cnf(c_1713,plain,
    ( k2_relset_1(sK2,sK3,sK4) = sK3
    | r2_hidden(sK1(sK3,sK4),sK3) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_980])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_398,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_24])).

cnf(c_399,plain,
    ( k2_relset_1(X0,X1,sK4) = k2_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_1138,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_399])).

cnf(c_1714,plain,
    ( k2_relat_1(sK4) = sK3
    | r2_hidden(sK1(sK3,sK4),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1713,c_1138])).

cnf(c_1943,plain,
    ( r2_hidden(sK1(sK3,sK4),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1714,c_21,c_1126,c_1180])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK4,sK5(X0)) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_988,plain,
    ( k1_funct_1(sK4,sK5(X0)) = X0
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1949,plain,
    ( k1_funct_1(sK4,sK5(sK1(sK3,sK4))) = sK1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1943,c_988])).

cnf(c_2010,plain,
    ( r2_hidden(k4_tarski(sK5(sK1(sK3,sK4)),sK1(sK3,sK4)),sK4) = iProver_top
    | r2_hidden(sK5(sK1(sK3,sK4)),k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1949,c_1537])).

cnf(c_13,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK1(X1,X2)),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | k2_relset_1(X3,X1,X2) = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_416,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK1(X1,X2)),X2)
    | k2_relset_1(X3,X1,X2) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X3,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_417,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK1(X1,sK4)),sK4)
    | k2_relset_1(X2,X1,sK4) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_982,plain,
    ( k2_relset_1(X0,X1,sK4) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | r2_hidden(k4_tarski(X2,sK1(X1,sK4)),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_417])).

cnf(c_1552,plain,
    ( k2_relset_1(sK2,sK3,sK4) = sK3
    | r2_hidden(k4_tarski(X0,sK1(sK3,sK4)),sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_982])).

cnf(c_1553,plain,
    ( k2_relat_1(sK4) = sK3
    | r2_hidden(k4_tarski(X0,sK1(sK3,sK4)),sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1552,c_1138])).

cnf(c_1187,plain,
    ( k2_relat_1(sK4) != sK3 ),
    inference(demodulation,[status(thm)],[c_1138,c_21])).

cnf(c_1818,plain,
    ( r2_hidden(k4_tarski(X0,sK1(sK3,sK4)),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1553,c_1187])).

cnf(c_2024,plain,
    ( r2_hidden(sK5(sK1(sK3,sK4)),k1_relat_1(sK4)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2010,c_1818])).

cnf(c_2027,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK5(sK1(sK3,sK4)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1382,c_2024])).

cnf(c_2068,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1910,c_21,c_1126,c_1180,c_1270,c_2027])).

cnf(c_2072,plain,
    ( k1_funct_1(sK4,sK5(sK1(k1_xboole_0,sK4))) = sK1(k1_xboole_0,sK4) ),
    inference(demodulation,[status(thm)],[c_2068,c_1949])).

cnf(c_2026,plain,
    ( k1_funct_1(sK4,sK5(sK1(sK3,sK4))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1698,c_2024])).

cnf(c_2613,plain,
    ( k1_funct_1(sK4,sK5(sK1(k1_xboole_0,sK4))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2026,c_2068])).

cnf(c_2617,plain,
    ( sK1(k1_xboole_0,sK4) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2072,c_2613])).

cnf(c_1948,plain,
    ( r1_tarski(sK3,sK1(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1943,c_989])).

cnf(c_2267,plain,
    ( r1_tarski(k1_xboole_0,sK1(k1_xboole_0,sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1948,c_2068])).

cnf(c_2620,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2617,c_2267])).

cnf(c_86,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_88,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_86])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2620,c_88])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:44:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.01/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/0.99  
% 2.01/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.01/0.99  
% 2.01/0.99  ------  iProver source info
% 2.01/0.99  
% 2.01/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.01/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.01/0.99  git: non_committed_changes: false
% 2.01/0.99  git: last_make_outside_of_git: false
% 2.01/0.99  
% 2.01/0.99  ------ 
% 2.01/0.99  
% 2.01/0.99  ------ Input Options
% 2.01/0.99  
% 2.01/0.99  --out_options                           all
% 2.01/0.99  --tptp_safe_out                         true
% 2.01/0.99  --problem_path                          ""
% 2.01/0.99  --include_path                          ""
% 2.01/0.99  --clausifier                            res/vclausify_rel
% 2.01/0.99  --clausifier_options                    --mode clausify
% 2.01/0.99  --stdin                                 false
% 2.01/0.99  --stats_out                             all
% 2.01/0.99  
% 2.01/0.99  ------ General Options
% 2.01/0.99  
% 2.01/0.99  --fof                                   false
% 2.01/0.99  --time_out_real                         305.
% 2.01/0.99  --time_out_virtual                      -1.
% 2.01/0.99  --symbol_type_check                     false
% 2.01/0.99  --clausify_out                          false
% 2.01/0.99  --sig_cnt_out                           false
% 2.01/0.99  --trig_cnt_out                          false
% 2.01/0.99  --trig_cnt_out_tolerance                1.
% 2.01/0.99  --trig_cnt_out_sk_spl                   false
% 2.01/0.99  --abstr_cl_out                          false
% 2.01/0.99  
% 2.01/0.99  ------ Global Options
% 2.01/0.99  
% 2.01/0.99  --schedule                              default
% 2.01/0.99  --add_important_lit                     false
% 2.01/0.99  --prop_solver_per_cl                    1000
% 2.01/0.99  --min_unsat_core                        false
% 2.01/0.99  --soft_assumptions                      false
% 2.01/0.99  --soft_lemma_size                       3
% 2.01/0.99  --prop_impl_unit_size                   0
% 2.01/0.99  --prop_impl_unit                        []
% 2.01/0.99  --share_sel_clauses                     true
% 2.01/0.99  --reset_solvers                         false
% 2.01/0.99  --bc_imp_inh                            [conj_cone]
% 2.01/0.99  --conj_cone_tolerance                   3.
% 2.01/0.99  --extra_neg_conj                        none
% 2.01/0.99  --large_theory_mode                     true
% 2.01/0.99  --prolific_symb_bound                   200
% 2.01/0.99  --lt_threshold                          2000
% 2.01/0.99  --clause_weak_htbl                      true
% 2.01/0.99  --gc_record_bc_elim                     false
% 2.01/0.99  
% 2.01/0.99  ------ Preprocessing Options
% 2.01/0.99  
% 2.01/0.99  --preprocessing_flag                    true
% 2.01/0.99  --time_out_prep_mult                    0.1
% 2.01/0.99  --splitting_mode                        input
% 2.01/0.99  --splitting_grd                         true
% 2.01/0.99  --splitting_cvd                         false
% 2.01/0.99  --splitting_cvd_svl                     false
% 2.01/0.99  --splitting_nvd                         32
% 2.01/0.99  --sub_typing                            true
% 2.01/0.99  --prep_gs_sim                           true
% 2.01/0.99  --prep_unflatten                        true
% 2.01/0.99  --prep_res_sim                          true
% 2.01/0.99  --prep_upred                            true
% 2.01/0.99  --prep_sem_filter                       exhaustive
% 2.01/0.99  --prep_sem_filter_out                   false
% 2.01/0.99  --pred_elim                             true
% 2.01/0.99  --res_sim_input                         true
% 2.01/0.99  --eq_ax_congr_red                       true
% 2.01/0.99  --pure_diseq_elim                       true
% 2.01/0.99  --brand_transform                       false
% 2.01/0.99  --non_eq_to_eq                          false
% 2.01/0.99  --prep_def_merge                        true
% 2.01/0.99  --prep_def_merge_prop_impl              false
% 2.01/0.99  --prep_def_merge_mbd                    true
% 2.01/0.99  --prep_def_merge_tr_red                 false
% 2.01/0.99  --prep_def_merge_tr_cl                  false
% 2.01/0.99  --smt_preprocessing                     true
% 2.01/0.99  --smt_ac_axioms                         fast
% 2.01/0.99  --preprocessed_out                      false
% 2.01/0.99  --preprocessed_stats                    false
% 2.01/0.99  
% 2.01/0.99  ------ Abstraction refinement Options
% 2.01/0.99  
% 2.01/0.99  --abstr_ref                             []
% 2.01/0.99  --abstr_ref_prep                        false
% 2.01/0.99  --abstr_ref_until_sat                   false
% 2.01/0.99  --abstr_ref_sig_restrict                funpre
% 2.01/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.01/0.99  --abstr_ref_under                       []
% 2.01/0.99  
% 2.01/0.99  ------ SAT Options
% 2.01/0.99  
% 2.01/0.99  --sat_mode                              false
% 2.01/0.99  --sat_fm_restart_options                ""
% 2.01/0.99  --sat_gr_def                            false
% 2.01/0.99  --sat_epr_types                         true
% 2.01/0.99  --sat_non_cyclic_types                  false
% 2.01/0.99  --sat_finite_models                     false
% 2.01/0.99  --sat_fm_lemmas                         false
% 2.01/0.99  --sat_fm_prep                           false
% 2.01/0.99  --sat_fm_uc_incr                        true
% 2.01/0.99  --sat_out_model                         small
% 2.01/0.99  --sat_out_clauses                       false
% 2.01/0.99  
% 2.01/0.99  ------ QBF Options
% 2.01/0.99  
% 2.01/0.99  --qbf_mode                              false
% 2.01/0.99  --qbf_elim_univ                         false
% 2.01/0.99  --qbf_dom_inst                          none
% 2.01/0.99  --qbf_dom_pre_inst                      false
% 2.01/0.99  --qbf_sk_in                             false
% 2.01/0.99  --qbf_pred_elim                         true
% 2.01/0.99  --qbf_split                             512
% 2.01/0.99  
% 2.01/0.99  ------ BMC1 Options
% 2.01/0.99  
% 2.01/0.99  --bmc1_incremental                      false
% 2.01/0.99  --bmc1_axioms                           reachable_all
% 2.01/0.99  --bmc1_min_bound                        0
% 2.01/0.99  --bmc1_max_bound                        -1
% 2.01/0.99  --bmc1_max_bound_default                -1
% 2.01/0.99  --bmc1_symbol_reachability              true
% 2.01/0.99  --bmc1_property_lemmas                  false
% 2.01/0.99  --bmc1_k_induction                      false
% 2.01/0.99  --bmc1_non_equiv_states                 false
% 2.01/0.99  --bmc1_deadlock                         false
% 2.01/0.99  --bmc1_ucm                              false
% 2.01/0.99  --bmc1_add_unsat_core                   none
% 2.01/0.99  --bmc1_unsat_core_children              false
% 2.01/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.01/0.99  --bmc1_out_stat                         full
% 2.01/0.99  --bmc1_ground_init                      false
% 2.01/0.99  --bmc1_pre_inst_next_state              false
% 2.01/0.99  --bmc1_pre_inst_state                   false
% 2.01/0.99  --bmc1_pre_inst_reach_state             false
% 2.01/0.99  --bmc1_out_unsat_core                   false
% 2.01/0.99  --bmc1_aig_witness_out                  false
% 2.01/0.99  --bmc1_verbose                          false
% 2.01/0.99  --bmc1_dump_clauses_tptp                false
% 2.01/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.01/0.99  --bmc1_dump_file                        -
% 2.01/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.01/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.01/0.99  --bmc1_ucm_extend_mode                  1
% 2.01/0.99  --bmc1_ucm_init_mode                    2
% 2.01/0.99  --bmc1_ucm_cone_mode                    none
% 2.01/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.01/0.99  --bmc1_ucm_relax_model                  4
% 2.01/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.01/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.01/0.99  --bmc1_ucm_layered_model                none
% 2.01/0.99  --bmc1_ucm_max_lemma_size               10
% 2.01/0.99  
% 2.01/0.99  ------ AIG Options
% 2.01/0.99  
% 2.01/0.99  --aig_mode                              false
% 2.01/0.99  
% 2.01/0.99  ------ Instantiation Options
% 2.01/0.99  
% 2.01/0.99  --instantiation_flag                    true
% 2.01/0.99  --inst_sos_flag                         false
% 2.01/0.99  --inst_sos_phase                        true
% 2.01/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.01/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.01/0.99  --inst_lit_sel_side                     num_symb
% 2.01/0.99  --inst_solver_per_active                1400
% 2.01/0.99  --inst_solver_calls_frac                1.
% 2.01/0.99  --inst_passive_queue_type               priority_queues
% 2.01/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.01/0.99  --inst_passive_queues_freq              [25;2]
% 2.01/0.99  --inst_dismatching                      true
% 2.01/0.99  --inst_eager_unprocessed_to_passive     true
% 2.01/0.99  --inst_prop_sim_given                   true
% 2.01/0.99  --inst_prop_sim_new                     false
% 2.01/0.99  --inst_subs_new                         false
% 2.01/0.99  --inst_eq_res_simp                      false
% 2.01/0.99  --inst_subs_given                       false
% 2.01/0.99  --inst_orphan_elimination               true
% 2.01/0.99  --inst_learning_loop_flag               true
% 2.01/0.99  --inst_learning_start                   3000
% 2.01/0.99  --inst_learning_factor                  2
% 2.01/0.99  --inst_start_prop_sim_after_learn       3
% 2.01/0.99  --inst_sel_renew                        solver
% 2.01/0.99  --inst_lit_activity_flag                true
% 2.01/0.99  --inst_restr_to_given                   false
% 2.01/0.99  --inst_activity_threshold               500
% 2.01/0.99  --inst_out_proof                        true
% 2.01/0.99  
% 2.01/0.99  ------ Resolution Options
% 2.01/0.99  
% 2.01/0.99  --resolution_flag                       true
% 2.01/0.99  --res_lit_sel                           adaptive
% 2.01/0.99  --res_lit_sel_side                      none
% 2.01/0.99  --res_ordering                          kbo
% 2.01/0.99  --res_to_prop_solver                    active
% 2.01/0.99  --res_prop_simpl_new                    false
% 2.01/0.99  --res_prop_simpl_given                  true
% 2.01/0.99  --res_passive_queue_type                priority_queues
% 2.01/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.01/0.99  --res_passive_queues_freq               [15;5]
% 2.01/0.99  --res_forward_subs                      full
% 2.01/0.99  --res_backward_subs                     full
% 2.01/0.99  --res_forward_subs_resolution           true
% 2.01/0.99  --res_backward_subs_resolution          true
% 2.01/0.99  --res_orphan_elimination                true
% 2.01/0.99  --res_time_limit                        2.
% 2.01/0.99  --res_out_proof                         true
% 2.01/0.99  
% 2.01/0.99  ------ Superposition Options
% 2.01/0.99  
% 2.01/0.99  --superposition_flag                    true
% 2.01/0.99  --sup_passive_queue_type                priority_queues
% 2.01/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.01/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.01/0.99  --demod_completeness_check              fast
% 2.01/0.99  --demod_use_ground                      true
% 2.01/0.99  --sup_to_prop_solver                    passive
% 2.01/0.99  --sup_prop_simpl_new                    true
% 2.01/0.99  --sup_prop_simpl_given                  true
% 2.01/0.99  --sup_fun_splitting                     false
% 2.01/0.99  --sup_smt_interval                      50000
% 2.01/0.99  
% 2.01/0.99  ------ Superposition Simplification Setup
% 2.01/0.99  
% 2.01/0.99  --sup_indices_passive                   []
% 2.01/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.01/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.01/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.01/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.01/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.01/0.99  --sup_full_bw                           [BwDemod]
% 2.01/0.99  --sup_immed_triv                        [TrivRules]
% 2.01/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.01/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.01/0.99  --sup_immed_bw_main                     []
% 2.01/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.01/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.01/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.01/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.01/0.99  
% 2.01/0.99  ------ Combination Options
% 2.01/0.99  
% 2.01/0.99  --comb_res_mult                         3
% 2.01/0.99  --comb_sup_mult                         2
% 2.01/0.99  --comb_inst_mult                        10
% 2.01/0.99  
% 2.01/0.99  ------ Debug Options
% 2.01/0.99  
% 2.01/0.99  --dbg_backtrace                         false
% 2.01/0.99  --dbg_dump_prop_clauses                 false
% 2.01/0.99  --dbg_dump_prop_clauses_file            -
% 2.01/0.99  --dbg_out_stat                          false
% 2.01/0.99  ------ Parsing...
% 2.01/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.01/0.99  
% 2.01/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.01/0.99  
% 2.01/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.01/0.99  
% 2.01/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.01/0.99  ------ Proving...
% 2.01/0.99  ------ Problem Properties 
% 2.01/0.99  
% 2.01/0.99  
% 2.01/0.99  clauses                                 19
% 2.01/0.99  conjectures                             3
% 2.01/0.99  EPR                                     3
% 2.01/0.99  Horn                                    15
% 2.01/0.99  unary                                   3
% 2.01/0.99  binary                                  6
% 2.01/0.99  lits                                    48
% 2.01/0.99  lits eq                                 25
% 2.01/0.99  fd_pure                                 0
% 2.01/0.99  fd_pseudo                               0
% 2.01/0.99  fd_cond                                 0
% 2.01/0.99  fd_pseudo_cond                          2
% 2.01/0.99  AC symbols                              0
% 2.01/0.99  
% 2.01/0.99  ------ Schedule dynamic 5 is on 
% 2.01/0.99  
% 2.01/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.01/0.99  
% 2.01/0.99  
% 2.01/0.99  ------ 
% 2.01/0.99  Current options:
% 2.01/0.99  ------ 
% 2.01/0.99  
% 2.01/0.99  ------ Input Options
% 2.01/0.99  
% 2.01/0.99  --out_options                           all
% 2.01/0.99  --tptp_safe_out                         true
% 2.01/0.99  --problem_path                          ""
% 2.01/0.99  --include_path                          ""
% 2.01/0.99  --clausifier                            res/vclausify_rel
% 2.01/0.99  --clausifier_options                    --mode clausify
% 2.01/0.99  --stdin                                 false
% 2.01/0.99  --stats_out                             all
% 2.01/0.99  
% 2.01/0.99  ------ General Options
% 2.01/0.99  
% 2.01/0.99  --fof                                   false
% 2.01/0.99  --time_out_real                         305.
% 2.01/0.99  --time_out_virtual                      -1.
% 2.01/0.99  --symbol_type_check                     false
% 2.01/0.99  --clausify_out                          false
% 2.01/0.99  --sig_cnt_out                           false
% 2.01/0.99  --trig_cnt_out                          false
% 2.01/0.99  --trig_cnt_out_tolerance                1.
% 2.01/0.99  --trig_cnt_out_sk_spl                   false
% 2.01/0.99  --abstr_cl_out                          false
% 2.01/0.99  
% 2.01/0.99  ------ Global Options
% 2.01/0.99  
% 2.01/0.99  --schedule                              default
% 2.01/0.99  --add_important_lit                     false
% 2.01/0.99  --prop_solver_per_cl                    1000
% 2.01/0.99  --min_unsat_core                        false
% 2.01/0.99  --soft_assumptions                      false
% 2.01/0.99  --soft_lemma_size                       3
% 2.01/0.99  --prop_impl_unit_size                   0
% 2.01/0.99  --prop_impl_unit                        []
% 2.01/0.99  --share_sel_clauses                     true
% 2.01/0.99  --reset_solvers                         false
% 2.01/0.99  --bc_imp_inh                            [conj_cone]
% 2.01/0.99  --conj_cone_tolerance                   3.
% 2.01/0.99  --extra_neg_conj                        none
% 2.01/0.99  --large_theory_mode                     true
% 2.01/0.99  --prolific_symb_bound                   200
% 2.01/0.99  --lt_threshold                          2000
% 2.01/0.99  --clause_weak_htbl                      true
% 2.01/0.99  --gc_record_bc_elim                     false
% 2.01/0.99  
% 2.01/0.99  ------ Preprocessing Options
% 2.01/0.99  
% 2.01/0.99  --preprocessing_flag                    true
% 2.01/0.99  --time_out_prep_mult                    0.1
% 2.01/0.99  --splitting_mode                        input
% 2.01/0.99  --splitting_grd                         true
% 2.01/0.99  --splitting_cvd                         false
% 2.01/0.99  --splitting_cvd_svl                     false
% 2.01/0.99  --splitting_nvd                         32
% 2.01/0.99  --sub_typing                            true
% 2.01/0.99  --prep_gs_sim                           true
% 2.01/0.99  --prep_unflatten                        true
% 2.01/0.99  --prep_res_sim                          true
% 2.01/0.99  --prep_upred                            true
% 2.01/0.99  --prep_sem_filter                       exhaustive
% 2.01/0.99  --prep_sem_filter_out                   false
% 2.01/0.99  --pred_elim                             true
% 2.01/0.99  --res_sim_input                         true
% 2.01/0.99  --eq_ax_congr_red                       true
% 2.01/0.99  --pure_diseq_elim                       true
% 2.01/0.99  --brand_transform                       false
% 2.01/0.99  --non_eq_to_eq                          false
% 2.01/0.99  --prep_def_merge                        true
% 2.01/0.99  --prep_def_merge_prop_impl              false
% 2.01/0.99  --prep_def_merge_mbd                    true
% 2.01/0.99  --prep_def_merge_tr_red                 false
% 2.01/0.99  --prep_def_merge_tr_cl                  false
% 2.01/0.99  --smt_preprocessing                     true
% 2.01/0.99  --smt_ac_axioms                         fast
% 2.01/0.99  --preprocessed_out                      false
% 2.01/0.99  --preprocessed_stats                    false
% 2.01/0.99  
% 2.01/0.99  ------ Abstraction refinement Options
% 2.01/0.99  
% 2.01/0.99  --abstr_ref                             []
% 2.01/0.99  --abstr_ref_prep                        false
% 2.01/0.99  --abstr_ref_until_sat                   false
% 2.01/0.99  --abstr_ref_sig_restrict                funpre
% 2.01/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.01/0.99  --abstr_ref_under                       []
% 2.01/0.99  
% 2.01/0.99  ------ SAT Options
% 2.01/0.99  
% 2.01/0.99  --sat_mode                              false
% 2.01/0.99  --sat_fm_restart_options                ""
% 2.01/0.99  --sat_gr_def                            false
% 2.01/0.99  --sat_epr_types                         true
% 2.01/0.99  --sat_non_cyclic_types                  false
% 2.01/0.99  --sat_finite_models                     false
% 2.01/0.99  --sat_fm_lemmas                         false
% 2.01/0.99  --sat_fm_prep                           false
% 2.01/0.99  --sat_fm_uc_incr                        true
% 2.01/0.99  --sat_out_model                         small
% 2.01/0.99  --sat_out_clauses                       false
% 2.01/0.99  
% 2.01/0.99  ------ QBF Options
% 2.01/0.99  
% 2.01/0.99  --qbf_mode                              false
% 2.01/0.99  --qbf_elim_univ                         false
% 2.01/0.99  --qbf_dom_inst                          none
% 2.01/0.99  --qbf_dom_pre_inst                      false
% 2.01/0.99  --qbf_sk_in                             false
% 2.01/0.99  --qbf_pred_elim                         true
% 2.01/0.99  --qbf_split                             512
% 2.01/0.99  
% 2.01/0.99  ------ BMC1 Options
% 2.01/0.99  
% 2.01/0.99  --bmc1_incremental                      false
% 2.01/0.99  --bmc1_axioms                           reachable_all
% 2.01/0.99  --bmc1_min_bound                        0
% 2.01/0.99  --bmc1_max_bound                        -1
% 2.01/0.99  --bmc1_max_bound_default                -1
% 2.01/0.99  --bmc1_symbol_reachability              true
% 2.01/0.99  --bmc1_property_lemmas                  false
% 2.01/0.99  --bmc1_k_induction                      false
% 2.01/0.99  --bmc1_non_equiv_states                 false
% 2.01/0.99  --bmc1_deadlock                         false
% 2.01/0.99  --bmc1_ucm                              false
% 2.01/0.99  --bmc1_add_unsat_core                   none
% 2.01/0.99  --bmc1_unsat_core_children              false
% 2.01/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.01/0.99  --bmc1_out_stat                         full
% 2.01/0.99  --bmc1_ground_init                      false
% 2.01/0.99  --bmc1_pre_inst_next_state              false
% 2.01/0.99  --bmc1_pre_inst_state                   false
% 2.01/0.99  --bmc1_pre_inst_reach_state             false
% 2.01/0.99  --bmc1_out_unsat_core                   false
% 2.01/0.99  --bmc1_aig_witness_out                  false
% 2.01/0.99  --bmc1_verbose                          false
% 2.01/0.99  --bmc1_dump_clauses_tptp                false
% 2.01/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.01/0.99  --bmc1_dump_file                        -
% 2.01/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.01/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.01/0.99  --bmc1_ucm_extend_mode                  1
% 2.01/0.99  --bmc1_ucm_init_mode                    2
% 2.01/0.99  --bmc1_ucm_cone_mode                    none
% 2.01/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.01/0.99  --bmc1_ucm_relax_model                  4
% 2.01/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.01/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.01/0.99  --bmc1_ucm_layered_model                none
% 2.01/0.99  --bmc1_ucm_max_lemma_size               10
% 2.01/0.99  
% 2.01/0.99  ------ AIG Options
% 2.01/0.99  
% 2.01/0.99  --aig_mode                              false
% 2.01/0.99  
% 2.01/0.99  ------ Instantiation Options
% 2.01/0.99  
% 2.01/0.99  --instantiation_flag                    true
% 2.01/0.99  --inst_sos_flag                         false
% 2.01/0.99  --inst_sos_phase                        true
% 2.01/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.01/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.01/0.99  --inst_lit_sel_side                     none
% 2.01/0.99  --inst_solver_per_active                1400
% 2.01/0.99  --inst_solver_calls_frac                1.
% 2.01/0.99  --inst_passive_queue_type               priority_queues
% 2.01/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.01/0.99  --inst_passive_queues_freq              [25;2]
% 2.01/0.99  --inst_dismatching                      true
% 2.01/0.99  --inst_eager_unprocessed_to_passive     true
% 2.01/0.99  --inst_prop_sim_given                   true
% 2.01/0.99  --inst_prop_sim_new                     false
% 2.01/0.99  --inst_subs_new                         false
% 2.01/0.99  --inst_eq_res_simp                      false
% 2.01/0.99  --inst_subs_given                       false
% 2.01/0.99  --inst_orphan_elimination               true
% 2.01/0.99  --inst_learning_loop_flag               true
% 2.01/0.99  --inst_learning_start                   3000
% 2.01/0.99  --inst_learning_factor                  2
% 2.01/0.99  --inst_start_prop_sim_after_learn       3
% 2.01/0.99  --inst_sel_renew                        solver
% 2.01/0.99  --inst_lit_activity_flag                true
% 2.01/0.99  --inst_restr_to_given                   false
% 2.01/0.99  --inst_activity_threshold               500
% 2.01/0.99  --inst_out_proof                        true
% 2.01/0.99  
% 2.01/0.99  ------ Resolution Options
% 2.01/0.99  
% 2.01/0.99  --resolution_flag                       false
% 2.01/0.99  --res_lit_sel                           adaptive
% 2.01/0.99  --res_lit_sel_side                      none
% 2.01/0.99  --res_ordering                          kbo
% 2.01/0.99  --res_to_prop_solver                    active
% 2.01/0.99  --res_prop_simpl_new                    false
% 2.01/0.99  --res_prop_simpl_given                  true
% 2.01/0.99  --res_passive_queue_type                priority_queues
% 2.01/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.01/0.99  --res_passive_queues_freq               [15;5]
% 2.01/0.99  --res_forward_subs                      full
% 2.01/0.99  --res_backward_subs                     full
% 2.01/0.99  --res_forward_subs_resolution           true
% 2.01/0.99  --res_backward_subs_resolution          true
% 2.01/0.99  --res_orphan_elimination                true
% 2.01/0.99  --res_time_limit                        2.
% 2.01/0.99  --res_out_proof                         true
% 2.01/0.99  
% 2.01/0.99  ------ Superposition Options
% 2.01/0.99  
% 2.01/0.99  --superposition_flag                    true
% 2.01/0.99  --sup_passive_queue_type                priority_queues
% 2.01/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.01/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.01/0.99  --demod_completeness_check              fast
% 2.01/0.99  --demod_use_ground                      true
% 2.01/0.99  --sup_to_prop_solver                    passive
% 2.01/0.99  --sup_prop_simpl_new                    true
% 2.01/0.99  --sup_prop_simpl_given                  true
% 2.01/0.99  --sup_fun_splitting                     false
% 2.01/0.99  --sup_smt_interval                      50000
% 2.01/0.99  
% 2.01/0.99  ------ Superposition Simplification Setup
% 2.01/0.99  
% 2.01/0.99  --sup_indices_passive                   []
% 2.01/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.01/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.01/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.01/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.01/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.01/0.99  --sup_full_bw                           [BwDemod]
% 2.01/0.99  --sup_immed_triv                        [TrivRules]
% 2.01/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.01/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.01/1.00  --sup_immed_bw_main                     []
% 2.01/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.01/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.01/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.01/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.01/1.00  
% 2.01/1.00  ------ Combination Options
% 2.01/1.00  
% 2.01/1.00  --comb_res_mult                         3
% 2.01/1.00  --comb_sup_mult                         2
% 2.01/1.00  --comb_inst_mult                        10
% 2.01/1.00  
% 2.01/1.00  ------ Debug Options
% 2.01/1.00  
% 2.01/1.00  --dbg_backtrace                         false
% 2.01/1.00  --dbg_dump_prop_clauses                 false
% 2.01/1.00  --dbg_dump_prop_clauses_file            -
% 2.01/1.00  --dbg_out_stat                          false
% 2.01/1.00  
% 2.01/1.00  
% 2.01/1.00  
% 2.01/1.00  
% 2.01/1.00  ------ Proving...
% 2.01/1.00  
% 2.01/1.00  
% 2.01/1.00  % SZS status Theorem for theBenchmark.p
% 2.01/1.00  
% 2.01/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.01/1.00  
% 2.01/1.00  fof(f10,conjecture,(
% 2.01/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 2.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.01/1.00  
% 2.01/1.00  fof(f11,negated_conjecture,(
% 2.01/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 2.01/1.00    inference(negated_conjecture,[],[f10])).
% 2.01/1.00  
% 2.01/1.00  fof(f21,plain,(
% 2.01/1.00    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.01/1.00    inference(ennf_transformation,[],[f11])).
% 2.01/1.00  
% 2.01/1.00  fof(f22,plain,(
% 2.01/1.00    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.01/1.00    inference(flattening,[],[f21])).
% 2.01/1.00  
% 2.01/1.00  fof(f33,plain,(
% 2.01/1.00    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK5(X3)) = X3 & r2_hidden(sK5(X3),X0)))) )),
% 2.01/1.00    introduced(choice_axiom,[])).
% 2.01/1.00  
% 2.01/1.00  fof(f32,plain,(
% 2.01/1.00    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK2,sK3,sK4) != sK3 & ! [X3] : (? [X4] : (k1_funct_1(sK4,X4) = X3 & r2_hidden(X4,sK2)) | ~r2_hidden(X3,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 2.01/1.00    introduced(choice_axiom,[])).
% 2.01/1.00  
% 2.01/1.00  fof(f34,plain,(
% 2.01/1.00    k2_relset_1(sK2,sK3,sK4) != sK3 & ! [X3] : ((k1_funct_1(sK4,sK5(X3)) = X3 & r2_hidden(sK5(X3),sK2)) | ~r2_hidden(X3,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 2.01/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f22,f33,f32])).
% 2.01/1.00  
% 2.01/1.00  fof(f57,plain,(
% 2.01/1.00    v1_funct_2(sK4,sK2,sK3)),
% 2.01/1.00    inference(cnf_transformation,[],[f34])).
% 2.01/1.00  
% 2.01/1.00  fof(f9,axiom,(
% 2.01/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.01/1.00  
% 2.01/1.00  fof(f19,plain,(
% 2.01/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/1.00    inference(ennf_transformation,[],[f9])).
% 2.01/1.00  
% 2.01/1.00  fof(f20,plain,(
% 2.01/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/1.00    inference(flattening,[],[f19])).
% 2.01/1.00  
% 2.01/1.00  fof(f31,plain,(
% 2.01/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/1.00    inference(nnf_transformation,[],[f20])).
% 2.01/1.00  
% 2.01/1.00  fof(f50,plain,(
% 2.01/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.01/1.00    inference(cnf_transformation,[],[f31])).
% 2.01/1.00  
% 2.01/1.00  fof(f58,plain,(
% 2.01/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.01/1.00    inference(cnf_transformation,[],[f34])).
% 2.01/1.00  
% 2.01/1.00  fof(f6,axiom,(
% 2.01/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.01/1.00  
% 2.01/1.00  fof(f16,plain,(
% 2.01/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/1.00    inference(ennf_transformation,[],[f6])).
% 2.01/1.00  
% 2.01/1.00  fof(f45,plain,(
% 2.01/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.01/1.00    inference(cnf_transformation,[],[f16])).
% 2.01/1.00  
% 2.01/1.00  fof(f1,axiom,(
% 2.01/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.01/1.00  
% 2.01/1.00  fof(f23,plain,(
% 2.01/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.01/1.00    inference(nnf_transformation,[],[f1])).
% 2.01/1.00  
% 2.01/1.00  fof(f24,plain,(
% 2.01/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.01/1.00    inference(flattening,[],[f23])).
% 2.01/1.00  
% 2.01/1.00  fof(f35,plain,(
% 2.01/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.01/1.00    inference(cnf_transformation,[],[f24])).
% 2.01/1.00  
% 2.01/1.00  fof(f63,plain,(
% 2.01/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.01/1.00    inference(equality_resolution,[],[f35])).
% 2.01/1.00  
% 2.01/1.00  fof(f4,axiom,(
% 2.01/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 2.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.01/1.00  
% 2.01/1.00  fof(f13,plain,(
% 2.01/1.00    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.01/1.00    inference(ennf_transformation,[],[f4])).
% 2.01/1.00  
% 2.01/1.00  fof(f14,plain,(
% 2.01/1.00    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.01/1.00    inference(flattening,[],[f13])).
% 2.01/1.00  
% 2.01/1.00  fof(f25,plain,(
% 2.01/1.00    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.01/1.00    inference(nnf_transformation,[],[f14])).
% 2.01/1.00  
% 2.01/1.00  fof(f43,plain,(
% 2.01/1.00    ( ! [X2,X0,X1] : (k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.01/1.00    inference(cnf_transformation,[],[f25])).
% 2.01/1.00  
% 2.01/1.00  fof(f64,plain,(
% 2.01/1.00    ( ! [X0,X1] : (k1_funct_1(X0,X1) = k1_xboole_0 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.01/1.00    inference(equality_resolution,[],[f43])).
% 2.01/1.00  
% 2.01/1.00  fof(f56,plain,(
% 2.01/1.00    v1_funct_1(sK4)),
% 2.01/1.00    inference(cnf_transformation,[],[f34])).
% 2.01/1.00  
% 2.01/1.00  fof(f2,axiom,(
% 2.01/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.01/1.00  
% 2.01/1.00  fof(f12,plain,(
% 2.01/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.01/1.00    inference(ennf_transformation,[],[f2])).
% 2.01/1.00  
% 2.01/1.00  fof(f38,plain,(
% 2.01/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.01/1.00    inference(cnf_transformation,[],[f12])).
% 2.01/1.00  
% 2.01/1.00  fof(f3,axiom,(
% 2.01/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.01/1.00  
% 2.01/1.00  fof(f39,plain,(
% 2.01/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.01/1.00    inference(cnf_transformation,[],[f3])).
% 2.01/1.00  
% 2.01/1.00  fof(f5,axiom,(
% 2.01/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.01/1.00  
% 2.01/1.00  fof(f15,plain,(
% 2.01/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.01/1.00    inference(ennf_transformation,[],[f5])).
% 2.01/1.00  
% 2.01/1.00  fof(f44,plain,(
% 2.01/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.01/1.00    inference(cnf_transformation,[],[f15])).
% 2.01/1.00  
% 2.01/1.00  fof(f40,plain,(
% 2.01/1.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2 | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.01/1.00    inference(cnf_transformation,[],[f25])).
% 2.01/1.00  
% 2.01/1.00  fof(f66,plain,(
% 2.01/1.00    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.01/1.00    inference(equality_resolution,[],[f40])).
% 2.01/1.00  
% 2.01/1.00  fof(f61,plain,(
% 2.01/1.00    k2_relset_1(sK2,sK3,sK4) != sK3),
% 2.01/1.00    inference(cnf_transformation,[],[f34])).
% 2.01/1.00  
% 2.01/1.00  fof(f8,axiom,(
% 2.01/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 2.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.01/1.00  
% 2.01/1.00  fof(f18,plain,(
% 2.01/1.00    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/1.00    inference(ennf_transformation,[],[f8])).
% 2.01/1.00  
% 2.01/1.00  fof(f26,plain,(
% 2.01/1.00    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) | k2_relset_1(X0,X1,X2) != X1) & (k2_relset_1(X0,X1,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/1.00    inference(nnf_transformation,[],[f18])).
% 2.01/1.00  
% 2.01/1.00  fof(f27,plain,(
% 2.01/1.00    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) | k2_relset_1(X0,X1,X2) != X1) & (k2_relset_1(X0,X1,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X6,X5),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/1.00    inference(rectify,[],[f26])).
% 2.01/1.00  
% 2.01/1.00  fof(f29,plain,(
% 2.01/1.00    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X6,X5),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(X6,sK1(X1,X2)),X2) & r2_hidden(sK1(X1,X2),X1)))),
% 2.01/1.00    introduced(choice_axiom,[])).
% 2.01/1.00  
% 2.01/1.00  fof(f28,plain,(
% 2.01/1.00    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) => r2_hidden(k4_tarski(sK0(X2,X3),X3),X2))),
% 2.01/1.00    introduced(choice_axiom,[])).
% 2.01/1.00  
% 2.01/1.00  fof(f30,plain,(
% 2.01/1.00    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(sK0(X2,X3),X3),X2) | ~r2_hidden(X3,X1)) | k2_relset_1(X0,X1,X2) != X1) & (k2_relset_1(X0,X1,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(X6,sK1(X1,X2)),X2) & r2_hidden(sK1(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f29,f28])).
% 2.01/1.00  
% 2.01/1.00  fof(f47,plain,(
% 2.01/1.00    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = X1 | r2_hidden(sK1(X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.01/1.00    inference(cnf_transformation,[],[f30])).
% 2.01/1.00  
% 2.01/1.00  fof(f59,plain,(
% 2.01/1.00    ( ! [X3] : (r2_hidden(sK5(X3),sK2) | ~r2_hidden(X3,sK3)) )),
% 2.01/1.00    inference(cnf_transformation,[],[f34])).
% 2.01/1.00  
% 2.01/1.00  fof(f7,axiom,(
% 2.01/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.01/1.00  
% 2.01/1.00  fof(f17,plain,(
% 2.01/1.00    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/1.00    inference(ennf_transformation,[],[f7])).
% 2.01/1.00  
% 2.01/1.00  fof(f46,plain,(
% 2.01/1.00    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.01/1.00    inference(cnf_transformation,[],[f17])).
% 2.01/1.00  
% 2.01/1.00  fof(f60,plain,(
% 2.01/1.00    ( ! [X3] : (k1_funct_1(sK4,sK5(X3)) = X3 | ~r2_hidden(X3,sK3)) )),
% 2.01/1.00    inference(cnf_transformation,[],[f34])).
% 2.01/1.00  
% 2.01/1.00  fof(f48,plain,(
% 2.01/1.00    ( ! [X6,X2,X0,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_hidden(k4_tarski(X6,sK1(X1,X2)),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.01/1.00    inference(cnf_transformation,[],[f30])).
% 2.01/1.00  
% 2.01/1.00  cnf(c_25,negated_conjecture,
% 2.01/1.00      ( v1_funct_2(sK4,sK2,sK3) ),
% 2.01/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_20,plain,
% 2.01/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.01/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.01/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.01/1.00      | k1_xboole_0 = X2 ),
% 2.01/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_24,negated_conjecture,
% 2.01/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.01/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_362,plain,
% 2.01/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.01/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.01/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.01/1.00      | sK4 != X0
% 2.01/1.00      | k1_xboole_0 = X2 ),
% 2.01/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_24]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_363,plain,
% 2.01/1.00      ( ~ v1_funct_2(sK4,X0,X1)
% 2.01/1.00      | k1_relset_1(X0,X1,sK4) = X0
% 2.01/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.01/1.00      | k1_xboole_0 = X1 ),
% 2.01/1.00      inference(unflattening,[status(thm)],[c_362]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_586,plain,
% 2.01/1.00      ( k1_relset_1(X0,X1,sK4) = X0
% 2.01/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.01/1.00      | sK4 != sK4
% 2.01/1.00      | sK3 != X1
% 2.01/1.00      | sK2 != X0
% 2.01/1.00      | k1_xboole_0 = X1 ),
% 2.01/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_363]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_587,plain,
% 2.01/1.00      ( k1_relset_1(sK2,sK3,sK4) = sK2
% 2.01/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.01/1.00      | k1_xboole_0 = sK3 ),
% 2.01/1.00      inference(unflattening,[status(thm)],[c_586]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_653,plain,
% 2.01/1.00      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 2.01/1.00      inference(equality_resolution_simp,[status(thm)],[c_587]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_10,plain,
% 2.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.01/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.01/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_407,plain,
% 2.01/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.01/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.01/1.00      | sK4 != X2 ),
% 2.01/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_24]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_408,plain,
% 2.01/1.00      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 2.01/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 2.01/1.00      inference(unflattening,[status(thm)],[c_407]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1168,plain,
% 2.01/1.00      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 2.01/1.00      inference(equality_resolution,[status(thm)],[c_408]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1382,plain,
% 2.01/1.00      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 2.01/1.00      inference(superposition,[status(thm)],[c_653,c_1168]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_2,plain,
% 2.01/1.00      ( r1_tarski(X0,X0) ),
% 2.01/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_991,plain,
% 2.01/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 2.01/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_5,plain,
% 2.01/1.00      ( r2_hidden(X0,k1_relat_1(X1))
% 2.01/1.00      | ~ v1_funct_1(X1)
% 2.01/1.00      | ~ v1_relat_1(X1)
% 2.01/1.00      | k1_funct_1(X1,X0) = k1_xboole_0 ),
% 2.01/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_26,negated_conjecture,
% 2.01/1.00      ( v1_funct_1(sK4) ),
% 2.01/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_319,plain,
% 2.01/1.00      ( r2_hidden(X0,k1_relat_1(X1))
% 2.01/1.00      | ~ v1_relat_1(X1)
% 2.01/1.00      | k1_funct_1(X1,X0) = k1_xboole_0
% 2.01/1.00      | sK4 != X1 ),
% 2.01/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_26]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_320,plain,
% 2.01/1.00      ( r2_hidden(X0,k1_relat_1(sK4))
% 2.01/1.00      | ~ v1_relat_1(sK4)
% 2.01/1.00      | k1_funct_1(sK4,X0) = k1_xboole_0 ),
% 2.01/1.00      inference(unflattening,[status(thm)],[c_319]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_984,plain,
% 2.01/1.00      ( k1_funct_1(sK4,X0) = k1_xboole_0
% 2.01/1.00      | r2_hidden(X0,k1_relat_1(sK4)) = iProver_top
% 2.01/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.01/1.00      inference(predicate_to_equality,[status(thm)],[c_320]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_321,plain,
% 2.01/1.00      ( k1_funct_1(sK4,X0) = k1_xboole_0
% 2.01/1.00      | r2_hidden(X0,k1_relat_1(sK4)) = iProver_top
% 2.01/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.01/1.00      inference(predicate_to_equality,[status(thm)],[c_320]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_738,plain,( X0 = X0 ),theory(equality) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1126,plain,
% 2.01/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 2.01/1.00      inference(instantiation,[status(thm)],[c_738]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_3,plain,
% 2.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.01/1.00      | ~ v1_relat_1(X1)
% 2.01/1.00      | v1_relat_1(X0) ),
% 2.01/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_347,plain,
% 2.01/1.00      ( ~ v1_relat_1(X0)
% 2.01/1.00      | v1_relat_1(X1)
% 2.01/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X0)
% 2.01/1.00      | sK4 != X1 ),
% 2.01/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_24]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_348,plain,
% 2.01/1.00      ( ~ v1_relat_1(X0)
% 2.01/1.00      | v1_relat_1(sK4)
% 2.01/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X0) ),
% 2.01/1.00      inference(unflattening,[status(thm)],[c_347]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1121,plain,
% 2.01/1.00      ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 2.01/1.00      | v1_relat_1(sK4)
% 2.01/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.01/1.00      inference(instantiation,[status(thm)],[c_348]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1209,plain,
% 2.01/1.00      ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
% 2.01/1.00      | v1_relat_1(sK4)
% 2.01/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 2.01/1.00      inference(instantiation,[status(thm)],[c_1121]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1210,plain,
% 2.01/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.01/1.00      | v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
% 2.01/1.00      | v1_relat_1(sK4) = iProver_top ),
% 2.01/1.00      inference(predicate_to_equality,[status(thm)],[c_1209]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_4,plain,
% 2.01/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.01/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1315,plain,
% 2.01/1.00      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) ),
% 2.01/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1316,plain,
% 2.01/1.00      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 2.01/1.00      inference(predicate_to_equality,[status(thm)],[c_1315]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1697,plain,
% 2.01/1.00      ( r2_hidden(X0,k1_relat_1(sK4)) = iProver_top
% 2.01/1.00      | k1_funct_1(sK4,X0) = k1_xboole_0 ),
% 2.01/1.00      inference(global_propositional_subsumption,
% 2.01/1.00                [status(thm)],
% 2.01/1.00                [c_984,c_321,c_1126,c_1210,c_1316]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1698,plain,
% 2.01/1.00      ( k1_funct_1(sK4,X0) = k1_xboole_0
% 2.01/1.00      | r2_hidden(X0,k1_relat_1(sK4)) = iProver_top ),
% 2.01/1.00      inference(renaming,[status(thm)],[c_1697]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_9,plain,
% 2.01/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.01/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_989,plain,
% 2.01/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.01/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 2.01/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1705,plain,
% 2.01/1.00      ( k1_funct_1(sK4,X0) = k1_xboole_0
% 2.01/1.00      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
% 2.01/1.00      inference(superposition,[status(thm)],[c_1698,c_989]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1786,plain,
% 2.01/1.00      ( k1_funct_1(sK4,k1_relat_1(sK4)) = k1_xboole_0 ),
% 2.01/1.00      inference(superposition,[status(thm)],[c_991,c_1705]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_8,plain,
% 2.01/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.01/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 2.01/1.00      | ~ v1_funct_1(X1)
% 2.01/1.00      | ~ v1_relat_1(X1) ),
% 2.01/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_286,plain,
% 2.01/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.01/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 2.01/1.00      | ~ v1_relat_1(X1)
% 2.01/1.00      | sK4 != X1 ),
% 2.01/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_26]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_287,plain,
% 2.01/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.01/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4)
% 2.01/1.00      | ~ v1_relat_1(sK4) ),
% 2.01/1.00      inference(unflattening,[status(thm)],[c_286]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_986,plain,
% 2.01/1.00      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.01/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top
% 2.01/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.01/1.00      inference(predicate_to_equality,[status(thm)],[c_287]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_288,plain,
% 2.01/1.00      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.01/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top
% 2.01/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.01/1.00      inference(predicate_to_equality,[status(thm)],[c_287]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1536,plain,
% 2.01/1.00      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top
% 2.01/1.00      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 2.01/1.00      inference(global_propositional_subsumption,
% 2.01/1.00                [status(thm)],
% 2.01/1.00                [c_986,c_288,c_1126,c_1210,c_1316]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1537,plain,
% 2.01/1.00      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.01/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top ),
% 2.01/1.00      inference(renaming,[status(thm)],[c_1536]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1815,plain,
% 2.01/1.00      ( r2_hidden(k4_tarski(k1_relat_1(sK4),k1_xboole_0),sK4) = iProver_top
% 2.01/1.00      | r2_hidden(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top ),
% 2.01/1.00      inference(superposition,[status(thm)],[c_1786,c_1537]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1566,plain,
% 2.01/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.01/1.00      | ~ r1_tarski(k1_relat_1(sK4),X0) ),
% 2.01/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1662,plain,
% 2.01/1.00      ( ~ r2_hidden(k1_relat_1(sK4),k1_relat_1(sK4))
% 2.01/1.00      | ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) ),
% 2.01/1.00      inference(instantiation,[status(thm)],[c_1566]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1664,plain,
% 2.01/1.00      ( r2_hidden(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
% 2.01/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top ),
% 2.01/1.00      inference(predicate_to_equality,[status(thm)],[c_1662]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1663,plain,
% 2.01/1.00      ( r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) ),
% 2.01/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1666,plain,
% 2.01/1.00      ( r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) = iProver_top ),
% 2.01/1.00      inference(predicate_to_equality,[status(thm)],[c_1663]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1864,plain,
% 2.01/1.00      ( r2_hidden(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top ),
% 2.01/1.00      inference(global_propositional_subsumption,
% 2.01/1.00                [status(thm)],
% 2.01/1.00                [c_1815,c_1664,c_1666]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1910,plain,
% 2.01/1.00      ( sK3 = k1_xboole_0 | r2_hidden(sK2,sK2) != iProver_top ),
% 2.01/1.00      inference(superposition,[status(thm)],[c_1382,c_1864]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_21,negated_conjecture,
% 2.01/1.00      ( k2_relset_1(sK2,sK3,sK4) != sK3 ),
% 2.01/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_14,plain,
% 2.01/1.00      ( r2_hidden(sK1(X0,X1),X0)
% 2.01/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
% 2.01/1.00      | k2_relset_1(X2,X0,X1) = X0 ),
% 2.01/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_449,plain,
% 2.01/1.00      ( r2_hidden(sK1(X0,X1),X0)
% 2.01/1.00      | k2_relset_1(X2,X0,X1) = X0
% 2.01/1.00      | k1_zfmisc_1(k2_zfmisc_1(X2,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.01/1.00      | sK4 != X1 ),
% 2.01/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_24]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_450,plain,
% 2.01/1.00      ( r2_hidden(sK1(X0,sK4),X0)
% 2.01/1.00      | k2_relset_1(X1,X0,sK4) = X0
% 2.01/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 2.01/1.00      inference(unflattening,[status(thm)],[c_449]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1179,plain,
% 2.01/1.00      ( r2_hidden(sK1(sK3,sK4),sK3)
% 2.01/1.00      | k2_relset_1(sK2,sK3,sK4) = sK3
% 2.01/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 2.01/1.00      inference(instantiation,[status(thm)],[c_450]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1180,plain,
% 2.01/1.00      ( k2_relset_1(sK2,sK3,sK4) = sK3
% 2.01/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.01/1.00      | r2_hidden(sK1(sK3,sK4),sK3) = iProver_top ),
% 2.01/1.00      inference(predicate_to_equality,[status(thm)],[c_1179]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_23,negated_conjecture,
% 2.01/1.00      ( ~ r2_hidden(X0,sK3) | r2_hidden(sK5(X0),sK2) ),
% 2.01/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1269,plain,
% 2.01/1.00      ( ~ r2_hidden(sK1(sK3,sK4),sK3)
% 2.01/1.00      | r2_hidden(sK5(sK1(sK3,sK4)),sK2) ),
% 2.01/1.00      inference(instantiation,[status(thm)],[c_23]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1270,plain,
% 2.01/1.00      ( r2_hidden(sK1(sK3,sK4),sK3) != iProver_top
% 2.01/1.00      | r2_hidden(sK5(sK1(sK3,sK4)),sK2) = iProver_top ),
% 2.01/1.00      inference(predicate_to_equality,[status(thm)],[c_1269]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_980,plain,
% 2.01/1.00      ( k2_relset_1(X0,X1,sK4) = X1
% 2.01/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.01/1.00      | r2_hidden(sK1(X1,sK4),X1) = iProver_top ),
% 2.01/1.00      inference(predicate_to_equality,[status(thm)],[c_450]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1713,plain,
% 2.01/1.00      ( k2_relset_1(sK2,sK3,sK4) = sK3
% 2.01/1.00      | r2_hidden(sK1(sK3,sK4),sK3) = iProver_top ),
% 2.01/1.00      inference(equality_resolution,[status(thm)],[c_980]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_11,plain,
% 2.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.01/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.01/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_398,plain,
% 2.01/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.01/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.01/1.00      | sK4 != X2 ),
% 2.01/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_24]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_399,plain,
% 2.01/1.00      ( k2_relset_1(X0,X1,sK4) = k2_relat_1(sK4)
% 2.01/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 2.01/1.00      inference(unflattening,[status(thm)],[c_398]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1138,plain,
% 2.01/1.00      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 2.01/1.00      inference(equality_resolution,[status(thm)],[c_399]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1714,plain,
% 2.01/1.00      ( k2_relat_1(sK4) = sK3
% 2.01/1.00      | r2_hidden(sK1(sK3,sK4),sK3) = iProver_top ),
% 2.01/1.00      inference(demodulation,[status(thm)],[c_1713,c_1138]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1943,plain,
% 2.01/1.00      ( r2_hidden(sK1(sK3,sK4),sK3) = iProver_top ),
% 2.01/1.00      inference(global_propositional_subsumption,
% 2.01/1.00                [status(thm)],
% 2.01/1.00                [c_1714,c_21,c_1126,c_1180]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_22,negated_conjecture,
% 2.01/1.00      ( ~ r2_hidden(X0,sK3) | k1_funct_1(sK4,sK5(X0)) = X0 ),
% 2.01/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_988,plain,
% 2.01/1.00      ( k1_funct_1(sK4,sK5(X0)) = X0 | r2_hidden(X0,sK3) != iProver_top ),
% 2.01/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1949,plain,
% 2.01/1.00      ( k1_funct_1(sK4,sK5(sK1(sK3,sK4))) = sK1(sK3,sK4) ),
% 2.01/1.00      inference(superposition,[status(thm)],[c_1943,c_988]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_2010,plain,
% 2.01/1.00      ( r2_hidden(k4_tarski(sK5(sK1(sK3,sK4)),sK1(sK3,sK4)),sK4) = iProver_top
% 2.01/1.00      | r2_hidden(sK5(sK1(sK3,sK4)),k1_relat_1(sK4)) != iProver_top ),
% 2.01/1.00      inference(superposition,[status(thm)],[c_1949,c_1537]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_13,plain,
% 2.01/1.00      ( ~ r2_hidden(k4_tarski(X0,sK1(X1,X2)),X2)
% 2.01/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 2.01/1.00      | k2_relset_1(X3,X1,X2) = X1 ),
% 2.01/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_416,plain,
% 2.01/1.00      ( ~ r2_hidden(k4_tarski(X0,sK1(X1,X2)),X2)
% 2.01/1.00      | k2_relset_1(X3,X1,X2) = X1
% 2.01/1.00      | k1_zfmisc_1(k2_zfmisc_1(X3,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.01/1.00      | sK4 != X2 ),
% 2.01/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_417,plain,
% 2.01/1.00      ( ~ r2_hidden(k4_tarski(X0,sK1(X1,sK4)),sK4)
% 2.01/1.00      | k2_relset_1(X2,X1,sK4) = X1
% 2.01/1.00      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 2.01/1.00      inference(unflattening,[status(thm)],[c_416]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_982,plain,
% 2.01/1.00      ( k2_relset_1(X0,X1,sK4) = X1
% 2.01/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.01/1.00      | r2_hidden(k4_tarski(X2,sK1(X1,sK4)),sK4) != iProver_top ),
% 2.01/1.00      inference(predicate_to_equality,[status(thm)],[c_417]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1552,plain,
% 2.01/1.00      ( k2_relset_1(sK2,sK3,sK4) = sK3
% 2.01/1.00      | r2_hidden(k4_tarski(X0,sK1(sK3,sK4)),sK4) != iProver_top ),
% 2.01/1.00      inference(equality_resolution,[status(thm)],[c_982]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1553,plain,
% 2.01/1.00      ( k2_relat_1(sK4) = sK3
% 2.01/1.00      | r2_hidden(k4_tarski(X0,sK1(sK3,sK4)),sK4) != iProver_top ),
% 2.01/1.00      inference(demodulation,[status(thm)],[c_1552,c_1138]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1187,plain,
% 2.01/1.00      ( k2_relat_1(sK4) != sK3 ),
% 2.01/1.00      inference(demodulation,[status(thm)],[c_1138,c_21]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1818,plain,
% 2.01/1.00      ( r2_hidden(k4_tarski(X0,sK1(sK3,sK4)),sK4) != iProver_top ),
% 2.01/1.00      inference(global_propositional_subsumption,
% 2.01/1.00                [status(thm)],
% 2.01/1.00                [c_1553,c_1187]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_2024,plain,
% 2.01/1.00      ( r2_hidden(sK5(sK1(sK3,sK4)),k1_relat_1(sK4)) != iProver_top ),
% 2.01/1.00      inference(forward_subsumption_resolution,
% 2.01/1.00                [status(thm)],
% 2.01/1.00                [c_2010,c_1818]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_2027,plain,
% 2.01/1.00      ( sK3 = k1_xboole_0
% 2.01/1.00      | r2_hidden(sK5(sK1(sK3,sK4)),sK2) != iProver_top ),
% 2.01/1.00      inference(superposition,[status(thm)],[c_1382,c_2024]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_2068,plain,
% 2.01/1.00      ( sK3 = k1_xboole_0 ),
% 2.01/1.00      inference(global_propositional_subsumption,
% 2.01/1.00                [status(thm)],
% 2.01/1.00                [c_1910,c_21,c_1126,c_1180,c_1270,c_2027]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_2072,plain,
% 2.01/1.00      ( k1_funct_1(sK4,sK5(sK1(k1_xboole_0,sK4))) = sK1(k1_xboole_0,sK4) ),
% 2.01/1.00      inference(demodulation,[status(thm)],[c_2068,c_1949]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_2026,plain,
% 2.01/1.00      ( k1_funct_1(sK4,sK5(sK1(sK3,sK4))) = k1_xboole_0 ),
% 2.01/1.00      inference(superposition,[status(thm)],[c_1698,c_2024]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_2613,plain,
% 2.01/1.00      ( k1_funct_1(sK4,sK5(sK1(k1_xboole_0,sK4))) = k1_xboole_0 ),
% 2.01/1.00      inference(light_normalisation,[status(thm)],[c_2026,c_2068]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_2617,plain,
% 2.01/1.00      ( sK1(k1_xboole_0,sK4) = k1_xboole_0 ),
% 2.01/1.00      inference(light_normalisation,[status(thm)],[c_2072,c_2613]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1948,plain,
% 2.01/1.00      ( r1_tarski(sK3,sK1(sK3,sK4)) != iProver_top ),
% 2.01/1.00      inference(superposition,[status(thm)],[c_1943,c_989]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_2267,plain,
% 2.01/1.00      ( r1_tarski(k1_xboole_0,sK1(k1_xboole_0,sK4)) != iProver_top ),
% 2.01/1.00      inference(light_normalisation,[status(thm)],[c_1948,c_2068]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_2620,plain,
% 2.01/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.01/1.00      inference(demodulation,[status(thm)],[c_2617,c_2267]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_86,plain,
% 2.01/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 2.01/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_88,plain,
% 2.01/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.01/1.00      inference(instantiation,[status(thm)],[c_86]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(contradiction,plain,
% 2.01/1.00      ( $false ),
% 2.01/1.00      inference(minisat,[status(thm)],[c_2620,c_88]) ).
% 2.01/1.00  
% 2.01/1.00  
% 2.01/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.01/1.00  
% 2.01/1.00  ------                               Statistics
% 2.01/1.00  
% 2.01/1.00  ------ General
% 2.01/1.00  
% 2.01/1.00  abstr_ref_over_cycles:                  0
% 2.01/1.00  abstr_ref_under_cycles:                 0
% 2.01/1.00  gc_basic_clause_elim:                   0
% 2.01/1.00  forced_gc_time:                         0
% 2.01/1.00  parsing_time:                           0.009
% 2.01/1.00  unif_index_cands_time:                  0.
% 2.01/1.00  unif_index_add_time:                    0.
% 2.01/1.00  orderings_time:                         0.
% 2.01/1.00  out_proof_time:                         0.011
% 2.01/1.00  total_time:                             0.113
% 2.01/1.00  num_of_symbols:                         52
% 2.01/1.00  num_of_terms:                           2043
% 2.01/1.00  
% 2.01/1.00  ------ Preprocessing
% 2.01/1.00  
% 2.01/1.00  num_of_splits:                          0
% 2.01/1.00  num_of_split_atoms:                     0
% 2.01/1.00  num_of_reused_defs:                     0
% 2.01/1.00  num_eq_ax_congr_red:                    21
% 2.01/1.00  num_of_sem_filtered_clauses:            1
% 2.01/1.00  num_of_subtypes:                        0
% 2.01/1.00  monotx_restored_types:                  0
% 2.01/1.00  sat_num_of_epr_types:                   0
% 2.01/1.00  sat_num_of_non_cyclic_types:            0
% 2.01/1.00  sat_guarded_non_collapsed_types:        0
% 2.01/1.00  num_pure_diseq_elim:                    0
% 2.01/1.00  simp_replaced_by:                       0
% 2.01/1.00  res_preprocessed:                       111
% 2.01/1.00  prep_upred:                             0
% 2.01/1.00  prep_unflattend:                        31
% 2.01/1.00  smt_new_axioms:                         0
% 2.01/1.00  pred_elim_cands:                        3
% 2.01/1.00  pred_elim:                              3
% 2.01/1.00  pred_elim_cl:                           6
% 2.01/1.00  pred_elim_cycles:                       5
% 2.01/1.00  merged_defs:                            0
% 2.01/1.00  merged_defs_ncl:                        0
% 2.01/1.00  bin_hyper_res:                          0
% 2.01/1.00  prep_cycles:                            4
% 2.01/1.00  pred_elim_time:                         0.007
% 2.01/1.00  splitting_time:                         0.
% 2.01/1.00  sem_filter_time:                        0.
% 2.01/1.00  monotx_time:                            0.
% 2.01/1.00  subtype_inf_time:                       0.
% 2.01/1.00  
% 2.01/1.00  ------ Problem properties
% 2.01/1.00  
% 2.01/1.00  clauses:                                19
% 2.01/1.00  conjectures:                            3
% 2.01/1.00  epr:                                    3
% 2.01/1.00  horn:                                   15
% 2.01/1.00  ground:                                 4
% 2.01/1.00  unary:                                  3
% 2.01/1.00  binary:                                 6
% 2.01/1.00  lits:                                   48
% 2.01/1.00  lits_eq:                                25
% 2.01/1.00  fd_pure:                                0
% 2.01/1.00  fd_pseudo:                              0
% 2.01/1.00  fd_cond:                                0
% 2.01/1.00  fd_pseudo_cond:                         2
% 2.01/1.00  ac_symbols:                             0
% 2.01/1.00  
% 2.01/1.00  ------ Propositional Solver
% 2.01/1.00  
% 2.01/1.00  prop_solver_calls:                      27
% 2.01/1.00  prop_fast_solver_calls:                 742
% 2.01/1.00  smt_solver_calls:                       0
% 2.01/1.00  smt_fast_solver_calls:                  0
% 2.01/1.00  prop_num_of_clauses:                    823
% 2.01/1.00  prop_preprocess_simplified:             3590
% 2.01/1.00  prop_fo_subsumed:                       9
% 2.01/1.00  prop_solver_time:                       0.
% 2.01/1.00  smt_solver_time:                        0.
% 2.01/1.00  smt_fast_solver_time:                   0.
% 2.01/1.00  prop_fast_solver_time:                  0.
% 2.01/1.00  prop_unsat_core_time:                   0.
% 2.01/1.00  
% 2.01/1.00  ------ QBF
% 2.01/1.00  
% 2.01/1.00  qbf_q_res:                              0
% 2.01/1.00  qbf_num_tautologies:                    0
% 2.01/1.00  qbf_prep_cycles:                        0
% 2.01/1.00  
% 2.01/1.00  ------ BMC1
% 2.01/1.00  
% 2.01/1.00  bmc1_current_bound:                     -1
% 2.01/1.00  bmc1_last_solved_bound:                 -1
% 2.01/1.00  bmc1_unsat_core_size:                   -1
% 2.01/1.00  bmc1_unsat_core_parents_size:           -1
% 2.01/1.00  bmc1_merge_next_fun:                    0
% 2.01/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.01/1.00  
% 2.01/1.00  ------ Instantiation
% 2.01/1.00  
% 2.01/1.00  inst_num_of_clauses:                    261
% 2.01/1.00  inst_num_in_passive:                    74
% 2.01/1.00  inst_num_in_active:                     183
% 2.01/1.00  inst_num_in_unprocessed:                4
% 2.01/1.00  inst_num_of_loops:                      220
% 2.01/1.00  inst_num_of_learning_restarts:          0
% 2.01/1.00  inst_num_moves_active_passive:          33
% 2.01/1.00  inst_lit_activity:                      0
% 2.01/1.00  inst_lit_activity_moves:                0
% 2.01/1.00  inst_num_tautologies:                   0
% 2.01/1.00  inst_num_prop_implied:                  0
% 2.01/1.00  inst_num_existing_simplified:           0
% 2.01/1.00  inst_num_eq_res_simplified:             0
% 2.01/1.00  inst_num_child_elim:                    0
% 2.01/1.00  inst_num_of_dismatching_blockings:      72
% 2.01/1.00  inst_num_of_non_proper_insts:           316
% 2.01/1.00  inst_num_of_duplicates:                 0
% 2.01/1.00  inst_inst_num_from_inst_to_res:         0
% 2.01/1.00  inst_dismatching_checking_time:         0.
% 2.01/1.00  
% 2.01/1.00  ------ Resolution
% 2.01/1.00  
% 2.01/1.00  res_num_of_clauses:                     0
% 2.01/1.00  res_num_in_passive:                     0
% 2.01/1.00  res_num_in_active:                      0
% 2.01/1.00  res_num_of_loops:                       115
% 2.01/1.00  res_forward_subset_subsumed:            63
% 2.01/1.00  res_backward_subset_subsumed:           0
% 2.01/1.00  res_forward_subsumed:                   0
% 2.01/1.00  res_backward_subsumed:                  0
% 2.01/1.00  res_forward_subsumption_resolution:     0
% 2.01/1.00  res_backward_subsumption_resolution:    0
% 2.01/1.00  res_clause_to_clause_subsumption:       69
% 2.01/1.00  res_orphan_elimination:                 0
% 2.01/1.00  res_tautology_del:                      67
% 2.01/1.00  res_num_eq_res_simplified:              1
% 2.01/1.00  res_num_sel_changes:                    0
% 2.01/1.00  res_moves_from_active_to_pass:          0
% 2.01/1.00  
% 2.01/1.00  ------ Superposition
% 2.01/1.00  
% 2.01/1.00  sup_time_total:                         0.
% 2.01/1.00  sup_time_generating:                    0.
% 2.01/1.00  sup_time_sim_full:                      0.
% 2.01/1.00  sup_time_sim_immed:                     0.
% 2.01/1.00  
% 2.01/1.00  sup_num_of_clauses:                     38
% 2.01/1.00  sup_num_in_active:                      22
% 2.01/1.00  sup_num_in_passive:                     16
% 2.01/1.00  sup_num_of_loops:                       43
% 2.01/1.00  sup_fw_superposition:                   9
% 2.01/1.00  sup_bw_superposition:                   16
% 2.01/1.00  sup_immediate_simplified:               6
% 2.01/1.00  sup_given_eliminated:                   0
% 2.01/1.00  comparisons_done:                       0
% 2.01/1.00  comparisons_avoided:                    3
% 2.01/1.00  
% 2.01/1.00  ------ Simplifications
% 2.01/1.00  
% 2.01/1.00  
% 2.01/1.00  sim_fw_subset_subsumed:                 3
% 2.01/1.00  sim_bw_subset_subsumed:                 2
% 2.01/1.00  sim_fw_subsumed:                        1
% 2.01/1.00  sim_bw_subsumed:                        0
% 2.01/1.00  sim_fw_subsumption_res:                 1
% 2.01/1.00  sim_bw_subsumption_res:                 0
% 2.01/1.00  sim_tautology_del:                      0
% 2.01/1.00  sim_eq_tautology_del:                   3
% 2.01/1.00  sim_eq_res_simp:                        1
% 2.01/1.00  sim_fw_demodulated:                     2
% 2.01/1.00  sim_bw_demodulated:                     21
% 2.01/1.00  sim_light_normalised:                   4
% 2.01/1.00  sim_joinable_taut:                      0
% 2.01/1.00  sim_joinable_simp:                      0
% 2.01/1.00  sim_ac_normalised:                      0
% 2.01/1.00  sim_smt_subsumption:                    0
% 2.01/1.00  
%------------------------------------------------------------------------------
