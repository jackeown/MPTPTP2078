%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:56 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :  156 (1544 expanded)
%              Number of clauses        :   88 ( 572 expanded)
%              Number of leaves         :   21 ( 345 expanded)
%              Depth                    :   23
%              Number of atoms          :  512 (6364 expanded)
%              Number of equality atoms :  228 (2014 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f48,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK7(X3)) = X3
        & r2_hidden(sK7(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
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

fof(f49,plain,
    ( k2_relset_1(sK4,sK5,sK6) != sK5
    & ! [X3] :
        ( ( k1_funct_1(sK6,sK7(X3)) = X3
          & r2_hidden(sK7(X3),sK4) )
        | ~ r2_hidden(X3,sK5) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK6,sK4,sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f33,f48,f47])).

fof(f82,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f14,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f81,plain,(
    v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f84,plain,(
    ! [X3] :
      ( k1_funct_1(sK6,sK7(X3)) = X3
      | ~ r2_hidden(X3,sK5) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f85,plain,(
    k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f44,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f41,f44,f43,f42])).

fof(f66,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f89,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f90,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f89])).

fof(f80,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f83,plain,(
    ! [X3] :
      ( r2_hidden(sK7(X3),sK4)
      | ~ r2_hidden(X3,sK5) ) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2669,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2668,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2664,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3032,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2668,c_2664])).

cnf(c_4582,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2669,c_3032])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2659,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_21,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_8,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_468,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_21,c_8])).

cnf(c_2656,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_468])).

cnf(c_3455,plain,
    ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2659,c_2656])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_278,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_279,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_278])).

cnf(c_347,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_279])).

cnf(c_2658,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_347])).

cnf(c_4374,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3455,c_2658])).

cnf(c_5132,plain,
    ( k2_relat_1(sK6) = X0
    | r2_hidden(sK0(k2_relat_1(sK6),X0),X0) = iProver_top
    | r2_hidden(sK0(k2_relat_1(sK6),X0),sK5) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2669,c_4374])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2666,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3092,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2659,c_2666])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_350,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_279])).

cnf(c_2657,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_350])).

cnf(c_9581,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3092,c_2657])).

cnf(c_9,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2665,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_9726,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9581,c_2665])).

cnf(c_11824,plain,
    ( r2_hidden(sK0(k2_relat_1(sK6),X0),sK5) = iProver_top
    | r2_hidden(sK0(k2_relat_1(sK6),X0),X0) = iProver_top
    | k2_relat_1(sK6) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5132,c_9726])).

cnf(c_11825,plain,
    ( k2_relat_1(sK6) = X0
    | r2_hidden(sK0(k2_relat_1(sK6),X0),X0) = iProver_top
    | r2_hidden(sK0(k2_relat_1(sK6),X0),sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_11824])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2670,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) != iProver_top
    | r2_hidden(sK0(X1,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_11836,plain,
    ( k2_relat_1(sK6) = X0
    | r2_hidden(sK0(k2_relat_1(sK6),X0),k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK6),X0),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_11825,c_2670])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1229,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK6 != X0
    | sK5 != X2
    | sK4 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_34])).

cnf(c_1230,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k1_relset_1(sK4,sK5,sK6) = sK4
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_1229])).

cnf(c_1232,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | k1_xboole_0 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1230,c_33])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2663,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3669,plain,
    ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_2659,c_2663])).

cnf(c_3996,plain,
    ( k1_relat_1(sK6) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1232,c_3669])).

cnf(c_31,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | k1_funct_1(sK6,sK7(X0)) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2661,plain,
    ( k1_funct_1(sK6,sK7(X0)) = X0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_11833,plain,
    ( k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),X0))) = sK0(k2_relat_1(sK6),X0)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK0(k2_relat_1(sK6),X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11825,c_2661])).

cnf(c_12095,plain,
    ( k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),sK5))) = sK0(k2_relat_1(sK6),sK5)
    | k2_relat_1(sK6) = sK5 ),
    inference(superposition,[status(thm)],[c_11833,c_2661])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2662,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3561,plain,
    ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_2659,c_2662])).

cnf(c_30,negated_conjecture,
    ( k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3852,plain,
    ( k2_relat_1(sK6) != sK5 ),
    inference(demodulation,[status(thm)],[c_3561,c_30])).

cnf(c_12243,plain,
    ( k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),sK5))) = sK0(k2_relat_1(sK6),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12095,c_3852])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_723,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_35])).

cnf(c_724,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_723])).

cnf(c_2651,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_724])).

cnf(c_5135,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),sK5) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2651,c_4374])).

cnf(c_12246,plain,
    ( r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) = iProver_top
    | r2_hidden(sK7(sK0(k2_relat_1(sK6),sK5)),k1_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_12243,c_5135])).

cnf(c_2913,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2011,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2894,plain,
    ( k2_relset_1(sK4,sK5,sK6) != X0
    | k2_relset_1(sK4,sK5,sK6) = sK5
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_2011])).

cnf(c_2994,plain,
    ( k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6)
    | k2_relset_1(sK4,sK5,sK6) = sK5
    | sK5 != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2894])).

cnf(c_3076,plain,
    ( ~ r2_hidden(sK0(X0,sK5),X0)
    | ~ r2_hidden(sK0(X0,sK5),sK5)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_6223,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
    | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5)
    | sK5 = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_3076])).

cnf(c_6227,plain,
    ( sK5 = k2_relat_1(sK6)
    | r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6223])).

cnf(c_11864,plain,
    ( k2_relat_1(sK6) = sK5
    | r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_11825])).

cnf(c_11866,plain,
    ( k2_relat_1(sK6) = sK5
    | r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_11864])).

cnf(c_12248,plain,
    ( r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK7(sK0(k2_relat_1(sK6),sK5)),k1_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_12243,c_2651])).

cnf(c_12364,plain,
    ( r2_hidden(sK7(sK0(k2_relat_1(sK6),sK5)),k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12246,c_33,c_30,c_2913,c_2994,c_3852,c_6227,c_9726,c_11866,c_12248])).

cnf(c_12370,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK7(sK0(k2_relat_1(sK6),sK5)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3996,c_12364])).

cnf(c_32,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(sK7(X0),sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3173,plain,
    ( ~ r2_hidden(sK0(X0,sK5),sK5)
    | r2_hidden(sK7(sK0(X0,sK5)),sK4) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_6224,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5)
    | r2_hidden(sK7(sK0(k2_relat_1(sK6),sK5)),sK4) ),
    inference(instantiation,[status(thm)],[c_3173])).

cnf(c_6225,plain,
    ( r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) != iProver_top
    | r2_hidden(sK7(sK0(k2_relat_1(sK6),sK5)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6224])).

cnf(c_12624,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12370,c_3852,c_6225,c_11866])).

cnf(c_12943,plain,
    ( k2_relat_1(sK6) = X0
    | r2_hidden(sK0(k2_relat_1(sK6),X0),k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK6),X0),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11836,c_12624])).

cnf(c_12947,plain,
    ( k2_relat_1(sK6) = X0
    | r2_hidden(sK0(k2_relat_1(sK6),X0),k2_relat_1(sK6)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12943,c_3032])).

cnf(c_12957,plain,
    ( k2_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4582,c_12947])).

cnf(c_3082,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_2011])).

cnf(c_3795,plain,
    ( k2_relat_1(sK6) != X0
    | sK5 != X0
    | sK5 = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_3082])).

cnf(c_3796,plain,
    ( k2_relat_1(sK6) != k1_xboole_0
    | sK5 = k2_relat_1(sK6)
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3795])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12957,c_12370,c_11866,c_6225,c_3852,c_3796,c_2994,c_2913,c_30,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:38:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.49/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.01  
% 3.49/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.49/1.01  
% 3.49/1.01  ------  iProver source info
% 3.49/1.01  
% 3.49/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.49/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.49/1.01  git: non_committed_changes: false
% 3.49/1.01  git: last_make_outside_of_git: false
% 3.49/1.01  
% 3.49/1.01  ------ 
% 3.49/1.01  
% 3.49/1.01  ------ Input Options
% 3.49/1.01  
% 3.49/1.01  --out_options                           all
% 3.49/1.01  --tptp_safe_out                         true
% 3.49/1.01  --problem_path                          ""
% 3.49/1.01  --include_path                          ""
% 3.49/1.01  --clausifier                            res/vclausify_rel
% 3.49/1.01  --clausifier_options                    --mode clausify
% 3.49/1.01  --stdin                                 false
% 3.49/1.01  --stats_out                             all
% 3.49/1.01  
% 3.49/1.01  ------ General Options
% 3.49/1.01  
% 3.49/1.01  --fof                                   false
% 3.49/1.01  --time_out_real                         305.
% 3.49/1.01  --time_out_virtual                      -1.
% 3.49/1.01  --symbol_type_check                     false
% 3.49/1.01  --clausify_out                          false
% 3.49/1.01  --sig_cnt_out                           false
% 3.49/1.01  --trig_cnt_out                          false
% 3.49/1.01  --trig_cnt_out_tolerance                1.
% 3.49/1.01  --trig_cnt_out_sk_spl                   false
% 3.49/1.01  --abstr_cl_out                          false
% 3.49/1.01  
% 3.49/1.01  ------ Global Options
% 3.49/1.01  
% 3.49/1.01  --schedule                              default
% 3.49/1.01  --add_important_lit                     false
% 3.49/1.01  --prop_solver_per_cl                    1000
% 3.49/1.01  --min_unsat_core                        false
% 3.49/1.01  --soft_assumptions                      false
% 3.49/1.01  --soft_lemma_size                       3
% 3.49/1.01  --prop_impl_unit_size                   0
% 3.49/1.01  --prop_impl_unit                        []
% 3.49/1.01  --share_sel_clauses                     true
% 3.49/1.01  --reset_solvers                         false
% 3.49/1.01  --bc_imp_inh                            [conj_cone]
% 3.49/1.01  --conj_cone_tolerance                   3.
% 3.49/1.01  --extra_neg_conj                        none
% 3.49/1.01  --large_theory_mode                     true
% 3.49/1.01  --prolific_symb_bound                   200
% 3.49/1.01  --lt_threshold                          2000
% 3.49/1.01  --clause_weak_htbl                      true
% 3.49/1.01  --gc_record_bc_elim                     false
% 3.49/1.01  
% 3.49/1.01  ------ Preprocessing Options
% 3.49/1.01  
% 3.49/1.01  --preprocessing_flag                    true
% 3.49/1.01  --time_out_prep_mult                    0.1
% 3.49/1.01  --splitting_mode                        input
% 3.49/1.01  --splitting_grd                         true
% 3.49/1.01  --splitting_cvd                         false
% 3.49/1.01  --splitting_cvd_svl                     false
% 3.49/1.01  --splitting_nvd                         32
% 3.49/1.01  --sub_typing                            true
% 3.49/1.01  --prep_gs_sim                           true
% 3.49/1.01  --prep_unflatten                        true
% 3.49/1.01  --prep_res_sim                          true
% 3.49/1.01  --prep_upred                            true
% 3.49/1.01  --prep_sem_filter                       exhaustive
% 3.49/1.01  --prep_sem_filter_out                   false
% 3.49/1.01  --pred_elim                             true
% 3.49/1.01  --res_sim_input                         true
% 3.49/1.01  --eq_ax_congr_red                       true
% 3.49/1.01  --pure_diseq_elim                       true
% 3.49/1.01  --brand_transform                       false
% 3.49/1.01  --non_eq_to_eq                          false
% 3.49/1.01  --prep_def_merge                        true
% 3.49/1.01  --prep_def_merge_prop_impl              false
% 3.49/1.01  --prep_def_merge_mbd                    true
% 3.49/1.01  --prep_def_merge_tr_red                 false
% 3.49/1.01  --prep_def_merge_tr_cl                  false
% 3.49/1.01  --smt_preprocessing                     true
% 3.49/1.01  --smt_ac_axioms                         fast
% 3.49/1.01  --preprocessed_out                      false
% 3.49/1.01  --preprocessed_stats                    false
% 3.49/1.01  
% 3.49/1.01  ------ Abstraction refinement Options
% 3.49/1.01  
% 3.49/1.01  --abstr_ref                             []
% 3.49/1.01  --abstr_ref_prep                        false
% 3.49/1.01  --abstr_ref_until_sat                   false
% 3.49/1.01  --abstr_ref_sig_restrict                funpre
% 3.49/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.49/1.01  --abstr_ref_under                       []
% 3.49/1.01  
% 3.49/1.01  ------ SAT Options
% 3.49/1.01  
% 3.49/1.01  --sat_mode                              false
% 3.49/1.01  --sat_fm_restart_options                ""
% 3.49/1.01  --sat_gr_def                            false
% 3.49/1.01  --sat_epr_types                         true
% 3.49/1.01  --sat_non_cyclic_types                  false
% 3.49/1.01  --sat_finite_models                     false
% 3.49/1.01  --sat_fm_lemmas                         false
% 3.49/1.01  --sat_fm_prep                           false
% 3.49/1.01  --sat_fm_uc_incr                        true
% 3.49/1.01  --sat_out_model                         small
% 3.49/1.01  --sat_out_clauses                       false
% 3.49/1.01  
% 3.49/1.01  ------ QBF Options
% 3.49/1.01  
% 3.49/1.01  --qbf_mode                              false
% 3.49/1.01  --qbf_elim_univ                         false
% 3.49/1.01  --qbf_dom_inst                          none
% 3.49/1.01  --qbf_dom_pre_inst                      false
% 3.49/1.01  --qbf_sk_in                             false
% 3.49/1.01  --qbf_pred_elim                         true
% 3.49/1.01  --qbf_split                             512
% 3.49/1.01  
% 3.49/1.01  ------ BMC1 Options
% 3.49/1.01  
% 3.49/1.01  --bmc1_incremental                      false
% 3.49/1.01  --bmc1_axioms                           reachable_all
% 3.49/1.01  --bmc1_min_bound                        0
% 3.49/1.01  --bmc1_max_bound                        -1
% 3.49/1.01  --bmc1_max_bound_default                -1
% 3.49/1.01  --bmc1_symbol_reachability              true
% 3.49/1.01  --bmc1_property_lemmas                  false
% 3.49/1.01  --bmc1_k_induction                      false
% 3.49/1.01  --bmc1_non_equiv_states                 false
% 3.49/1.01  --bmc1_deadlock                         false
% 3.49/1.01  --bmc1_ucm                              false
% 3.49/1.01  --bmc1_add_unsat_core                   none
% 3.49/1.01  --bmc1_unsat_core_children              false
% 3.49/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.49/1.01  --bmc1_out_stat                         full
% 3.49/1.01  --bmc1_ground_init                      false
% 3.49/1.01  --bmc1_pre_inst_next_state              false
% 3.49/1.01  --bmc1_pre_inst_state                   false
% 3.49/1.01  --bmc1_pre_inst_reach_state             false
% 3.49/1.01  --bmc1_out_unsat_core                   false
% 3.49/1.01  --bmc1_aig_witness_out                  false
% 3.49/1.01  --bmc1_verbose                          false
% 3.49/1.01  --bmc1_dump_clauses_tptp                false
% 3.49/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.49/1.01  --bmc1_dump_file                        -
% 3.49/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.49/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.49/1.01  --bmc1_ucm_extend_mode                  1
% 3.49/1.01  --bmc1_ucm_init_mode                    2
% 3.49/1.01  --bmc1_ucm_cone_mode                    none
% 3.49/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.49/1.01  --bmc1_ucm_relax_model                  4
% 3.49/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.49/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.49/1.01  --bmc1_ucm_layered_model                none
% 3.49/1.01  --bmc1_ucm_max_lemma_size               10
% 3.49/1.01  
% 3.49/1.01  ------ AIG Options
% 3.49/1.01  
% 3.49/1.01  --aig_mode                              false
% 3.49/1.01  
% 3.49/1.01  ------ Instantiation Options
% 3.49/1.01  
% 3.49/1.01  --instantiation_flag                    true
% 3.49/1.01  --inst_sos_flag                         false
% 3.49/1.01  --inst_sos_phase                        true
% 3.49/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.49/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.49/1.01  --inst_lit_sel_side                     num_symb
% 3.49/1.01  --inst_solver_per_active                1400
% 3.49/1.01  --inst_solver_calls_frac                1.
% 3.49/1.01  --inst_passive_queue_type               priority_queues
% 3.49/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.49/1.01  --inst_passive_queues_freq              [25;2]
% 3.49/1.01  --inst_dismatching                      true
% 3.49/1.01  --inst_eager_unprocessed_to_passive     true
% 3.49/1.01  --inst_prop_sim_given                   true
% 3.49/1.01  --inst_prop_sim_new                     false
% 3.49/1.01  --inst_subs_new                         false
% 3.49/1.01  --inst_eq_res_simp                      false
% 3.49/1.01  --inst_subs_given                       false
% 3.49/1.01  --inst_orphan_elimination               true
% 3.49/1.01  --inst_learning_loop_flag               true
% 3.49/1.01  --inst_learning_start                   3000
% 3.49/1.01  --inst_learning_factor                  2
% 3.49/1.01  --inst_start_prop_sim_after_learn       3
% 3.49/1.01  --inst_sel_renew                        solver
% 3.49/1.01  --inst_lit_activity_flag                true
% 3.49/1.01  --inst_restr_to_given                   false
% 3.49/1.01  --inst_activity_threshold               500
% 3.49/1.01  --inst_out_proof                        true
% 3.49/1.01  
% 3.49/1.01  ------ Resolution Options
% 3.49/1.01  
% 3.49/1.01  --resolution_flag                       true
% 3.49/1.01  --res_lit_sel                           adaptive
% 3.49/1.01  --res_lit_sel_side                      none
% 3.49/1.01  --res_ordering                          kbo
% 3.49/1.01  --res_to_prop_solver                    active
% 3.49/1.01  --res_prop_simpl_new                    false
% 3.49/1.01  --res_prop_simpl_given                  true
% 3.49/1.01  --res_passive_queue_type                priority_queues
% 3.49/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.49/1.01  --res_passive_queues_freq               [15;5]
% 3.49/1.01  --res_forward_subs                      full
% 3.49/1.01  --res_backward_subs                     full
% 3.49/1.01  --res_forward_subs_resolution           true
% 3.49/1.01  --res_backward_subs_resolution          true
% 3.49/1.01  --res_orphan_elimination                true
% 3.49/1.01  --res_time_limit                        2.
% 3.49/1.01  --res_out_proof                         true
% 3.49/1.01  
% 3.49/1.01  ------ Superposition Options
% 3.49/1.01  
% 3.49/1.01  --superposition_flag                    true
% 3.49/1.01  --sup_passive_queue_type                priority_queues
% 3.49/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.49/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.49/1.01  --demod_completeness_check              fast
% 3.49/1.01  --demod_use_ground                      true
% 3.49/1.01  --sup_to_prop_solver                    passive
% 3.49/1.01  --sup_prop_simpl_new                    true
% 3.49/1.01  --sup_prop_simpl_given                  true
% 3.49/1.01  --sup_fun_splitting                     false
% 3.49/1.01  --sup_smt_interval                      50000
% 3.49/1.01  
% 3.49/1.01  ------ Superposition Simplification Setup
% 3.49/1.01  
% 3.49/1.01  --sup_indices_passive                   []
% 3.49/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.49/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.49/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.49/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.49/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.49/1.01  --sup_full_bw                           [BwDemod]
% 3.49/1.01  --sup_immed_triv                        [TrivRules]
% 3.49/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.49/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.49/1.01  --sup_immed_bw_main                     []
% 3.49/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.49/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.49/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.49/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.49/1.01  
% 3.49/1.01  ------ Combination Options
% 3.49/1.01  
% 3.49/1.01  --comb_res_mult                         3
% 3.49/1.01  --comb_sup_mult                         2
% 3.49/1.01  --comb_inst_mult                        10
% 3.49/1.01  
% 3.49/1.01  ------ Debug Options
% 3.49/1.01  
% 3.49/1.01  --dbg_backtrace                         false
% 3.49/1.01  --dbg_dump_prop_clauses                 false
% 3.49/1.01  --dbg_dump_prop_clauses_file            -
% 3.49/1.01  --dbg_out_stat                          false
% 3.49/1.01  ------ Parsing...
% 3.49/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.49/1.01  
% 3.49/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.49/1.01  
% 3.49/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.49/1.01  
% 3.49/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.49/1.01  ------ Proving...
% 3.49/1.01  ------ Problem Properties 
% 3.49/1.01  
% 3.49/1.01  
% 3.49/1.01  clauses                                 28
% 3.49/1.01  conjectures                             4
% 3.49/1.01  EPR                                     4
% 3.49/1.01  Horn                                    22
% 3.49/1.01  unary                                   4
% 3.49/1.01  binary                                  8
% 3.49/1.01  lits                                    74
% 3.49/1.01  lits eq                                 21
% 3.49/1.01  fd_pure                                 0
% 3.49/1.01  fd_pseudo                               0
% 3.49/1.01  fd_cond                                 3
% 3.49/1.01  fd_pseudo_cond                          3
% 3.49/1.01  AC symbols                              0
% 3.49/1.01  
% 3.49/1.01  ------ Schedule dynamic 5 is on 
% 3.49/1.01  
% 3.49/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.49/1.01  
% 3.49/1.01  
% 3.49/1.01  ------ 
% 3.49/1.01  Current options:
% 3.49/1.01  ------ 
% 3.49/1.01  
% 3.49/1.01  ------ Input Options
% 3.49/1.01  
% 3.49/1.01  --out_options                           all
% 3.49/1.01  --tptp_safe_out                         true
% 3.49/1.01  --problem_path                          ""
% 3.49/1.01  --include_path                          ""
% 3.49/1.01  --clausifier                            res/vclausify_rel
% 3.49/1.01  --clausifier_options                    --mode clausify
% 3.49/1.01  --stdin                                 false
% 3.49/1.01  --stats_out                             all
% 3.49/1.01  
% 3.49/1.01  ------ General Options
% 3.49/1.01  
% 3.49/1.01  --fof                                   false
% 3.49/1.01  --time_out_real                         305.
% 3.49/1.01  --time_out_virtual                      -1.
% 3.49/1.01  --symbol_type_check                     false
% 3.49/1.01  --clausify_out                          false
% 3.49/1.01  --sig_cnt_out                           false
% 3.49/1.01  --trig_cnt_out                          false
% 3.49/1.01  --trig_cnt_out_tolerance                1.
% 3.49/1.01  --trig_cnt_out_sk_spl                   false
% 3.49/1.01  --abstr_cl_out                          false
% 3.49/1.01  
% 3.49/1.01  ------ Global Options
% 3.49/1.01  
% 3.49/1.01  --schedule                              default
% 3.49/1.01  --add_important_lit                     false
% 3.49/1.01  --prop_solver_per_cl                    1000
% 3.49/1.01  --min_unsat_core                        false
% 3.49/1.01  --soft_assumptions                      false
% 3.49/1.01  --soft_lemma_size                       3
% 3.49/1.01  --prop_impl_unit_size                   0
% 3.49/1.01  --prop_impl_unit                        []
% 3.49/1.01  --share_sel_clauses                     true
% 3.49/1.01  --reset_solvers                         false
% 3.49/1.01  --bc_imp_inh                            [conj_cone]
% 3.49/1.01  --conj_cone_tolerance                   3.
% 3.49/1.01  --extra_neg_conj                        none
% 3.49/1.01  --large_theory_mode                     true
% 3.49/1.01  --prolific_symb_bound                   200
% 3.49/1.01  --lt_threshold                          2000
% 3.49/1.01  --clause_weak_htbl                      true
% 3.49/1.01  --gc_record_bc_elim                     false
% 3.49/1.01  
% 3.49/1.01  ------ Preprocessing Options
% 3.49/1.01  
% 3.49/1.01  --preprocessing_flag                    true
% 3.49/1.01  --time_out_prep_mult                    0.1
% 3.49/1.01  --splitting_mode                        input
% 3.49/1.01  --splitting_grd                         true
% 3.49/1.01  --splitting_cvd                         false
% 3.49/1.01  --splitting_cvd_svl                     false
% 3.49/1.01  --splitting_nvd                         32
% 3.49/1.01  --sub_typing                            true
% 3.49/1.01  --prep_gs_sim                           true
% 3.49/1.01  --prep_unflatten                        true
% 3.49/1.01  --prep_res_sim                          true
% 3.49/1.01  --prep_upred                            true
% 3.49/1.01  --prep_sem_filter                       exhaustive
% 3.49/1.01  --prep_sem_filter_out                   false
% 3.49/1.01  --pred_elim                             true
% 3.49/1.01  --res_sim_input                         true
% 3.49/1.01  --eq_ax_congr_red                       true
% 3.49/1.01  --pure_diseq_elim                       true
% 3.49/1.01  --brand_transform                       false
% 3.49/1.01  --non_eq_to_eq                          false
% 3.49/1.01  --prep_def_merge                        true
% 3.49/1.01  --prep_def_merge_prop_impl              false
% 3.49/1.01  --prep_def_merge_mbd                    true
% 3.49/1.01  --prep_def_merge_tr_red                 false
% 3.49/1.01  --prep_def_merge_tr_cl                  false
% 3.49/1.01  --smt_preprocessing                     true
% 3.49/1.01  --smt_ac_axioms                         fast
% 3.49/1.01  --preprocessed_out                      false
% 3.49/1.01  --preprocessed_stats                    false
% 3.49/1.01  
% 3.49/1.01  ------ Abstraction refinement Options
% 3.49/1.01  
% 3.49/1.01  --abstr_ref                             []
% 3.49/1.01  --abstr_ref_prep                        false
% 3.49/1.01  --abstr_ref_until_sat                   false
% 3.49/1.01  --abstr_ref_sig_restrict                funpre
% 3.49/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.49/1.01  --abstr_ref_under                       []
% 3.49/1.01  
% 3.49/1.01  ------ SAT Options
% 3.49/1.01  
% 3.49/1.01  --sat_mode                              false
% 3.49/1.01  --sat_fm_restart_options                ""
% 3.49/1.01  --sat_gr_def                            false
% 3.49/1.01  --sat_epr_types                         true
% 3.49/1.01  --sat_non_cyclic_types                  false
% 3.49/1.01  --sat_finite_models                     false
% 3.49/1.01  --sat_fm_lemmas                         false
% 3.49/1.01  --sat_fm_prep                           false
% 3.49/1.01  --sat_fm_uc_incr                        true
% 3.49/1.01  --sat_out_model                         small
% 3.49/1.01  --sat_out_clauses                       false
% 3.49/1.01  
% 3.49/1.01  ------ QBF Options
% 3.49/1.01  
% 3.49/1.01  --qbf_mode                              false
% 3.49/1.01  --qbf_elim_univ                         false
% 3.49/1.01  --qbf_dom_inst                          none
% 3.49/1.01  --qbf_dom_pre_inst                      false
% 3.49/1.01  --qbf_sk_in                             false
% 3.49/1.01  --qbf_pred_elim                         true
% 3.49/1.01  --qbf_split                             512
% 3.49/1.01  
% 3.49/1.01  ------ BMC1 Options
% 3.49/1.01  
% 3.49/1.01  --bmc1_incremental                      false
% 3.49/1.01  --bmc1_axioms                           reachable_all
% 3.49/1.01  --bmc1_min_bound                        0
% 3.49/1.01  --bmc1_max_bound                        -1
% 3.49/1.01  --bmc1_max_bound_default                -1
% 3.49/1.01  --bmc1_symbol_reachability              true
% 3.49/1.01  --bmc1_property_lemmas                  false
% 3.49/1.01  --bmc1_k_induction                      false
% 3.49/1.01  --bmc1_non_equiv_states                 false
% 3.49/1.01  --bmc1_deadlock                         false
% 3.49/1.01  --bmc1_ucm                              false
% 3.49/1.01  --bmc1_add_unsat_core                   none
% 3.49/1.01  --bmc1_unsat_core_children              false
% 3.49/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.49/1.01  --bmc1_out_stat                         full
% 3.49/1.01  --bmc1_ground_init                      false
% 3.49/1.01  --bmc1_pre_inst_next_state              false
% 3.49/1.01  --bmc1_pre_inst_state                   false
% 3.49/1.01  --bmc1_pre_inst_reach_state             false
% 3.49/1.01  --bmc1_out_unsat_core                   false
% 3.49/1.01  --bmc1_aig_witness_out                  false
% 3.49/1.01  --bmc1_verbose                          false
% 3.49/1.01  --bmc1_dump_clauses_tptp                false
% 3.49/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.49/1.01  --bmc1_dump_file                        -
% 3.49/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.49/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.49/1.01  --bmc1_ucm_extend_mode                  1
% 3.49/1.01  --bmc1_ucm_init_mode                    2
% 3.49/1.01  --bmc1_ucm_cone_mode                    none
% 3.49/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.49/1.01  --bmc1_ucm_relax_model                  4
% 3.49/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.49/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.49/1.01  --bmc1_ucm_layered_model                none
% 3.49/1.01  --bmc1_ucm_max_lemma_size               10
% 3.49/1.01  
% 3.49/1.01  ------ AIG Options
% 3.49/1.01  
% 3.49/1.01  --aig_mode                              false
% 3.49/1.01  
% 3.49/1.01  ------ Instantiation Options
% 3.49/1.01  
% 3.49/1.01  --instantiation_flag                    true
% 3.49/1.01  --inst_sos_flag                         false
% 3.49/1.01  --inst_sos_phase                        true
% 3.49/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.49/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.49/1.01  --inst_lit_sel_side                     none
% 3.49/1.01  --inst_solver_per_active                1400
% 3.49/1.01  --inst_solver_calls_frac                1.
% 3.49/1.01  --inst_passive_queue_type               priority_queues
% 3.49/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.49/1.01  --inst_passive_queues_freq              [25;2]
% 3.49/1.01  --inst_dismatching                      true
% 3.49/1.01  --inst_eager_unprocessed_to_passive     true
% 3.49/1.01  --inst_prop_sim_given                   true
% 3.49/1.01  --inst_prop_sim_new                     false
% 3.49/1.01  --inst_subs_new                         false
% 3.49/1.01  --inst_eq_res_simp                      false
% 3.49/1.01  --inst_subs_given                       false
% 3.49/1.01  --inst_orphan_elimination               true
% 3.49/1.01  --inst_learning_loop_flag               true
% 3.49/1.01  --inst_learning_start                   3000
% 3.49/1.01  --inst_learning_factor                  2
% 3.49/1.01  --inst_start_prop_sim_after_learn       3
% 3.49/1.01  --inst_sel_renew                        solver
% 3.49/1.01  --inst_lit_activity_flag                true
% 3.49/1.01  --inst_restr_to_given                   false
% 3.49/1.01  --inst_activity_threshold               500
% 3.49/1.01  --inst_out_proof                        true
% 3.49/1.01  
% 3.49/1.01  ------ Resolution Options
% 3.49/1.01  
% 3.49/1.01  --resolution_flag                       false
% 3.49/1.01  --res_lit_sel                           adaptive
% 3.49/1.01  --res_lit_sel_side                      none
% 3.49/1.01  --res_ordering                          kbo
% 3.49/1.01  --res_to_prop_solver                    active
% 3.49/1.01  --res_prop_simpl_new                    false
% 3.49/1.01  --res_prop_simpl_given                  true
% 3.49/1.01  --res_passive_queue_type                priority_queues
% 3.49/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.49/1.01  --res_passive_queues_freq               [15;5]
% 3.49/1.01  --res_forward_subs                      full
% 3.49/1.01  --res_backward_subs                     full
% 3.49/1.01  --res_forward_subs_resolution           true
% 3.49/1.01  --res_backward_subs_resolution          true
% 3.49/1.01  --res_orphan_elimination                true
% 3.49/1.01  --res_time_limit                        2.
% 3.49/1.01  --res_out_proof                         true
% 3.49/1.01  
% 3.49/1.01  ------ Superposition Options
% 3.49/1.01  
% 3.49/1.01  --superposition_flag                    true
% 3.49/1.01  --sup_passive_queue_type                priority_queues
% 3.49/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.49/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.49/1.01  --demod_completeness_check              fast
% 3.49/1.01  --demod_use_ground                      true
% 3.49/1.01  --sup_to_prop_solver                    passive
% 3.49/1.01  --sup_prop_simpl_new                    true
% 3.49/1.01  --sup_prop_simpl_given                  true
% 3.49/1.01  --sup_fun_splitting                     false
% 3.49/1.01  --sup_smt_interval                      50000
% 3.49/1.01  
% 3.49/1.01  ------ Superposition Simplification Setup
% 3.49/1.01  
% 3.49/1.01  --sup_indices_passive                   []
% 3.49/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.49/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.49/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.49/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.49/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.49/1.01  --sup_full_bw                           [BwDemod]
% 3.49/1.01  --sup_immed_triv                        [TrivRules]
% 3.49/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.49/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.49/1.01  --sup_immed_bw_main                     []
% 3.49/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.49/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.49/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.49/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.49/1.01  
% 3.49/1.01  ------ Combination Options
% 3.49/1.01  
% 3.49/1.01  --comb_res_mult                         3
% 3.49/1.01  --comb_sup_mult                         2
% 3.49/1.01  --comb_inst_mult                        10
% 3.49/1.01  
% 3.49/1.01  ------ Debug Options
% 3.49/1.01  
% 3.49/1.01  --dbg_backtrace                         false
% 3.49/1.01  --dbg_dump_prop_clauses                 false
% 3.49/1.01  --dbg_dump_prop_clauses_file            -
% 3.49/1.01  --dbg_out_stat                          false
% 3.49/1.01  
% 3.49/1.01  
% 3.49/1.01  
% 3.49/1.01  
% 3.49/1.01  ------ Proving...
% 3.49/1.01  
% 3.49/1.01  
% 3.49/1.01  % SZS status Theorem for theBenchmark.p
% 3.49/1.01  
% 3.49/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.49/1.01  
% 3.49/1.01  fof(f1,axiom,(
% 3.49/1.01    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 3.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f18,plain,(
% 3.49/1.01    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 3.49/1.01    inference(ennf_transformation,[],[f1])).
% 3.49/1.01  
% 3.49/1.01  fof(f34,plain,(
% 3.49/1.01    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 3.49/1.01    inference(nnf_transformation,[],[f18])).
% 3.49/1.01  
% 3.49/1.01  fof(f35,plain,(
% 3.49/1.01    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 3.49/1.01    introduced(choice_axiom,[])).
% 3.49/1.01  
% 3.49/1.01  fof(f36,plain,(
% 3.49/1.01    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 3.49/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 3.49/1.01  
% 3.49/1.01  fof(f50,plain,(
% 3.49/1.01    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f36])).
% 3.49/1.01  
% 3.49/1.01  fof(f2,axiom,(
% 3.49/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f52,plain,(
% 3.49/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f2])).
% 3.49/1.01  
% 3.49/1.01  fof(f10,axiom,(
% 3.49/1.01    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f26,plain,(
% 3.49/1.01    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.49/1.01    inference(ennf_transformation,[],[f10])).
% 3.49/1.01  
% 3.49/1.01  fof(f70,plain,(
% 3.49/1.01    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f26])).
% 3.49/1.01  
% 3.49/1.01  fof(f15,conjecture,(
% 3.49/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 3.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f16,negated_conjecture,(
% 3.49/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 3.49/1.01    inference(negated_conjecture,[],[f15])).
% 3.49/1.01  
% 3.49/1.01  fof(f32,plain,(
% 3.49/1.01    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.49/1.01    inference(ennf_transformation,[],[f16])).
% 3.49/1.01  
% 3.49/1.01  fof(f33,plain,(
% 3.49/1.01    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.49/1.01    inference(flattening,[],[f32])).
% 3.49/1.01  
% 3.49/1.01  fof(f48,plain,(
% 3.49/1.01    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK7(X3)) = X3 & r2_hidden(sK7(X3),X0)))) )),
% 3.49/1.01    introduced(choice_axiom,[])).
% 3.49/1.01  
% 3.49/1.01  fof(f47,plain,(
% 3.49/1.01    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK4,sK5,sK6) != sK5 & ! [X3] : (? [X4] : (k1_funct_1(sK6,X4) = X3 & r2_hidden(X4,sK4)) | ~r2_hidden(X3,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6))),
% 3.49/1.01    introduced(choice_axiom,[])).
% 3.49/1.01  
% 3.49/1.01  fof(f49,plain,(
% 3.49/1.01    k2_relset_1(sK4,sK5,sK6) != sK5 & ! [X3] : ((k1_funct_1(sK6,sK7(X3)) = X3 & r2_hidden(sK7(X3),sK4)) | ~r2_hidden(X3,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6)),
% 3.49/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f33,f48,f47])).
% 3.49/1.01  
% 3.49/1.01  fof(f82,plain,(
% 3.49/1.01    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 3.49/1.01    inference(cnf_transformation,[],[f49])).
% 3.49/1.01  
% 3.49/1.01  fof(f11,axiom,(
% 3.49/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f17,plain,(
% 3.49/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.49/1.01    inference(pure_predicate_removal,[],[f11])).
% 3.49/1.01  
% 3.49/1.01  fof(f27,plain,(
% 3.49/1.01    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.49/1.01    inference(ennf_transformation,[],[f17])).
% 3.49/1.01  
% 3.49/1.01  fof(f71,plain,(
% 3.49/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.49/1.01    inference(cnf_transformation,[],[f27])).
% 3.49/1.01  
% 3.49/1.01  fof(f6,axiom,(
% 3.49/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f21,plain,(
% 3.49/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.49/1.01    inference(ennf_transformation,[],[f6])).
% 3.49/1.01  
% 3.49/1.01  fof(f38,plain,(
% 3.49/1.01    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.49/1.01    inference(nnf_transformation,[],[f21])).
% 3.49/1.01  
% 3.49/1.01  fof(f57,plain,(
% 3.49/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f38])).
% 3.49/1.01  
% 3.49/1.01  fof(f3,axiom,(
% 3.49/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f19,plain,(
% 3.49/1.01    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.49/1.01    inference(ennf_transformation,[],[f3])).
% 3.49/1.01  
% 3.49/1.01  fof(f53,plain,(
% 3.49/1.01    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.49/1.01    inference(cnf_transformation,[],[f19])).
% 3.49/1.01  
% 3.49/1.01  fof(f4,axiom,(
% 3.49/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f37,plain,(
% 3.49/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.49/1.01    inference(nnf_transformation,[],[f4])).
% 3.49/1.01  
% 3.49/1.01  fof(f55,plain,(
% 3.49/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f37])).
% 3.49/1.01  
% 3.49/1.01  fof(f54,plain,(
% 3.49/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.49/1.01    inference(cnf_transformation,[],[f37])).
% 3.49/1.01  
% 3.49/1.01  fof(f5,axiom,(
% 3.49/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f20,plain,(
% 3.49/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.49/1.01    inference(ennf_transformation,[],[f5])).
% 3.49/1.01  
% 3.49/1.01  fof(f56,plain,(
% 3.49/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f20])).
% 3.49/1.01  
% 3.49/1.01  fof(f7,axiom,(
% 3.49/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f59,plain,(
% 3.49/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.49/1.01    inference(cnf_transformation,[],[f7])).
% 3.49/1.01  
% 3.49/1.01  fof(f51,plain,(
% 3.49/1.01    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f36])).
% 3.49/1.01  
% 3.49/1.01  fof(f14,axiom,(
% 3.49/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f30,plain,(
% 3.49/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.49/1.01    inference(ennf_transformation,[],[f14])).
% 3.49/1.01  
% 3.49/1.01  fof(f31,plain,(
% 3.49/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.49/1.01    inference(flattening,[],[f30])).
% 3.49/1.01  
% 3.49/1.01  fof(f46,plain,(
% 3.49/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.49/1.01    inference(nnf_transformation,[],[f31])).
% 3.49/1.01  
% 3.49/1.01  fof(f74,plain,(
% 3.49/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.49/1.01    inference(cnf_transformation,[],[f46])).
% 3.49/1.01  
% 3.49/1.01  fof(f81,plain,(
% 3.49/1.01    v1_funct_2(sK6,sK4,sK5)),
% 3.49/1.01    inference(cnf_transformation,[],[f49])).
% 3.49/1.01  
% 3.49/1.01  fof(f12,axiom,(
% 3.49/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f28,plain,(
% 3.49/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.49/1.01    inference(ennf_transformation,[],[f12])).
% 3.49/1.01  
% 3.49/1.01  fof(f72,plain,(
% 3.49/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.49/1.01    inference(cnf_transformation,[],[f28])).
% 3.49/1.01  
% 3.49/1.01  fof(f84,plain,(
% 3.49/1.01    ( ! [X3] : (k1_funct_1(sK6,sK7(X3)) = X3 | ~r2_hidden(X3,sK5)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f49])).
% 3.49/1.01  
% 3.49/1.01  fof(f13,axiom,(
% 3.49/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f29,plain,(
% 3.49/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.49/1.01    inference(ennf_transformation,[],[f13])).
% 3.49/1.01  
% 3.49/1.01  fof(f73,plain,(
% 3.49/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.49/1.01    inference(cnf_transformation,[],[f29])).
% 3.49/1.01  
% 3.49/1.01  fof(f85,plain,(
% 3.49/1.01    k2_relset_1(sK4,sK5,sK6) != sK5),
% 3.49/1.01    inference(cnf_transformation,[],[f49])).
% 3.49/1.01  
% 3.49/1.01  fof(f9,axiom,(
% 3.49/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f24,plain,(
% 3.49/1.01    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.49/1.01    inference(ennf_transformation,[],[f9])).
% 3.49/1.01  
% 3.49/1.01  fof(f25,plain,(
% 3.49/1.01    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.49/1.01    inference(flattening,[],[f24])).
% 3.49/1.01  
% 3.49/1.01  fof(f40,plain,(
% 3.49/1.01    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.49/1.01    inference(nnf_transformation,[],[f25])).
% 3.49/1.01  
% 3.49/1.01  fof(f41,plain,(
% 3.49/1.01    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.49/1.01    inference(rectify,[],[f40])).
% 3.49/1.01  
% 3.49/1.01  fof(f44,plain,(
% 3.49/1.01    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 3.49/1.01    introduced(choice_axiom,[])).
% 3.49/1.01  
% 3.49/1.01  fof(f43,plain,(
% 3.49/1.01    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 3.49/1.01    introduced(choice_axiom,[])).
% 3.49/1.01  
% 3.49/1.01  fof(f42,plain,(
% 3.49/1.01    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 3.49/1.01    introduced(choice_axiom,[])).
% 3.49/1.01  
% 3.49/1.01  fof(f45,plain,(
% 3.49/1.01    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.49/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f41,f44,f43,f42])).
% 3.49/1.01  
% 3.49/1.01  fof(f66,plain,(
% 3.49/1.01    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f45])).
% 3.49/1.01  
% 3.49/1.01  fof(f89,plain,(
% 3.49/1.01    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.49/1.01    inference(equality_resolution,[],[f66])).
% 3.49/1.01  
% 3.49/1.01  fof(f90,plain,(
% 3.49/1.01    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.49/1.01    inference(equality_resolution,[],[f89])).
% 3.49/1.01  
% 3.49/1.01  fof(f80,plain,(
% 3.49/1.01    v1_funct_1(sK6)),
% 3.49/1.01    inference(cnf_transformation,[],[f49])).
% 3.49/1.01  
% 3.49/1.01  fof(f83,plain,(
% 3.49/1.01    ( ! [X3] : (r2_hidden(sK7(X3),sK4) | ~r2_hidden(X3,sK5)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f49])).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1,plain,
% 3.49/1.01      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 3.49/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_2669,plain,
% 3.49/1.01      ( X0 = X1
% 3.49/1.01      | r2_hidden(sK0(X1,X0),X0) = iProver_top
% 3.49/1.01      | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_2,plain,
% 3.49/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 3.49/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_2668,plain,
% 3.49/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_20,plain,
% 3.49/1.01      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.49/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_2664,plain,
% 3.49/1.01      ( r1_tarski(X0,X1) != iProver_top
% 3.49/1.01      | r2_hidden(X1,X0) != iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_3032,plain,
% 3.49/1.01      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_2668,c_2664]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_4582,plain,
% 3.49/1.01      ( k1_xboole_0 = X0
% 3.49/1.01      | r2_hidden(sK0(X0,k1_xboole_0),X0) = iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_2669,c_3032]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_33,negated_conjecture,
% 3.49/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.49/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_2659,plain,
% 3.49/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_21,plain,
% 3.49/1.01      ( v5_relat_1(X0,X1)
% 3.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.49/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_8,plain,
% 3.49/1.01      ( ~ v5_relat_1(X0,X1)
% 3.49/1.01      | r1_tarski(k2_relat_1(X0),X1)
% 3.49/1.01      | ~ v1_relat_1(X0) ),
% 3.49/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_468,plain,
% 3.49/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.49/1.01      | r1_tarski(k2_relat_1(X0),X2)
% 3.49/1.01      | ~ v1_relat_1(X0) ),
% 3.49/1.01      inference(resolution,[status(thm)],[c_21,c_8]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_2656,plain,
% 3.49/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.49/1.01      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 3.49/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_468]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_3455,plain,
% 3.49/1.01      ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top
% 3.49/1.01      | v1_relat_1(sK6) != iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_2659,c_2656]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_3,plain,
% 3.49/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.49/1.01      | ~ r2_hidden(X2,X0)
% 3.49/1.01      | r2_hidden(X2,X1) ),
% 3.49/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_4,plain,
% 3.49/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.49/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_278,plain,
% 3.49/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.49/1.01      inference(prop_impl,[status(thm)],[c_4]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_279,plain,
% 3.49/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.49/1.01      inference(renaming,[status(thm)],[c_278]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_347,plain,
% 3.49/1.01      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.49/1.01      inference(bin_hyper_res,[status(thm)],[c_3,c_279]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_2658,plain,
% 3.49/1.01      ( r1_tarski(X0,X1) != iProver_top
% 3.49/1.01      | r2_hidden(X2,X0) != iProver_top
% 3.49/1.01      | r2_hidden(X2,X1) = iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_347]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_4374,plain,
% 3.49/1.01      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 3.49/1.01      | r2_hidden(X0,sK5) = iProver_top
% 3.49/1.01      | v1_relat_1(sK6) != iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_3455,c_2658]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_5132,plain,
% 3.49/1.01      ( k2_relat_1(sK6) = X0
% 3.49/1.01      | r2_hidden(sK0(k2_relat_1(sK6),X0),X0) = iProver_top
% 3.49/1.01      | r2_hidden(sK0(k2_relat_1(sK6),X0),sK5) = iProver_top
% 3.49/1.01      | v1_relat_1(sK6) != iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_2669,c_4374]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_5,plain,
% 3.49/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.49/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_2666,plain,
% 3.49/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.49/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_3092,plain,
% 3.49/1.01      ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_2659,c_2666]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_6,plain,
% 3.49/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.49/1.01      | ~ v1_relat_1(X1)
% 3.49/1.01      | v1_relat_1(X0) ),
% 3.49/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_350,plain,
% 3.49/1.01      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.49/1.01      inference(bin_hyper_res,[status(thm)],[c_6,c_279]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_2657,plain,
% 3.49/1.01      ( r1_tarski(X0,X1) != iProver_top
% 3.49/1.01      | v1_relat_1(X1) != iProver_top
% 3.49/1.01      | v1_relat_1(X0) = iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_350]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_9581,plain,
% 3.49/1.01      ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
% 3.49/1.01      | v1_relat_1(sK6) = iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_3092,c_2657]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_9,plain,
% 3.49/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.49/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_2665,plain,
% 3.49/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_9726,plain,
% 3.49/1.01      ( v1_relat_1(sK6) = iProver_top ),
% 3.49/1.01      inference(forward_subsumption_resolution,
% 3.49/1.01                [status(thm)],
% 3.49/1.01                [c_9581,c_2665]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_11824,plain,
% 3.49/1.01      ( r2_hidden(sK0(k2_relat_1(sK6),X0),sK5) = iProver_top
% 3.49/1.01      | r2_hidden(sK0(k2_relat_1(sK6),X0),X0) = iProver_top
% 3.49/1.01      | k2_relat_1(sK6) = X0 ),
% 3.49/1.01      inference(global_propositional_subsumption,
% 3.49/1.01                [status(thm)],
% 3.49/1.01                [c_5132,c_9726]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_11825,plain,
% 3.49/1.01      ( k2_relat_1(sK6) = X0
% 3.49/1.01      | r2_hidden(sK0(k2_relat_1(sK6),X0),X0) = iProver_top
% 3.49/1.01      | r2_hidden(sK0(k2_relat_1(sK6),X0),sK5) = iProver_top ),
% 3.49/1.01      inference(renaming,[status(thm)],[c_11824]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_0,plain,
% 3.49/1.01      ( ~ r2_hidden(sK0(X0,X1),X1)
% 3.49/1.01      | ~ r2_hidden(sK0(X0,X1),X0)
% 3.49/1.01      | X1 = X0 ),
% 3.49/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_2670,plain,
% 3.49/1.01      ( X0 = X1
% 3.49/1.01      | r2_hidden(sK0(X1,X0),X0) != iProver_top
% 3.49/1.01      | r2_hidden(sK0(X1,X0),X1) != iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_11836,plain,
% 3.49/1.01      ( k2_relat_1(sK6) = X0
% 3.49/1.01      | r2_hidden(sK0(k2_relat_1(sK6),X0),k2_relat_1(sK6)) != iProver_top
% 3.49/1.01      | r2_hidden(sK0(k2_relat_1(sK6),X0),sK5) = iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_11825,c_2670]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_29,plain,
% 3.49/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.49/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.49/1.01      | k1_xboole_0 = X2 ),
% 3.49/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_34,negated_conjecture,
% 3.49/1.01      ( v1_funct_2(sK6,sK4,sK5) ),
% 3.49/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1229,plain,
% 3.49/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.49/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.49/1.01      | sK6 != X0
% 3.49/1.01      | sK5 != X2
% 3.49/1.01      | sK4 != X1
% 3.49/1.01      | k1_xboole_0 = X2 ),
% 3.49/1.01      inference(resolution_lifted,[status(thm)],[c_29,c_34]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1230,plain,
% 3.49/1.01      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.49/1.01      | k1_relset_1(sK4,sK5,sK6) = sK4
% 3.49/1.01      | k1_xboole_0 = sK5 ),
% 3.49/1.01      inference(unflattening,[status(thm)],[c_1229]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1232,plain,
% 3.49/1.01      ( k1_relset_1(sK4,sK5,sK6) = sK4 | k1_xboole_0 = sK5 ),
% 3.49/1.01      inference(global_propositional_subsumption,
% 3.49/1.01                [status(thm)],
% 3.49/1.01                [c_1230,c_33]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_22,plain,
% 3.49/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.49/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.49/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_2663,plain,
% 3.49/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.49/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_3669,plain,
% 3.49/1.01      ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_2659,c_2663]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_3996,plain,
% 3.49/1.01      ( k1_relat_1(sK6) = sK4 | sK5 = k1_xboole_0 ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_1232,c_3669]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_31,negated_conjecture,
% 3.49/1.01      ( ~ r2_hidden(X0,sK5) | k1_funct_1(sK6,sK7(X0)) = X0 ),
% 3.49/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_2661,plain,
% 3.49/1.01      ( k1_funct_1(sK6,sK7(X0)) = X0 | r2_hidden(X0,sK5) != iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_11833,plain,
% 3.49/1.01      ( k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),X0))) = sK0(k2_relat_1(sK6),X0)
% 3.49/1.01      | k2_relat_1(sK6) = X0
% 3.49/1.01      | r2_hidden(sK0(k2_relat_1(sK6),X0),X0) = iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_11825,c_2661]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_12095,plain,
% 3.49/1.01      ( k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),sK5))) = sK0(k2_relat_1(sK6),sK5)
% 3.49/1.01      | k2_relat_1(sK6) = sK5 ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_11833,c_2661]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_23,plain,
% 3.49/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.49/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.49/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_2662,plain,
% 3.49/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.49/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_3561,plain,
% 3.49/1.01      ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_2659,c_2662]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_30,negated_conjecture,
% 3.49/1.01      ( k2_relset_1(sK4,sK5,sK6) != sK5 ),
% 3.49/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_3852,plain,
% 3.49/1.01      ( k2_relat_1(sK6) != sK5 ),
% 3.49/1.01      inference(demodulation,[status(thm)],[c_3561,c_30]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_12243,plain,
% 3.49/1.01      ( k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),sK5))) = sK0(k2_relat_1(sK6),sK5) ),
% 3.49/1.01      inference(global_propositional_subsumption,
% 3.49/1.01                [status(thm)],
% 3.49/1.01                [c_12095,c_3852]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_17,plain,
% 3.49/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.49/1.01      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.49/1.01      | ~ v1_funct_1(X1)
% 3.49/1.01      | ~ v1_relat_1(X1) ),
% 3.49/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_35,negated_conjecture,
% 3.49/1.01      ( v1_funct_1(sK6) ),
% 3.49/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_723,plain,
% 3.49/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.49/1.01      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.49/1.01      | ~ v1_relat_1(X1)
% 3.49/1.01      | sK6 != X1 ),
% 3.49/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_35]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_724,plain,
% 3.49/1.01      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 3.49/1.01      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
% 3.49/1.01      | ~ v1_relat_1(sK6) ),
% 3.49/1.01      inference(unflattening,[status(thm)],[c_723]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_2651,plain,
% 3.49/1.01      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.49/1.01      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
% 3.49/1.01      | v1_relat_1(sK6) != iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_724]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_5135,plain,
% 3.49/1.01      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.49/1.01      | r2_hidden(k1_funct_1(sK6,X0),sK5) = iProver_top
% 3.49/1.01      | v1_relat_1(sK6) != iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_2651,c_4374]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_12246,plain,
% 3.49/1.01      ( r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) = iProver_top
% 3.49/1.01      | r2_hidden(sK7(sK0(k2_relat_1(sK6),sK5)),k1_relat_1(sK6)) != iProver_top
% 3.49/1.01      | v1_relat_1(sK6) != iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_12243,c_5135]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_2913,plain,
% 3.49/1.01      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.49/1.01      | k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_23]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_2011,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_2894,plain,
% 3.49/1.01      ( k2_relset_1(sK4,sK5,sK6) != X0
% 3.49/1.01      | k2_relset_1(sK4,sK5,sK6) = sK5
% 3.49/1.01      | sK5 != X0 ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_2011]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_2994,plain,
% 3.49/1.01      ( k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6)
% 3.49/1.01      | k2_relset_1(sK4,sK5,sK6) = sK5
% 3.49/1.01      | sK5 != k2_relat_1(sK6) ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_2894]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_3076,plain,
% 3.49/1.01      ( ~ r2_hidden(sK0(X0,sK5),X0)
% 3.49/1.01      | ~ r2_hidden(sK0(X0,sK5),sK5)
% 3.49/1.01      | sK5 = X0 ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_6223,plain,
% 3.49/1.01      ( ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
% 3.49/1.01      | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5)
% 3.49/1.01      | sK5 = k2_relat_1(sK6) ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_3076]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_6227,plain,
% 3.49/1.01      ( sK5 = k2_relat_1(sK6)
% 3.49/1.01      | r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6)) != iProver_top
% 3.49/1.01      | r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) != iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_6223]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_11864,plain,
% 3.49/1.01      ( k2_relat_1(sK6) = sK5
% 3.49/1.01      | r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) = iProver_top
% 3.49/1.01      | iProver_top != iProver_top ),
% 3.49/1.01      inference(equality_factoring,[status(thm)],[c_11825]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_11866,plain,
% 3.49/1.01      ( k2_relat_1(sK6) = sK5
% 3.49/1.01      | r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) = iProver_top ),
% 3.49/1.01      inference(equality_resolution_simp,[status(thm)],[c_11864]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_12248,plain,
% 3.49/1.01      ( r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6)) = iProver_top
% 3.49/1.01      | r2_hidden(sK7(sK0(k2_relat_1(sK6),sK5)),k1_relat_1(sK6)) != iProver_top
% 3.49/1.01      | v1_relat_1(sK6) != iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_12243,c_2651]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_12364,plain,
% 3.49/1.01      ( r2_hidden(sK7(sK0(k2_relat_1(sK6),sK5)),k1_relat_1(sK6)) != iProver_top ),
% 3.49/1.01      inference(global_propositional_subsumption,
% 3.49/1.01                [status(thm)],
% 3.49/1.01                [c_12246,c_33,c_30,c_2913,c_2994,c_3852,c_6227,c_9726,
% 3.49/1.01                 c_11866,c_12248]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_12370,plain,
% 3.49/1.01      ( sK5 = k1_xboole_0
% 3.49/1.01      | r2_hidden(sK7(sK0(k2_relat_1(sK6),sK5)),sK4) != iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_3996,c_12364]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_32,negated_conjecture,
% 3.49/1.01      ( ~ r2_hidden(X0,sK5) | r2_hidden(sK7(X0),sK4) ),
% 3.49/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_3173,plain,
% 3.49/1.01      ( ~ r2_hidden(sK0(X0,sK5),sK5) | r2_hidden(sK7(sK0(X0,sK5)),sK4) ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_32]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_6224,plain,
% 3.49/1.01      ( ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5)
% 3.49/1.01      | r2_hidden(sK7(sK0(k2_relat_1(sK6),sK5)),sK4) ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_3173]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_6225,plain,
% 3.49/1.01      ( r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) != iProver_top
% 3.49/1.01      | r2_hidden(sK7(sK0(k2_relat_1(sK6),sK5)),sK4) = iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_6224]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_12624,plain,
% 3.49/1.01      ( sK5 = k1_xboole_0 ),
% 3.49/1.01      inference(global_propositional_subsumption,
% 3.49/1.01                [status(thm)],
% 3.49/1.01                [c_12370,c_3852,c_6225,c_11866]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_12943,plain,
% 3.49/1.01      ( k2_relat_1(sK6) = X0
% 3.49/1.01      | r2_hidden(sK0(k2_relat_1(sK6),X0),k2_relat_1(sK6)) != iProver_top
% 3.49/1.01      | r2_hidden(sK0(k2_relat_1(sK6),X0),k1_xboole_0) = iProver_top ),
% 3.49/1.01      inference(light_normalisation,[status(thm)],[c_11836,c_12624]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_12947,plain,
% 3.49/1.01      ( k2_relat_1(sK6) = X0
% 3.49/1.01      | r2_hidden(sK0(k2_relat_1(sK6),X0),k2_relat_1(sK6)) != iProver_top ),
% 3.49/1.01      inference(forward_subsumption_resolution,
% 3.49/1.01                [status(thm)],
% 3.49/1.01                [c_12943,c_3032]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_12957,plain,
% 3.49/1.01      ( k2_relat_1(sK6) = k1_xboole_0 ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_4582,c_12947]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_3082,plain,
% 3.49/1.01      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_2011]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_3795,plain,
% 3.49/1.01      ( k2_relat_1(sK6) != X0 | sK5 != X0 | sK5 = k2_relat_1(sK6) ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_3082]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_3796,plain,
% 3.49/1.01      ( k2_relat_1(sK6) != k1_xboole_0
% 3.49/1.01      | sK5 = k2_relat_1(sK6)
% 3.49/1.01      | sK5 != k1_xboole_0 ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_3795]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(contradiction,plain,
% 3.49/1.01      ( $false ),
% 3.49/1.01      inference(minisat,
% 3.49/1.01                [status(thm)],
% 3.49/1.01                [c_12957,c_12370,c_11866,c_6225,c_3852,c_3796,c_2994,
% 3.49/1.01                 c_2913,c_30,c_33]) ).
% 3.49/1.01  
% 3.49/1.01  
% 3.49/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.49/1.01  
% 3.49/1.01  ------                               Statistics
% 3.49/1.01  
% 3.49/1.01  ------ General
% 3.49/1.01  
% 3.49/1.01  abstr_ref_over_cycles:                  0
% 3.49/1.01  abstr_ref_under_cycles:                 0
% 3.49/1.01  gc_basic_clause_elim:                   0
% 3.49/1.01  forced_gc_time:                         0
% 3.49/1.01  parsing_time:                           0.017
% 3.49/1.01  unif_index_cands_time:                  0.
% 3.49/1.01  unif_index_add_time:                    0.
% 3.49/1.01  orderings_time:                         0.
% 3.49/1.01  out_proof_time:                         0.01
% 3.49/1.01  total_time:                             0.362
% 3.49/1.01  num_of_symbols:                         55
% 3.49/1.01  num_of_terms:                           8381
% 3.49/1.01  
% 3.49/1.01  ------ Preprocessing
% 3.49/1.01  
% 3.49/1.01  num_of_splits:                          0
% 3.49/1.01  num_of_split_atoms:                     0
% 3.49/1.01  num_of_reused_defs:                     0
% 3.49/1.01  num_eq_ax_congr_red:                    33
% 3.49/1.01  num_of_sem_filtered_clauses:            1
% 3.49/1.01  num_of_subtypes:                        0
% 3.49/1.01  monotx_restored_types:                  0
% 3.49/1.01  sat_num_of_epr_types:                   0
% 3.49/1.01  sat_num_of_non_cyclic_types:            0
% 3.49/1.01  sat_guarded_non_collapsed_types:        0
% 3.49/1.01  num_pure_diseq_elim:                    0
% 3.49/1.01  simp_replaced_by:                       0
% 3.49/1.01  res_preprocessed:                       154
% 3.49/1.01  prep_upred:                             0
% 3.49/1.01  prep_unflattend:                        103
% 3.49/1.01  smt_new_axioms:                         0
% 3.49/1.01  pred_elim_cands:                        4
% 3.49/1.01  pred_elim:                              3
% 3.49/1.01  pred_elim_cl:                           7
% 3.49/1.01  pred_elim_cycles:                       8
% 3.49/1.01  merged_defs:                            8
% 3.49/1.01  merged_defs_ncl:                        0
% 3.49/1.01  bin_hyper_res:                          10
% 3.49/1.01  prep_cycles:                            4
% 3.49/1.01  pred_elim_time:                         0.036
% 3.49/1.01  splitting_time:                         0.
% 3.49/1.01  sem_filter_time:                        0.
% 3.49/1.01  monotx_time:                            0.001
% 3.49/1.01  subtype_inf_time:                       0.
% 3.49/1.01  
% 3.49/1.01  ------ Problem properties
% 3.49/1.01  
% 3.49/1.01  clauses:                                28
% 3.49/1.01  conjectures:                            4
% 3.49/1.01  epr:                                    4
% 3.49/1.01  horn:                                   22
% 3.49/1.01  ground:                                 5
% 3.49/1.01  unary:                                  4
% 3.49/1.01  binary:                                 8
% 3.49/1.01  lits:                                   74
% 3.49/1.01  lits_eq:                                21
% 3.49/1.01  fd_pure:                                0
% 3.49/1.01  fd_pseudo:                              0
% 3.49/1.01  fd_cond:                                3
% 3.49/1.01  fd_pseudo_cond:                         3
% 3.49/1.01  ac_symbols:                             0
% 3.49/1.01  
% 3.49/1.01  ------ Propositional Solver
% 3.49/1.01  
% 3.49/1.01  prop_solver_calls:                      29
% 3.49/1.01  prop_fast_solver_calls:                 1385
% 3.49/1.01  smt_solver_calls:                       0
% 3.49/1.01  smt_fast_solver_calls:                  0
% 3.49/1.01  prop_num_of_clauses:                    3899
% 3.49/1.01  prop_preprocess_simplified:             9360
% 3.49/1.01  prop_fo_subsumed:                       31
% 3.49/1.01  prop_solver_time:                       0.
% 3.49/1.01  smt_solver_time:                        0.
% 3.49/1.01  smt_fast_solver_time:                   0.
% 3.49/1.01  prop_fast_solver_time:                  0.
% 3.49/1.01  prop_unsat_core_time:                   0.
% 3.49/1.01  
% 3.49/1.01  ------ QBF
% 3.49/1.01  
% 3.49/1.01  qbf_q_res:                              0
% 3.49/1.01  qbf_num_tautologies:                    0
% 3.49/1.01  qbf_prep_cycles:                        0
% 3.49/1.01  
% 3.49/1.01  ------ BMC1
% 3.49/1.01  
% 3.49/1.01  bmc1_current_bound:                     -1
% 3.49/1.01  bmc1_last_solved_bound:                 -1
% 3.49/1.01  bmc1_unsat_core_size:                   -1
% 3.49/1.01  bmc1_unsat_core_parents_size:           -1
% 3.49/1.01  bmc1_merge_next_fun:                    0
% 3.49/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.49/1.01  
% 3.49/1.01  ------ Instantiation
% 3.49/1.01  
% 3.49/1.01  inst_num_of_clauses:                    900
% 3.49/1.01  inst_num_in_passive:                    458
% 3.49/1.01  inst_num_in_active:                     324
% 3.49/1.01  inst_num_in_unprocessed:                118
% 3.49/1.01  inst_num_of_loops:                      510
% 3.49/1.01  inst_num_of_learning_restarts:          0
% 3.49/1.01  inst_num_moves_active_passive:          183
% 3.49/1.01  inst_lit_activity:                      0
% 3.49/1.01  inst_lit_activity_moves:                0
% 3.49/1.01  inst_num_tautologies:                   0
% 3.49/1.01  inst_num_prop_implied:                  0
% 3.49/1.01  inst_num_existing_simplified:           0
% 3.49/1.01  inst_num_eq_res_simplified:             0
% 3.49/1.01  inst_num_child_elim:                    0
% 3.49/1.01  inst_num_of_dismatching_blockings:      288
% 3.49/1.01  inst_num_of_non_proper_insts:           947
% 3.49/1.01  inst_num_of_duplicates:                 0
% 3.49/1.01  inst_inst_num_from_inst_to_res:         0
% 3.49/1.01  inst_dismatching_checking_time:         0.
% 3.49/1.01  
% 3.49/1.01  ------ Resolution
% 3.49/1.01  
% 3.49/1.01  res_num_of_clauses:                     0
% 3.49/1.01  res_num_in_passive:                     0
% 3.49/1.01  res_num_in_active:                      0
% 3.49/1.01  res_num_of_loops:                       158
% 3.49/1.01  res_forward_subset_subsumed:            39
% 3.49/1.01  res_backward_subset_subsumed:           0
% 3.49/1.01  res_forward_subsumed:                   0
% 3.49/1.01  res_backward_subsumed:                  1
% 3.49/1.01  res_forward_subsumption_resolution:     0
% 3.49/1.01  res_backward_subsumption_resolution:    1
% 3.49/1.01  res_clause_to_clause_subsumption:       981
% 3.49/1.01  res_orphan_elimination:                 0
% 3.49/1.01  res_tautology_del:                      71
% 3.49/1.01  res_num_eq_res_simplified:              0
% 3.49/1.01  res_num_sel_changes:                    0
% 3.49/1.01  res_moves_from_active_to_pass:          0
% 3.49/1.01  
% 3.49/1.01  ------ Superposition
% 3.49/1.01  
% 3.49/1.01  sup_time_total:                         0.
% 3.49/1.01  sup_time_generating:                    0.
% 3.49/1.01  sup_time_sim_full:                      0.
% 3.49/1.01  sup_time_sim_immed:                     0.
% 3.49/1.01  
% 3.49/1.01  sup_num_of_clauses:                     462
% 3.49/1.01  sup_num_in_active:                      69
% 3.49/1.01  sup_num_in_passive:                     393
% 3.49/1.01  sup_num_of_loops:                       100
% 3.49/1.01  sup_fw_superposition:                   365
% 3.49/1.01  sup_bw_superposition:                   267
% 3.49/1.01  sup_immediate_simplified:               29
% 3.49/1.01  sup_given_eliminated:                   2
% 3.49/1.01  comparisons_done:                       0
% 3.49/1.01  comparisons_avoided:                    17
% 3.49/1.01  
% 3.49/1.01  ------ Simplifications
% 3.49/1.01  
% 3.49/1.01  
% 3.49/1.01  sim_fw_subset_subsumed:                 16
% 3.49/1.01  sim_bw_subset_subsumed:                 17
% 3.49/1.01  sim_fw_subsumed:                        6
% 3.49/1.01  sim_bw_subsumed:                        0
% 3.49/1.01  sim_fw_subsumption_res:                 3
% 3.49/1.01  sim_bw_subsumption_res:                 0
% 3.49/1.01  sim_tautology_del:                      3
% 3.49/1.01  sim_eq_tautology_del:                   132
% 3.49/1.01  sim_eq_res_simp:                        3
% 3.49/1.01  sim_fw_demodulated:                     2
% 3.49/1.01  sim_bw_demodulated:                     31
% 3.49/1.01  sim_light_normalised:                   7
% 3.49/1.01  sim_joinable_taut:                      0
% 3.49/1.01  sim_joinable_simp:                      0
% 3.49/1.01  sim_ac_normalised:                      0
% 3.49/1.01  sim_smt_subsumption:                    0
% 3.49/1.01  
%------------------------------------------------------------------------------
