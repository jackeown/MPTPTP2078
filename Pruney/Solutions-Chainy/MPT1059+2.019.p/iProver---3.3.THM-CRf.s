%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:28 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 447 expanded)
%              Number of clauses        :   63 ( 127 expanded)
%              Number of leaves         :   18 ( 144 expanded)
%              Depth                    :   19
%              Number of atoms          :  393 (2394 expanded)
%              Number of equality atoms :  129 ( 535 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => k7_partfun1(X1,X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,X0)
                   => k7_partfun1(X1,X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3)
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3)
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3)
          & m1_subset_1(X3,X0) )
     => ( k7_partfun1(X1,X2,sK4) != k3_funct_2(X0,X1,X2,sK4)
        & m1_subset_1(sK4,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3)
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( k7_partfun1(X1,sK3,X3) != k3_funct_2(X0,X1,sK3,X3)
            & m1_subset_1(X3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK3,X0,X1)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3)
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k7_partfun1(sK2,X2,X3) != k3_funct_2(X0,sK2,X2,X3)
                & m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
            & v1_funct_2(X2,X0,sK2)
            & v1_funct_1(X2) )
        & ~ v1_xboole_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3)
                    & m1_subset_1(X3,X0) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_partfun1(X1,X2,X3) != k3_funct_2(sK1,X1,X2,X3)
                  & m1_subset_1(X3,sK1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
              & v1_funct_2(X2,sK1,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( k7_partfun1(sK2,sK3,sK4) != k3_funct_2(sK1,sK2,sK3,sK4)
    & m1_subset_1(sK4,sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f34,f42,f41,f40,f39])).

fof(f68,plain,(
    m1_subset_1(sK4,sK1) ),
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

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f67,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f2,f35])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
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
    inference(nnf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,(
    k7_partfun1(sK2,sK3,sK4) != k3_funct_2(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1579,plain,
    ( m1_subset_1(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_799,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X1
    | sK3 != X0
    | sK2 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_800,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_799])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_802,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_800,c_21])).

cnf(c_1578,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1580,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2482,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1578,c_1580])).

cnf(c_2605,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_802,c_2482])).

cnf(c_25,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_9,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_17,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_362,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k7_partfun1(X3,X1,X0) = k1_funct_1(X1,X0) ),
    inference(resolution,[status(thm)],[c_9,c_17])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_376,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | k7_partfun1(X3,X1,X0) = k1_funct_1(X1,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_362,c_8])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_410,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k7_partfun1(X3,X1,X0) = k1_funct_1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_376,c_23])).

cnf(c_411,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_partfun1(X2,sK3,X0) = k1_funct_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_464,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | v1_xboole_0(X1)
    | X4 != X0
    | k7_partfun1(X3,sK3,X4) = k1_funct_1(sK3,X4)
    | k1_relat_1(sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_411])).

cnf(c_465,plain,
    ( ~ m1_subset_1(X0,k1_relat_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(k1_relat_1(sK3))
    | k7_partfun1(X2,sK3,X0) = k1_funct_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_603,plain,
    ( ~ m1_subset_1(X0,k1_relat_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_partfun1(X2,sK3,X0) = k1_funct_1(sK3,X0)
    | k1_relat_1(sK3) != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_465])).

cnf(c_1572,plain,
    ( k7_partfun1(X0,sK3,X1) = k1_funct_1(sK3,X1)
    | k1_relat_1(sK3) != sK1
    | m1_subset_1(X1,k1_relat_1(sK3)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_603])).

cnf(c_2677,plain,
    ( k7_partfun1(X0,sK3,X1) = k1_funct_1(sK3,X1)
    | sK2 = k1_xboole_0
    | m1_subset_1(X1,k1_relat_1(sK3)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2605,c_1572])).

cnf(c_604,plain,
    ( k7_partfun1(X0,sK3,X1) = k1_funct_1(sK3,X1)
    | k1_relat_1(sK3) != sK1
    | m1_subset_1(X1,k1_relat_1(sK3)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_603])).

cnf(c_1,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1830,plain,
    ( m1_subset_1(sK0(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_435,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ r1_tarski(X1,X0)
    | v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_3,c_7])).

cnf(c_24,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_511,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ r1_tarski(X1,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_435,c_24])).

cnf(c_512,plain,
    ( ~ m1_subset_1(X0,sK2)
    | ~ r1_tarski(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_511])).

cnf(c_1832,plain,
    ( ~ m1_subset_1(sK0(sK2),sK2)
    | ~ r1_tarski(sK2,sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_512])).

cnf(c_954,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_1981,plain,
    ( ~ r1_tarski(X0,sK0(sK2))
    | r1_tarski(sK2,sK0(sK2))
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_954])).

cnf(c_1983,plain,
    ( r1_tarski(sK2,sK0(sK2))
    | ~ r1_tarski(k1_xboole_0,sK0(sK2))
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1981])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2344,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0(sK2)))
    | r1_tarski(X0,sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2346,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(sK2)))
    | r1_tarski(k1_xboole_0,sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2344])).

cnf(c_2,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2879,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(sK2))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3457,plain,
    ( k7_partfun1(X0,sK3,X1) = k1_funct_1(sK3,X1)
    | m1_subset_1(X1,k1_relat_1(sK3)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2677,c_604,c_1830,c_1832,c_1983,c_2346,c_2605,c_2879])).

cnf(c_3467,plain,
    ( k7_partfun1(sK2,sK3,X0) = k1_funct_1(sK3,X0)
    | m1_subset_1(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1578,c_3457])).

cnf(c_3488,plain,
    ( k7_partfun1(sK2,sK3,X0) = k1_funct_1(sK3,X0)
    | sK2 = k1_xboole_0
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2605,c_3467])).

cnf(c_4158,plain,
    ( k7_partfun1(sK2,sK3,X0) = k1_funct_1(sK3,X0)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3488,c_1830,c_1832,c_1983,c_2346,c_2879])).

cnf(c_4167,plain,
    ( k7_partfun1(sK2,sK3,sK4) = k1_funct_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1579,c_4158])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_389,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_23])).

cnf(c_390,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | ~ m1_subset_1(X2,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X0)
    | k3_funct_2(X0,X1,sK3,X2) = k1_funct_1(sK3,X2) ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_568,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | ~ m1_subset_1(X2,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k3_funct_2(X0,X1,sK3,X2) = k1_funct_1(sK3,X2)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_390,c_25])).

cnf(c_569,plain,
    ( ~ v1_funct_2(sK3,sK1,X0)
    | ~ m1_subset_1(X1,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
    | k3_funct_2(sK1,X0,sK3,X1) = k1_funct_1(sK3,X1) ),
    inference(unflattening,[status(thm)],[c_568])).

cnf(c_870,plain,
    ( ~ m1_subset_1(X0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | k3_funct_2(sK1,X1,sK3,X0) = k1_funct_1(sK3,X0)
    | sK1 != sK1
    | sK3 != sK3
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_569])).

cnf(c_871,plain,
    ( ~ m1_subset_1(X0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_870])).

cnf(c_875,plain,
    ( ~ m1_subset_1(X0,sK1)
    | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_871,c_21])).

cnf(c_1559,plain,
    ( k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_875])).

cnf(c_1922,plain,
    ( k3_funct_2(sK1,sK2,sK3,sK4) = k1_funct_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1579,c_1559])).

cnf(c_19,negated_conjecture,
    ( k7_partfun1(sK2,sK3,sK4) != k3_funct_2(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2186,plain,
    ( k7_partfun1(sK2,sK3,sK4) != k1_funct_1(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_1922,c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4167,c_2186])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:06:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.55/1.07  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.07  
% 2.55/1.07  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.55/1.07  
% 2.55/1.07  ------  iProver source info
% 2.55/1.07  
% 2.55/1.07  git: date: 2020-06-30 10:37:57 +0100
% 2.55/1.07  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.55/1.07  git: non_committed_changes: false
% 2.55/1.07  git: last_make_outside_of_git: false
% 2.55/1.07  
% 2.55/1.07  ------ 
% 2.55/1.07  
% 2.55/1.07  ------ Input Options
% 2.55/1.07  
% 2.55/1.07  --out_options                           all
% 2.55/1.07  --tptp_safe_out                         true
% 2.55/1.07  --problem_path                          ""
% 2.55/1.07  --include_path                          ""
% 2.55/1.07  --clausifier                            res/vclausify_rel
% 2.55/1.07  --clausifier_options                    --mode clausify
% 2.55/1.07  --stdin                                 false
% 2.55/1.07  --stats_out                             all
% 2.55/1.07  
% 2.55/1.07  ------ General Options
% 2.55/1.07  
% 2.55/1.07  --fof                                   false
% 2.55/1.07  --time_out_real                         305.
% 2.55/1.07  --time_out_virtual                      -1.
% 2.55/1.07  --symbol_type_check                     false
% 2.55/1.07  --clausify_out                          false
% 2.55/1.07  --sig_cnt_out                           false
% 2.55/1.07  --trig_cnt_out                          false
% 2.55/1.07  --trig_cnt_out_tolerance                1.
% 2.55/1.07  --trig_cnt_out_sk_spl                   false
% 2.55/1.07  --abstr_cl_out                          false
% 2.55/1.07  
% 2.55/1.07  ------ Global Options
% 2.55/1.07  
% 2.55/1.07  --schedule                              default
% 2.55/1.07  --add_important_lit                     false
% 2.55/1.07  --prop_solver_per_cl                    1000
% 2.55/1.07  --min_unsat_core                        false
% 2.55/1.07  --soft_assumptions                      false
% 2.55/1.07  --soft_lemma_size                       3
% 2.55/1.07  --prop_impl_unit_size                   0
% 2.55/1.07  --prop_impl_unit                        []
% 2.55/1.07  --share_sel_clauses                     true
% 2.55/1.07  --reset_solvers                         false
% 2.55/1.07  --bc_imp_inh                            [conj_cone]
% 2.55/1.07  --conj_cone_tolerance                   3.
% 2.55/1.07  --extra_neg_conj                        none
% 2.55/1.07  --large_theory_mode                     true
% 2.55/1.07  --prolific_symb_bound                   200
% 2.55/1.07  --lt_threshold                          2000
% 2.55/1.07  --clause_weak_htbl                      true
% 2.55/1.07  --gc_record_bc_elim                     false
% 2.55/1.07  
% 2.55/1.07  ------ Preprocessing Options
% 2.55/1.07  
% 2.55/1.07  --preprocessing_flag                    true
% 2.55/1.07  --time_out_prep_mult                    0.1
% 2.55/1.07  --splitting_mode                        input
% 2.55/1.07  --splitting_grd                         true
% 2.55/1.07  --splitting_cvd                         false
% 2.55/1.07  --splitting_cvd_svl                     false
% 2.55/1.07  --splitting_nvd                         32
% 2.55/1.07  --sub_typing                            true
% 2.55/1.07  --prep_gs_sim                           true
% 2.55/1.07  --prep_unflatten                        true
% 2.55/1.07  --prep_res_sim                          true
% 2.55/1.07  --prep_upred                            true
% 2.55/1.07  --prep_sem_filter                       exhaustive
% 2.55/1.07  --prep_sem_filter_out                   false
% 2.55/1.07  --pred_elim                             true
% 2.55/1.07  --res_sim_input                         true
% 2.55/1.07  --eq_ax_congr_red                       true
% 2.55/1.07  --pure_diseq_elim                       true
% 2.55/1.07  --brand_transform                       false
% 2.55/1.07  --non_eq_to_eq                          false
% 2.55/1.07  --prep_def_merge                        true
% 2.55/1.07  --prep_def_merge_prop_impl              false
% 2.55/1.07  --prep_def_merge_mbd                    true
% 2.55/1.07  --prep_def_merge_tr_red                 false
% 2.55/1.07  --prep_def_merge_tr_cl                  false
% 2.55/1.07  --smt_preprocessing                     true
% 2.55/1.07  --smt_ac_axioms                         fast
% 2.55/1.07  --preprocessed_out                      false
% 2.55/1.07  --preprocessed_stats                    false
% 2.55/1.07  
% 2.55/1.07  ------ Abstraction refinement Options
% 2.55/1.07  
% 2.55/1.07  --abstr_ref                             []
% 2.55/1.07  --abstr_ref_prep                        false
% 2.55/1.07  --abstr_ref_until_sat                   false
% 2.55/1.07  --abstr_ref_sig_restrict                funpre
% 2.55/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 2.55/1.07  --abstr_ref_under                       []
% 2.55/1.07  
% 2.55/1.07  ------ SAT Options
% 2.55/1.07  
% 2.55/1.07  --sat_mode                              false
% 2.55/1.07  --sat_fm_restart_options                ""
% 2.55/1.07  --sat_gr_def                            false
% 2.55/1.07  --sat_epr_types                         true
% 2.55/1.07  --sat_non_cyclic_types                  false
% 2.55/1.07  --sat_finite_models                     false
% 2.55/1.07  --sat_fm_lemmas                         false
% 2.55/1.07  --sat_fm_prep                           false
% 2.55/1.07  --sat_fm_uc_incr                        true
% 2.55/1.07  --sat_out_model                         small
% 2.55/1.07  --sat_out_clauses                       false
% 2.55/1.07  
% 2.55/1.07  ------ QBF Options
% 2.55/1.07  
% 2.55/1.07  --qbf_mode                              false
% 2.55/1.07  --qbf_elim_univ                         false
% 2.55/1.07  --qbf_dom_inst                          none
% 2.55/1.07  --qbf_dom_pre_inst                      false
% 2.55/1.07  --qbf_sk_in                             false
% 2.55/1.07  --qbf_pred_elim                         true
% 2.55/1.07  --qbf_split                             512
% 2.55/1.07  
% 2.55/1.07  ------ BMC1 Options
% 2.55/1.07  
% 2.55/1.07  --bmc1_incremental                      false
% 2.55/1.07  --bmc1_axioms                           reachable_all
% 2.55/1.07  --bmc1_min_bound                        0
% 2.55/1.07  --bmc1_max_bound                        -1
% 2.55/1.07  --bmc1_max_bound_default                -1
% 2.55/1.07  --bmc1_symbol_reachability              true
% 2.55/1.07  --bmc1_property_lemmas                  false
% 2.55/1.07  --bmc1_k_induction                      false
% 2.55/1.07  --bmc1_non_equiv_states                 false
% 2.55/1.07  --bmc1_deadlock                         false
% 2.55/1.07  --bmc1_ucm                              false
% 2.55/1.07  --bmc1_add_unsat_core                   none
% 2.55/1.07  --bmc1_unsat_core_children              false
% 2.55/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 2.55/1.07  --bmc1_out_stat                         full
% 2.55/1.07  --bmc1_ground_init                      false
% 2.55/1.07  --bmc1_pre_inst_next_state              false
% 2.55/1.07  --bmc1_pre_inst_state                   false
% 2.55/1.07  --bmc1_pre_inst_reach_state             false
% 2.55/1.07  --bmc1_out_unsat_core                   false
% 2.55/1.07  --bmc1_aig_witness_out                  false
% 2.55/1.07  --bmc1_verbose                          false
% 2.55/1.07  --bmc1_dump_clauses_tptp                false
% 2.55/1.07  --bmc1_dump_unsat_core_tptp             false
% 2.55/1.07  --bmc1_dump_file                        -
% 2.55/1.07  --bmc1_ucm_expand_uc_limit              128
% 2.55/1.07  --bmc1_ucm_n_expand_iterations          6
% 2.55/1.07  --bmc1_ucm_extend_mode                  1
% 2.55/1.07  --bmc1_ucm_init_mode                    2
% 2.55/1.07  --bmc1_ucm_cone_mode                    none
% 2.55/1.07  --bmc1_ucm_reduced_relation_type        0
% 2.55/1.07  --bmc1_ucm_relax_model                  4
% 2.55/1.07  --bmc1_ucm_full_tr_after_sat            true
% 2.55/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 2.55/1.07  --bmc1_ucm_layered_model                none
% 2.55/1.07  --bmc1_ucm_max_lemma_size               10
% 2.55/1.07  
% 2.55/1.07  ------ AIG Options
% 2.55/1.07  
% 2.55/1.07  --aig_mode                              false
% 2.55/1.07  
% 2.55/1.07  ------ Instantiation Options
% 2.55/1.07  
% 2.55/1.07  --instantiation_flag                    true
% 2.55/1.07  --inst_sos_flag                         false
% 2.55/1.07  --inst_sos_phase                        true
% 2.55/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.55/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.55/1.07  --inst_lit_sel_side                     num_symb
% 2.55/1.07  --inst_solver_per_active                1400
% 2.55/1.07  --inst_solver_calls_frac                1.
% 2.55/1.07  --inst_passive_queue_type               priority_queues
% 2.55/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.55/1.07  --inst_passive_queues_freq              [25;2]
% 2.55/1.07  --inst_dismatching                      true
% 2.55/1.07  --inst_eager_unprocessed_to_passive     true
% 2.55/1.07  --inst_prop_sim_given                   true
% 2.55/1.07  --inst_prop_sim_new                     false
% 2.55/1.07  --inst_subs_new                         false
% 2.55/1.07  --inst_eq_res_simp                      false
% 2.55/1.07  --inst_subs_given                       false
% 2.55/1.07  --inst_orphan_elimination               true
% 2.55/1.07  --inst_learning_loop_flag               true
% 2.55/1.07  --inst_learning_start                   3000
% 2.55/1.07  --inst_learning_factor                  2
% 2.55/1.07  --inst_start_prop_sim_after_learn       3
% 2.55/1.07  --inst_sel_renew                        solver
% 2.55/1.07  --inst_lit_activity_flag                true
% 2.55/1.07  --inst_restr_to_given                   false
% 2.55/1.07  --inst_activity_threshold               500
% 2.55/1.07  --inst_out_proof                        true
% 2.55/1.07  
% 2.55/1.07  ------ Resolution Options
% 2.55/1.07  
% 2.55/1.07  --resolution_flag                       true
% 2.55/1.07  --res_lit_sel                           adaptive
% 2.55/1.07  --res_lit_sel_side                      none
% 2.55/1.07  --res_ordering                          kbo
% 2.55/1.07  --res_to_prop_solver                    active
% 2.55/1.07  --res_prop_simpl_new                    false
% 2.55/1.07  --res_prop_simpl_given                  true
% 2.55/1.07  --res_passive_queue_type                priority_queues
% 2.55/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.55/1.07  --res_passive_queues_freq               [15;5]
% 2.55/1.07  --res_forward_subs                      full
% 2.55/1.07  --res_backward_subs                     full
% 2.55/1.07  --res_forward_subs_resolution           true
% 2.55/1.07  --res_backward_subs_resolution          true
% 2.55/1.07  --res_orphan_elimination                true
% 2.55/1.07  --res_time_limit                        2.
% 2.55/1.07  --res_out_proof                         true
% 2.55/1.07  
% 2.55/1.07  ------ Superposition Options
% 2.55/1.07  
% 2.55/1.07  --superposition_flag                    true
% 2.55/1.07  --sup_passive_queue_type                priority_queues
% 2.55/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.55/1.07  --sup_passive_queues_freq               [8;1;4]
% 2.55/1.07  --demod_completeness_check              fast
% 2.55/1.07  --demod_use_ground                      true
% 2.55/1.07  --sup_to_prop_solver                    passive
% 2.55/1.07  --sup_prop_simpl_new                    true
% 2.55/1.07  --sup_prop_simpl_given                  true
% 2.55/1.07  --sup_fun_splitting                     false
% 2.55/1.07  --sup_smt_interval                      50000
% 2.55/1.07  
% 2.55/1.07  ------ Superposition Simplification Setup
% 2.55/1.07  
% 2.55/1.07  --sup_indices_passive                   []
% 2.55/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 2.55/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/1.07  --sup_full_bw                           [BwDemod]
% 2.55/1.07  --sup_immed_triv                        [TrivRules]
% 2.55/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.55/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/1.07  --sup_immed_bw_main                     []
% 2.55/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.55/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 2.55/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.55/1.07  
% 2.55/1.07  ------ Combination Options
% 2.55/1.07  
% 2.55/1.07  --comb_res_mult                         3
% 2.55/1.07  --comb_sup_mult                         2
% 2.55/1.07  --comb_inst_mult                        10
% 2.55/1.07  
% 2.55/1.07  ------ Debug Options
% 2.55/1.07  
% 2.55/1.07  --dbg_backtrace                         false
% 2.55/1.07  --dbg_dump_prop_clauses                 false
% 2.55/1.07  --dbg_dump_prop_clauses_file            -
% 2.55/1.07  --dbg_out_stat                          false
% 2.55/1.07  ------ Parsing...
% 2.55/1.07  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.55/1.07  
% 2.55/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e 
% 2.55/1.07  
% 2.55/1.07  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.55/1.07  
% 2.55/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.55/1.07  ------ Proving...
% 2.55/1.07  ------ Problem Properties 
% 2.55/1.07  
% 2.55/1.07  
% 2.55/1.07  clauses                                 29
% 2.55/1.07  conjectures                             3
% 2.55/1.07  EPR                                     4
% 2.55/1.07  Horn                                    23
% 2.55/1.07  unary                                   5
% 2.55/1.07  binary                                  7
% 2.55/1.07  lits                                    85
% 2.55/1.07  lits eq                                 34
% 2.55/1.07  fd_pure                                 0
% 2.55/1.07  fd_pseudo                               0
% 2.55/1.07  fd_cond                                 2
% 2.55/1.07  fd_pseudo_cond                          0
% 2.55/1.07  AC symbols                              0
% 2.55/1.07  
% 2.55/1.07  ------ Schedule dynamic 5 is on 
% 2.55/1.07  
% 2.55/1.07  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.55/1.07  
% 2.55/1.07  
% 2.55/1.07  ------ 
% 2.55/1.07  Current options:
% 2.55/1.07  ------ 
% 2.55/1.07  
% 2.55/1.07  ------ Input Options
% 2.55/1.07  
% 2.55/1.07  --out_options                           all
% 2.55/1.07  --tptp_safe_out                         true
% 2.55/1.07  --problem_path                          ""
% 2.55/1.07  --include_path                          ""
% 2.55/1.07  --clausifier                            res/vclausify_rel
% 2.55/1.07  --clausifier_options                    --mode clausify
% 2.55/1.07  --stdin                                 false
% 2.55/1.07  --stats_out                             all
% 2.55/1.07  
% 2.55/1.07  ------ General Options
% 2.55/1.07  
% 2.55/1.07  --fof                                   false
% 2.55/1.07  --time_out_real                         305.
% 2.55/1.07  --time_out_virtual                      -1.
% 2.55/1.07  --symbol_type_check                     false
% 2.55/1.07  --clausify_out                          false
% 2.55/1.07  --sig_cnt_out                           false
% 2.55/1.07  --trig_cnt_out                          false
% 2.55/1.07  --trig_cnt_out_tolerance                1.
% 2.55/1.07  --trig_cnt_out_sk_spl                   false
% 2.55/1.07  --abstr_cl_out                          false
% 2.55/1.07  
% 2.55/1.07  ------ Global Options
% 2.55/1.07  
% 2.55/1.07  --schedule                              default
% 2.55/1.07  --add_important_lit                     false
% 2.55/1.07  --prop_solver_per_cl                    1000
% 2.55/1.07  --min_unsat_core                        false
% 2.55/1.07  --soft_assumptions                      false
% 2.55/1.07  --soft_lemma_size                       3
% 2.55/1.07  --prop_impl_unit_size                   0
% 2.55/1.07  --prop_impl_unit                        []
% 2.55/1.07  --share_sel_clauses                     true
% 2.55/1.07  --reset_solvers                         false
% 2.55/1.07  --bc_imp_inh                            [conj_cone]
% 2.55/1.07  --conj_cone_tolerance                   3.
% 2.55/1.07  --extra_neg_conj                        none
% 2.55/1.07  --large_theory_mode                     true
% 2.55/1.07  --prolific_symb_bound                   200
% 2.55/1.07  --lt_threshold                          2000
% 2.55/1.07  --clause_weak_htbl                      true
% 2.55/1.07  --gc_record_bc_elim                     false
% 2.55/1.07  
% 2.55/1.07  ------ Preprocessing Options
% 2.55/1.07  
% 2.55/1.07  --preprocessing_flag                    true
% 2.55/1.07  --time_out_prep_mult                    0.1
% 2.55/1.07  --splitting_mode                        input
% 2.55/1.07  --splitting_grd                         true
% 2.55/1.07  --splitting_cvd                         false
% 2.55/1.07  --splitting_cvd_svl                     false
% 2.55/1.07  --splitting_nvd                         32
% 2.55/1.07  --sub_typing                            true
% 2.55/1.07  --prep_gs_sim                           true
% 2.55/1.07  --prep_unflatten                        true
% 2.55/1.07  --prep_res_sim                          true
% 2.55/1.07  --prep_upred                            true
% 2.55/1.07  --prep_sem_filter                       exhaustive
% 2.55/1.07  --prep_sem_filter_out                   false
% 2.55/1.07  --pred_elim                             true
% 2.55/1.07  --res_sim_input                         true
% 2.55/1.07  --eq_ax_congr_red                       true
% 2.55/1.07  --pure_diseq_elim                       true
% 2.55/1.07  --brand_transform                       false
% 2.55/1.07  --non_eq_to_eq                          false
% 2.55/1.07  --prep_def_merge                        true
% 2.55/1.07  --prep_def_merge_prop_impl              false
% 2.55/1.07  --prep_def_merge_mbd                    true
% 2.55/1.07  --prep_def_merge_tr_red                 false
% 2.55/1.07  --prep_def_merge_tr_cl                  false
% 2.55/1.07  --smt_preprocessing                     true
% 2.55/1.07  --smt_ac_axioms                         fast
% 2.55/1.07  --preprocessed_out                      false
% 2.55/1.07  --preprocessed_stats                    false
% 2.55/1.07  
% 2.55/1.07  ------ Abstraction refinement Options
% 2.55/1.07  
% 2.55/1.07  --abstr_ref                             []
% 2.55/1.07  --abstr_ref_prep                        false
% 2.55/1.07  --abstr_ref_until_sat                   false
% 2.55/1.07  --abstr_ref_sig_restrict                funpre
% 2.55/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 2.55/1.07  --abstr_ref_under                       []
% 2.55/1.07  
% 2.55/1.07  ------ SAT Options
% 2.55/1.07  
% 2.55/1.07  --sat_mode                              false
% 2.55/1.07  --sat_fm_restart_options                ""
% 2.55/1.07  --sat_gr_def                            false
% 2.55/1.07  --sat_epr_types                         true
% 2.55/1.07  --sat_non_cyclic_types                  false
% 2.55/1.07  --sat_finite_models                     false
% 2.55/1.07  --sat_fm_lemmas                         false
% 2.55/1.07  --sat_fm_prep                           false
% 2.55/1.07  --sat_fm_uc_incr                        true
% 2.55/1.07  --sat_out_model                         small
% 2.55/1.07  --sat_out_clauses                       false
% 2.55/1.07  
% 2.55/1.07  ------ QBF Options
% 2.55/1.07  
% 2.55/1.07  --qbf_mode                              false
% 2.55/1.07  --qbf_elim_univ                         false
% 2.55/1.07  --qbf_dom_inst                          none
% 2.55/1.07  --qbf_dom_pre_inst                      false
% 2.55/1.07  --qbf_sk_in                             false
% 2.55/1.07  --qbf_pred_elim                         true
% 2.55/1.07  --qbf_split                             512
% 2.55/1.07  
% 2.55/1.07  ------ BMC1 Options
% 2.55/1.07  
% 2.55/1.07  --bmc1_incremental                      false
% 2.55/1.07  --bmc1_axioms                           reachable_all
% 2.55/1.07  --bmc1_min_bound                        0
% 2.55/1.07  --bmc1_max_bound                        -1
% 2.55/1.07  --bmc1_max_bound_default                -1
% 2.55/1.07  --bmc1_symbol_reachability              true
% 2.55/1.07  --bmc1_property_lemmas                  false
% 2.55/1.07  --bmc1_k_induction                      false
% 2.55/1.07  --bmc1_non_equiv_states                 false
% 2.55/1.07  --bmc1_deadlock                         false
% 2.55/1.07  --bmc1_ucm                              false
% 2.55/1.07  --bmc1_add_unsat_core                   none
% 2.55/1.07  --bmc1_unsat_core_children              false
% 2.55/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 2.55/1.07  --bmc1_out_stat                         full
% 2.55/1.07  --bmc1_ground_init                      false
% 2.55/1.07  --bmc1_pre_inst_next_state              false
% 2.55/1.07  --bmc1_pre_inst_state                   false
% 2.55/1.07  --bmc1_pre_inst_reach_state             false
% 2.55/1.07  --bmc1_out_unsat_core                   false
% 2.55/1.07  --bmc1_aig_witness_out                  false
% 2.55/1.07  --bmc1_verbose                          false
% 2.55/1.07  --bmc1_dump_clauses_tptp                false
% 2.55/1.07  --bmc1_dump_unsat_core_tptp             false
% 2.55/1.07  --bmc1_dump_file                        -
% 2.55/1.07  --bmc1_ucm_expand_uc_limit              128
% 2.55/1.07  --bmc1_ucm_n_expand_iterations          6
% 2.55/1.07  --bmc1_ucm_extend_mode                  1
% 2.55/1.07  --bmc1_ucm_init_mode                    2
% 2.55/1.07  --bmc1_ucm_cone_mode                    none
% 2.55/1.07  --bmc1_ucm_reduced_relation_type        0
% 2.55/1.07  --bmc1_ucm_relax_model                  4
% 2.55/1.07  --bmc1_ucm_full_tr_after_sat            true
% 2.55/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 2.55/1.07  --bmc1_ucm_layered_model                none
% 2.55/1.07  --bmc1_ucm_max_lemma_size               10
% 2.55/1.07  
% 2.55/1.07  ------ AIG Options
% 2.55/1.07  
% 2.55/1.07  --aig_mode                              false
% 2.55/1.07  
% 2.55/1.07  ------ Instantiation Options
% 2.55/1.07  
% 2.55/1.07  --instantiation_flag                    true
% 2.55/1.07  --inst_sos_flag                         false
% 2.55/1.07  --inst_sos_phase                        true
% 2.55/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.55/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.55/1.07  --inst_lit_sel_side                     none
% 2.55/1.07  --inst_solver_per_active                1400
% 2.55/1.07  --inst_solver_calls_frac                1.
% 2.55/1.07  --inst_passive_queue_type               priority_queues
% 2.55/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.55/1.07  --inst_passive_queues_freq              [25;2]
% 2.55/1.07  --inst_dismatching                      true
% 2.55/1.07  --inst_eager_unprocessed_to_passive     true
% 2.55/1.07  --inst_prop_sim_given                   true
% 2.55/1.07  --inst_prop_sim_new                     false
% 2.55/1.07  --inst_subs_new                         false
% 2.55/1.07  --inst_eq_res_simp                      false
% 2.55/1.07  --inst_subs_given                       false
% 2.55/1.07  --inst_orphan_elimination               true
% 2.55/1.07  --inst_learning_loop_flag               true
% 2.55/1.07  --inst_learning_start                   3000
% 2.55/1.07  --inst_learning_factor                  2
% 2.55/1.07  --inst_start_prop_sim_after_learn       3
% 2.55/1.07  --inst_sel_renew                        solver
% 2.55/1.07  --inst_lit_activity_flag                true
% 2.55/1.07  --inst_restr_to_given                   false
% 2.55/1.07  --inst_activity_threshold               500
% 2.55/1.07  --inst_out_proof                        true
% 2.55/1.07  
% 2.55/1.07  ------ Resolution Options
% 2.55/1.07  
% 2.55/1.07  --resolution_flag                       false
% 2.55/1.07  --res_lit_sel                           adaptive
% 2.55/1.07  --res_lit_sel_side                      none
% 2.55/1.07  --res_ordering                          kbo
% 2.55/1.07  --res_to_prop_solver                    active
% 2.55/1.07  --res_prop_simpl_new                    false
% 2.55/1.07  --res_prop_simpl_given                  true
% 2.55/1.07  --res_passive_queue_type                priority_queues
% 2.55/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.55/1.07  --res_passive_queues_freq               [15;5]
% 2.55/1.07  --res_forward_subs                      full
% 2.55/1.07  --res_backward_subs                     full
% 2.55/1.07  --res_forward_subs_resolution           true
% 2.55/1.07  --res_backward_subs_resolution          true
% 2.55/1.07  --res_orphan_elimination                true
% 2.55/1.07  --res_time_limit                        2.
% 2.55/1.07  --res_out_proof                         true
% 2.55/1.07  
% 2.55/1.07  ------ Superposition Options
% 2.55/1.07  
% 2.55/1.07  --superposition_flag                    true
% 2.55/1.07  --sup_passive_queue_type                priority_queues
% 2.55/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.55/1.07  --sup_passive_queues_freq               [8;1;4]
% 2.55/1.07  --demod_completeness_check              fast
% 2.55/1.07  --demod_use_ground                      true
% 2.55/1.07  --sup_to_prop_solver                    passive
% 2.55/1.07  --sup_prop_simpl_new                    true
% 2.55/1.07  --sup_prop_simpl_given                  true
% 2.55/1.07  --sup_fun_splitting                     false
% 2.55/1.07  --sup_smt_interval                      50000
% 2.55/1.07  
% 2.55/1.07  ------ Superposition Simplification Setup
% 2.55/1.07  
% 2.55/1.07  --sup_indices_passive                   []
% 2.55/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 2.55/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/1.07  --sup_full_bw                           [BwDemod]
% 2.55/1.07  --sup_immed_triv                        [TrivRules]
% 2.55/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.55/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/1.07  --sup_immed_bw_main                     []
% 2.55/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.55/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 2.55/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.55/1.07  
% 2.55/1.07  ------ Combination Options
% 2.55/1.07  
% 2.55/1.07  --comb_res_mult                         3
% 2.55/1.07  --comb_sup_mult                         2
% 2.55/1.07  --comb_inst_mult                        10
% 2.55/1.07  
% 2.55/1.07  ------ Debug Options
% 2.55/1.07  
% 2.55/1.07  --dbg_backtrace                         false
% 2.55/1.07  --dbg_dump_prop_clauses                 false
% 2.55/1.07  --dbg_dump_prop_clauses_file            -
% 2.55/1.07  --dbg_out_stat                          false
% 2.55/1.07  
% 2.55/1.07  
% 2.55/1.07  
% 2.55/1.07  
% 2.55/1.07  ------ Proving...
% 2.55/1.07  
% 2.55/1.07  
% 2.55/1.07  % SZS status Theorem for theBenchmark.p
% 2.55/1.07  
% 2.55/1.07  % SZS output start CNFRefutation for theBenchmark.p
% 2.55/1.07  
% 2.55/1.07  fof(f14,conjecture,(
% 2.55/1.07    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k7_partfun1(X1,X2,X3) = k3_funct_2(X0,X1,X2,X3)))))),
% 2.55/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.07  
% 2.55/1.07  fof(f15,negated_conjecture,(
% 2.55/1.07    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k7_partfun1(X1,X2,X3) = k3_funct_2(X0,X1,X2,X3)))))),
% 2.55/1.07    inference(negated_conjecture,[],[f14])).
% 2.55/1.07  
% 2.55/1.07  fof(f33,plain,(
% 2.55/1.07    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3) & m1_subset_1(X3,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.55/1.07    inference(ennf_transformation,[],[f15])).
% 2.55/1.07  
% 2.55/1.07  fof(f34,plain,(
% 2.55/1.07    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.55/1.07    inference(flattening,[],[f33])).
% 2.55/1.07  
% 2.55/1.07  fof(f42,plain,(
% 2.55/1.07    ( ! [X2,X0,X1] : (? [X3] : (k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3) & m1_subset_1(X3,X0)) => (k7_partfun1(X1,X2,sK4) != k3_funct_2(X0,X1,X2,sK4) & m1_subset_1(sK4,X0))) )),
% 2.55/1.07    introduced(choice_axiom,[])).
% 2.55/1.07  
% 2.55/1.07  fof(f41,plain,(
% 2.55/1.07    ( ! [X0,X1] : (? [X2] : (? [X3] : (k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k7_partfun1(X1,sK3,X3) != k3_funct_2(X0,X1,sK3,X3) & m1_subset_1(X3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK3,X0,X1) & v1_funct_1(sK3))) )),
% 2.55/1.07    introduced(choice_axiom,[])).
% 2.55/1.07  
% 2.55/1.07  fof(f40,plain,(
% 2.55/1.07    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (k7_partfun1(sK2,X2,X3) != k3_funct_2(X0,sK2,X2,X3) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) & v1_funct_2(X2,X0,sK2) & v1_funct_1(X2)) & ~v1_xboole_0(sK2))) )),
% 2.55/1.07    introduced(choice_axiom,[])).
% 2.55/1.07  
% 2.55/1.07  fof(f39,plain,(
% 2.55/1.07    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (k7_partfun1(X1,X2,X3) != k3_funct_2(sK1,X1,X2,X3) & m1_subset_1(X3,sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) & v1_funct_2(X2,sK1,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK1))),
% 2.55/1.07    introduced(choice_axiom,[])).
% 2.55/1.07  
% 2.55/1.07  fof(f43,plain,(
% 2.55/1.07    (((k7_partfun1(sK2,sK3,sK4) != k3_funct_2(sK1,sK2,sK3,sK4) & m1_subset_1(sK4,sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)),
% 2.55/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f34,f42,f41,f40,f39])).
% 2.55/1.07  
% 2.55/1.07  fof(f68,plain,(
% 2.55/1.07    m1_subset_1(sK4,sK1)),
% 2.55/1.07    inference(cnf_transformation,[],[f43])).
% 2.55/1.07  
% 2.55/1.07  fof(f11,axiom,(
% 2.55/1.07    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.55/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.07  
% 2.55/1.07  fof(f27,plain,(
% 2.55/1.07    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.55/1.07    inference(ennf_transformation,[],[f11])).
% 2.55/1.07  
% 2.55/1.07  fof(f28,plain,(
% 2.55/1.07    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.55/1.07    inference(flattening,[],[f27])).
% 2.55/1.07  
% 2.55/1.07  fof(f38,plain,(
% 2.55/1.07    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.55/1.07    inference(nnf_transformation,[],[f28])).
% 2.55/1.07  
% 2.55/1.07  fof(f55,plain,(
% 2.55/1.07    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.55/1.07    inference(cnf_transformation,[],[f38])).
% 2.55/1.07  
% 2.55/1.07  fof(f66,plain,(
% 2.55/1.07    v1_funct_2(sK3,sK1,sK2)),
% 2.55/1.07    inference(cnf_transformation,[],[f43])).
% 2.55/1.07  
% 2.55/1.07  fof(f67,plain,(
% 2.55/1.07    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.55/1.07    inference(cnf_transformation,[],[f43])).
% 2.55/1.07  
% 2.55/1.07  fof(f10,axiom,(
% 2.55/1.07    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.55/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.07  
% 2.55/1.07  fof(f26,plain,(
% 2.55/1.07    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.55/1.07    inference(ennf_transformation,[],[f10])).
% 2.55/1.07  
% 2.55/1.07  fof(f54,plain,(
% 2.55/1.07    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.55/1.07    inference(cnf_transformation,[],[f26])).
% 2.55/1.07  
% 2.55/1.07  fof(f63,plain,(
% 2.55/1.07    ~v1_xboole_0(sK1)),
% 2.55/1.07    inference(cnf_transformation,[],[f43])).
% 2.55/1.07  
% 2.55/1.07  fof(f4,axiom,(
% 2.55/1.07    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.55/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.07  
% 2.55/1.07  fof(f19,plain,(
% 2.55/1.07    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.55/1.07    inference(ennf_transformation,[],[f4])).
% 2.55/1.07  
% 2.55/1.07  fof(f20,plain,(
% 2.55/1.07    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.55/1.07    inference(flattening,[],[f19])).
% 2.55/1.07  
% 2.55/1.07  fof(f47,plain,(
% 2.55/1.07    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.55/1.07    inference(cnf_transformation,[],[f20])).
% 2.55/1.07  
% 2.55/1.07  fof(f9,axiom,(
% 2.55/1.07    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.55/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.07  
% 2.55/1.07  fof(f16,plain,(
% 2.55/1.07    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.55/1.07    inference(pure_predicate_removal,[],[f9])).
% 2.55/1.07  
% 2.55/1.07  fof(f25,plain,(
% 2.55/1.07    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.55/1.07    inference(ennf_transformation,[],[f16])).
% 2.55/1.07  
% 2.55/1.07  fof(f53,plain,(
% 2.55/1.07    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.55/1.07    inference(cnf_transformation,[],[f25])).
% 2.55/1.07  
% 2.55/1.07  fof(f12,axiom,(
% 2.55/1.07    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 2.55/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.07  
% 2.55/1.07  fof(f29,plain,(
% 2.55/1.07    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.55/1.07    inference(ennf_transformation,[],[f12])).
% 2.55/1.07  
% 2.55/1.07  fof(f30,plain,(
% 2.55/1.07    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.55/1.07    inference(flattening,[],[f29])).
% 2.55/1.07  
% 2.55/1.07  fof(f61,plain,(
% 2.55/1.07    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.55/1.07    inference(cnf_transformation,[],[f30])).
% 2.55/1.07  
% 2.55/1.07  fof(f8,axiom,(
% 2.55/1.07    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.55/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.07  
% 2.55/1.07  fof(f24,plain,(
% 2.55/1.07    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.55/1.07    inference(ennf_transformation,[],[f8])).
% 2.55/1.07  
% 2.55/1.07  fof(f52,plain,(
% 2.55/1.07    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.55/1.07    inference(cnf_transformation,[],[f24])).
% 2.55/1.07  
% 2.55/1.07  fof(f65,plain,(
% 2.55/1.07    v1_funct_1(sK3)),
% 2.55/1.07    inference(cnf_transformation,[],[f43])).
% 2.55/1.07  
% 2.55/1.07  fof(f2,axiom,(
% 2.55/1.07    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 2.55/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.07  
% 2.55/1.07  fof(f35,plain,(
% 2.55/1.07    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK0(X0),X0))),
% 2.55/1.07    introduced(choice_axiom,[])).
% 2.55/1.07  
% 2.55/1.07  fof(f36,plain,(
% 2.55/1.07    ! [X0] : m1_subset_1(sK0(X0),X0)),
% 2.55/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f2,f35])).
% 2.55/1.07  
% 2.55/1.07  fof(f45,plain,(
% 2.55/1.07    ( ! [X0] : (m1_subset_1(sK0(X0),X0)) )),
% 2.55/1.07    inference(cnf_transformation,[],[f36])).
% 2.55/1.07  
% 2.55/1.07  fof(f7,axiom,(
% 2.55/1.07    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.55/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.07  
% 2.55/1.07  fof(f23,plain,(
% 2.55/1.07    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.55/1.07    inference(ennf_transformation,[],[f7])).
% 2.55/1.07  
% 2.55/1.07  fof(f51,plain,(
% 2.55/1.07    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.55/1.07    inference(cnf_transformation,[],[f23])).
% 2.55/1.07  
% 2.55/1.07  fof(f64,plain,(
% 2.55/1.07    ~v1_xboole_0(sK2)),
% 2.55/1.07    inference(cnf_transformation,[],[f43])).
% 2.55/1.07  
% 2.55/1.07  fof(f5,axiom,(
% 2.55/1.07    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.55/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.07  
% 2.55/1.07  fof(f37,plain,(
% 2.55/1.07    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.55/1.07    inference(nnf_transformation,[],[f5])).
% 2.55/1.07  
% 2.55/1.07  fof(f48,plain,(
% 2.55/1.07    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.55/1.07    inference(cnf_transformation,[],[f37])).
% 2.55/1.07  
% 2.55/1.07  fof(f3,axiom,(
% 2.55/1.07    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.55/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.07  
% 2.55/1.07  fof(f46,plain,(
% 2.55/1.07    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.55/1.07    inference(cnf_transformation,[],[f3])).
% 2.55/1.07  
% 2.55/1.07  fof(f13,axiom,(
% 2.55/1.07    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3))),
% 2.55/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.07  
% 2.55/1.07  fof(f31,plain,(
% 2.55/1.07    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 2.55/1.07    inference(ennf_transformation,[],[f13])).
% 2.55/1.07  
% 2.55/1.07  fof(f32,plain,(
% 2.55/1.07    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 2.55/1.07    inference(flattening,[],[f31])).
% 2.55/1.07  
% 2.55/1.07  fof(f62,plain,(
% 2.55/1.07    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 2.55/1.07    inference(cnf_transformation,[],[f32])).
% 2.55/1.07  
% 2.55/1.07  fof(f69,plain,(
% 2.55/1.07    k7_partfun1(sK2,sK3,sK4) != k3_funct_2(sK1,sK2,sK3,sK4)),
% 2.55/1.07    inference(cnf_transformation,[],[f43])).
% 2.55/1.07  
% 2.55/1.07  cnf(c_20,negated_conjecture,
% 2.55/1.07      ( m1_subset_1(sK4,sK1) ),
% 2.55/1.07      inference(cnf_transformation,[],[f68]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_1579,plain,
% 2.55/1.07      ( m1_subset_1(sK4,sK1) = iProver_top ),
% 2.55/1.07      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_16,plain,
% 2.55/1.07      ( ~ v1_funct_2(X0,X1,X2)
% 2.55/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.55/1.07      | k1_relset_1(X1,X2,X0) = X1
% 2.55/1.07      | k1_xboole_0 = X2 ),
% 2.55/1.07      inference(cnf_transformation,[],[f55]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_22,negated_conjecture,
% 2.55/1.07      ( v1_funct_2(sK3,sK1,sK2) ),
% 2.55/1.07      inference(cnf_transformation,[],[f66]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_799,plain,
% 2.55/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.55/1.07      | k1_relset_1(X1,X2,X0) = X1
% 2.55/1.07      | sK1 != X1
% 2.55/1.07      | sK3 != X0
% 2.55/1.07      | sK2 != X2
% 2.55/1.07      | k1_xboole_0 = X2 ),
% 2.55/1.07      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_800,plain,
% 2.55/1.07      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.55/1.07      | k1_relset_1(sK1,sK2,sK3) = sK1
% 2.55/1.07      | k1_xboole_0 = sK2 ),
% 2.55/1.07      inference(unflattening,[status(thm)],[c_799]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_21,negated_conjecture,
% 2.55/1.07      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.55/1.07      inference(cnf_transformation,[],[f67]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_802,plain,
% 2.55/1.07      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 2.55/1.07      inference(global_propositional_subsumption,
% 2.55/1.07                [status(thm)],
% 2.55/1.07                [c_800,c_21]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_1578,plain,
% 2.55/1.07      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.55/1.07      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_10,plain,
% 2.55/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.55/1.07      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.55/1.07      inference(cnf_transformation,[],[f54]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_1580,plain,
% 2.55/1.07      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.55/1.07      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.55/1.07      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_2482,plain,
% 2.55/1.07      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 2.55/1.07      inference(superposition,[status(thm)],[c_1578,c_1580]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_2605,plain,
% 2.55/1.07      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 2.55/1.07      inference(superposition,[status(thm)],[c_802,c_2482]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_25,negated_conjecture,
% 2.55/1.07      ( ~ v1_xboole_0(sK1) ),
% 2.55/1.07      inference(cnf_transformation,[],[f63]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_3,plain,
% 2.55/1.07      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 2.55/1.07      inference(cnf_transformation,[],[f47]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_9,plain,
% 2.55/1.07      ( v5_relat_1(X0,X1)
% 2.55/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.55/1.07      inference(cnf_transformation,[],[f53]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_17,plain,
% 2.55/1.07      ( ~ v5_relat_1(X0,X1)
% 2.55/1.07      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.55/1.07      | ~ v1_funct_1(X0)
% 2.55/1.07      | ~ v1_relat_1(X0)
% 2.55/1.07      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 2.55/1.07      inference(cnf_transformation,[],[f61]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_362,plain,
% 2.55/1.07      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.55/1.07      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.55/1.07      | ~ v1_funct_1(X1)
% 2.55/1.07      | ~ v1_relat_1(X1)
% 2.55/1.07      | k7_partfun1(X3,X1,X0) = k1_funct_1(X1,X0) ),
% 2.55/1.07      inference(resolution,[status(thm)],[c_9,c_17]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_8,plain,
% 2.55/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.55/1.07      | v1_relat_1(X0) ),
% 2.55/1.07      inference(cnf_transformation,[],[f52]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_376,plain,
% 2.55/1.07      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.55/1.07      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.55/1.07      | ~ v1_funct_1(X1)
% 2.55/1.07      | k7_partfun1(X3,X1,X0) = k1_funct_1(X1,X0) ),
% 2.55/1.07      inference(forward_subsumption_resolution,[status(thm)],[c_362,c_8]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_23,negated_conjecture,
% 2.55/1.07      ( v1_funct_1(sK3) ),
% 2.55/1.07      inference(cnf_transformation,[],[f65]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_410,plain,
% 2.55/1.07      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.55/1.07      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.55/1.07      | k7_partfun1(X3,X1,X0) = k1_funct_1(X1,X0)
% 2.55/1.07      | sK3 != X1 ),
% 2.55/1.07      inference(resolution_lifted,[status(thm)],[c_376,c_23]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_411,plain,
% 2.55/1.07      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.55/1.07      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.55/1.07      | k7_partfun1(X2,sK3,X0) = k1_funct_1(sK3,X0) ),
% 2.55/1.07      inference(unflattening,[status(thm)],[c_410]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_464,plain,
% 2.55/1.07      ( ~ m1_subset_1(X0,X1)
% 2.55/1.07      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.55/1.07      | v1_xboole_0(X1)
% 2.55/1.07      | X4 != X0
% 2.55/1.07      | k7_partfun1(X3,sK3,X4) = k1_funct_1(sK3,X4)
% 2.55/1.07      | k1_relat_1(sK3) != X1 ),
% 2.55/1.07      inference(resolution_lifted,[status(thm)],[c_3,c_411]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_465,plain,
% 2.55/1.07      ( ~ m1_subset_1(X0,k1_relat_1(sK3))
% 2.55/1.07      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.55/1.07      | v1_xboole_0(k1_relat_1(sK3))
% 2.55/1.07      | k7_partfun1(X2,sK3,X0) = k1_funct_1(sK3,X0) ),
% 2.55/1.07      inference(unflattening,[status(thm)],[c_464]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_603,plain,
% 2.55/1.07      ( ~ m1_subset_1(X0,k1_relat_1(sK3))
% 2.55/1.07      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.55/1.07      | k7_partfun1(X2,sK3,X0) = k1_funct_1(sK3,X0)
% 2.55/1.07      | k1_relat_1(sK3) != sK1 ),
% 2.55/1.07      inference(resolution_lifted,[status(thm)],[c_25,c_465]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_1572,plain,
% 2.55/1.07      ( k7_partfun1(X0,sK3,X1) = k1_funct_1(sK3,X1)
% 2.55/1.07      | k1_relat_1(sK3) != sK1
% 2.55/1.07      | m1_subset_1(X1,k1_relat_1(sK3)) != iProver_top
% 2.55/1.07      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top ),
% 2.55/1.07      inference(predicate_to_equality,[status(thm)],[c_603]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_2677,plain,
% 2.55/1.07      ( k7_partfun1(X0,sK3,X1) = k1_funct_1(sK3,X1)
% 2.55/1.07      | sK2 = k1_xboole_0
% 2.55/1.07      | m1_subset_1(X1,k1_relat_1(sK3)) != iProver_top
% 2.55/1.07      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top ),
% 2.55/1.07      inference(superposition,[status(thm)],[c_2605,c_1572]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_604,plain,
% 2.55/1.07      ( k7_partfun1(X0,sK3,X1) = k1_funct_1(sK3,X1)
% 2.55/1.07      | k1_relat_1(sK3) != sK1
% 2.55/1.07      | m1_subset_1(X1,k1_relat_1(sK3)) != iProver_top
% 2.55/1.07      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top ),
% 2.55/1.07      inference(predicate_to_equality,[status(thm)],[c_603]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_1,plain,
% 2.55/1.07      ( m1_subset_1(sK0(X0),X0) ),
% 2.55/1.07      inference(cnf_transformation,[],[f45]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_1830,plain,
% 2.55/1.07      ( m1_subset_1(sK0(sK2),sK2) ),
% 2.55/1.07      inference(instantiation,[status(thm)],[c_1]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_7,plain,
% 2.55/1.07      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.55/1.07      inference(cnf_transformation,[],[f51]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_435,plain,
% 2.55/1.07      ( ~ m1_subset_1(X0,X1) | ~ r1_tarski(X1,X0) | v1_xboole_0(X1) ),
% 2.55/1.07      inference(resolution,[status(thm)],[c_3,c_7]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_24,negated_conjecture,
% 2.55/1.07      ( ~ v1_xboole_0(sK2) ),
% 2.55/1.07      inference(cnf_transformation,[],[f64]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_511,plain,
% 2.55/1.07      ( ~ m1_subset_1(X0,X1) | ~ r1_tarski(X1,X0) | sK2 != X1 ),
% 2.55/1.07      inference(resolution_lifted,[status(thm)],[c_435,c_24]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_512,plain,
% 2.55/1.07      ( ~ m1_subset_1(X0,sK2) | ~ r1_tarski(sK2,X0) ),
% 2.55/1.07      inference(unflattening,[status(thm)],[c_511]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_1832,plain,
% 2.55/1.07      ( ~ m1_subset_1(sK0(sK2),sK2) | ~ r1_tarski(sK2,sK0(sK2)) ),
% 2.55/1.07      inference(instantiation,[status(thm)],[c_512]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_954,plain,
% 2.55/1.07      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 2.55/1.07      theory(equality) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_1981,plain,
% 2.55/1.07      ( ~ r1_tarski(X0,sK0(sK2)) | r1_tarski(sK2,sK0(sK2)) | sK2 != X0 ),
% 2.55/1.07      inference(instantiation,[status(thm)],[c_954]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_1983,plain,
% 2.55/1.07      ( r1_tarski(sK2,sK0(sK2))
% 2.55/1.07      | ~ r1_tarski(k1_xboole_0,sK0(sK2))
% 2.55/1.07      | sK2 != k1_xboole_0 ),
% 2.55/1.07      inference(instantiation,[status(thm)],[c_1981]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_5,plain,
% 2.55/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.55/1.07      inference(cnf_transformation,[],[f48]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_2344,plain,
% 2.55/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0(sK2)))
% 2.55/1.07      | r1_tarski(X0,sK0(sK2)) ),
% 2.55/1.07      inference(instantiation,[status(thm)],[c_5]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_2346,plain,
% 2.55/1.07      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(sK2)))
% 2.55/1.07      | r1_tarski(k1_xboole_0,sK0(sK2)) ),
% 2.55/1.07      inference(instantiation,[status(thm)],[c_2344]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_2,plain,
% 2.55/1.07      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.55/1.07      inference(cnf_transformation,[],[f46]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_2879,plain,
% 2.55/1.07      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(sK2))) ),
% 2.55/1.07      inference(instantiation,[status(thm)],[c_2]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_3457,plain,
% 2.55/1.07      ( k7_partfun1(X0,sK3,X1) = k1_funct_1(sK3,X1)
% 2.55/1.07      | m1_subset_1(X1,k1_relat_1(sK3)) != iProver_top
% 2.55/1.07      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top ),
% 2.55/1.07      inference(global_propositional_subsumption,
% 2.55/1.07                [status(thm)],
% 2.55/1.07                [c_2677,c_604,c_1830,c_1832,c_1983,c_2346,c_2605,c_2879]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_3467,plain,
% 2.55/1.07      ( k7_partfun1(sK2,sK3,X0) = k1_funct_1(sK3,X0)
% 2.55/1.07      | m1_subset_1(X0,k1_relat_1(sK3)) != iProver_top ),
% 2.55/1.07      inference(superposition,[status(thm)],[c_1578,c_3457]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_3488,plain,
% 2.55/1.07      ( k7_partfun1(sK2,sK3,X0) = k1_funct_1(sK3,X0)
% 2.55/1.07      | sK2 = k1_xboole_0
% 2.55/1.07      | m1_subset_1(X0,sK1) != iProver_top ),
% 2.55/1.07      inference(superposition,[status(thm)],[c_2605,c_3467]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_4158,plain,
% 2.55/1.07      ( k7_partfun1(sK2,sK3,X0) = k1_funct_1(sK3,X0)
% 2.55/1.07      | m1_subset_1(X0,sK1) != iProver_top ),
% 2.55/1.07      inference(global_propositional_subsumption,
% 2.55/1.07                [status(thm)],
% 2.55/1.07                [c_3488,c_1830,c_1832,c_1983,c_2346,c_2879]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_4167,plain,
% 2.55/1.07      ( k7_partfun1(sK2,sK3,sK4) = k1_funct_1(sK3,sK4) ),
% 2.55/1.07      inference(superposition,[status(thm)],[c_1579,c_4158]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_18,plain,
% 2.55/1.07      ( ~ v1_funct_2(X0,X1,X2)
% 2.55/1.07      | ~ m1_subset_1(X3,X1)
% 2.55/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.55/1.07      | ~ v1_funct_1(X0)
% 2.55/1.07      | v1_xboole_0(X1)
% 2.55/1.07      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.55/1.07      inference(cnf_transformation,[],[f62]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_389,plain,
% 2.55/1.07      ( ~ v1_funct_2(X0,X1,X2)
% 2.55/1.07      | ~ m1_subset_1(X3,X1)
% 2.55/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.55/1.07      | v1_xboole_0(X1)
% 2.55/1.07      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
% 2.55/1.07      | sK3 != X0 ),
% 2.55/1.07      inference(resolution_lifted,[status(thm)],[c_18,c_23]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_390,plain,
% 2.55/1.07      ( ~ v1_funct_2(sK3,X0,X1)
% 2.55/1.07      | ~ m1_subset_1(X2,X0)
% 2.55/1.07      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.55/1.07      | v1_xboole_0(X0)
% 2.55/1.07      | k3_funct_2(X0,X1,sK3,X2) = k1_funct_1(sK3,X2) ),
% 2.55/1.07      inference(unflattening,[status(thm)],[c_389]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_568,plain,
% 2.55/1.07      ( ~ v1_funct_2(sK3,X0,X1)
% 2.55/1.07      | ~ m1_subset_1(X2,X0)
% 2.55/1.07      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.55/1.07      | k3_funct_2(X0,X1,sK3,X2) = k1_funct_1(sK3,X2)
% 2.55/1.07      | sK1 != X0 ),
% 2.55/1.07      inference(resolution_lifted,[status(thm)],[c_390,c_25]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_569,plain,
% 2.55/1.07      ( ~ v1_funct_2(sK3,sK1,X0)
% 2.55/1.07      | ~ m1_subset_1(X1,sK1)
% 2.55/1.07      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
% 2.55/1.07      | k3_funct_2(sK1,X0,sK3,X1) = k1_funct_1(sK3,X1) ),
% 2.55/1.07      inference(unflattening,[status(thm)],[c_568]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_870,plain,
% 2.55/1.07      ( ~ m1_subset_1(X0,sK1)
% 2.55/1.07      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 2.55/1.07      | k3_funct_2(sK1,X1,sK3,X0) = k1_funct_1(sK3,X0)
% 2.55/1.07      | sK1 != sK1
% 2.55/1.07      | sK3 != sK3
% 2.55/1.07      | sK2 != X1 ),
% 2.55/1.07      inference(resolution_lifted,[status(thm)],[c_22,c_569]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_871,plain,
% 2.55/1.07      ( ~ m1_subset_1(X0,sK1)
% 2.55/1.07      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.55/1.07      | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) ),
% 2.55/1.07      inference(unflattening,[status(thm)],[c_870]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_875,plain,
% 2.55/1.07      ( ~ m1_subset_1(X0,sK1)
% 2.55/1.07      | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) ),
% 2.55/1.07      inference(global_propositional_subsumption,
% 2.55/1.07                [status(thm)],
% 2.55/1.07                [c_871,c_21]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_1559,plain,
% 2.55/1.07      ( k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)
% 2.55/1.07      | m1_subset_1(X0,sK1) != iProver_top ),
% 2.55/1.07      inference(predicate_to_equality,[status(thm)],[c_875]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_1922,plain,
% 2.55/1.07      ( k3_funct_2(sK1,sK2,sK3,sK4) = k1_funct_1(sK3,sK4) ),
% 2.55/1.07      inference(superposition,[status(thm)],[c_1579,c_1559]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_19,negated_conjecture,
% 2.55/1.07      ( k7_partfun1(sK2,sK3,sK4) != k3_funct_2(sK1,sK2,sK3,sK4) ),
% 2.55/1.07      inference(cnf_transformation,[],[f69]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(c_2186,plain,
% 2.55/1.07      ( k7_partfun1(sK2,sK3,sK4) != k1_funct_1(sK3,sK4) ),
% 2.55/1.07      inference(demodulation,[status(thm)],[c_1922,c_19]) ).
% 2.55/1.07  
% 2.55/1.07  cnf(contradiction,plain,
% 2.55/1.07      ( $false ),
% 2.55/1.07      inference(minisat,[status(thm)],[c_4167,c_2186]) ).
% 2.55/1.07  
% 2.55/1.07  
% 2.55/1.07  % SZS output end CNFRefutation for theBenchmark.p
% 2.55/1.07  
% 2.55/1.07  ------                               Statistics
% 2.55/1.07  
% 2.55/1.07  ------ General
% 2.55/1.07  
% 2.55/1.07  abstr_ref_over_cycles:                  0
% 2.55/1.07  abstr_ref_under_cycles:                 0
% 2.55/1.07  gc_basic_clause_elim:                   0
% 2.55/1.07  forced_gc_time:                         0
% 2.55/1.07  parsing_time:                           0.016
% 2.55/1.07  unif_index_cands_time:                  0.
% 2.55/1.07  unif_index_add_time:                    0.
% 2.55/1.07  orderings_time:                         0.
% 2.55/1.07  out_proof_time:                         0.016
% 2.55/1.07  total_time:                             0.187
% 2.55/1.07  num_of_symbols:                         55
% 2.55/1.07  num_of_terms:                           3096
% 2.55/1.07  
% 2.55/1.07  ------ Preprocessing
% 2.55/1.07  
% 2.55/1.07  num_of_splits:                          3
% 2.55/1.07  num_of_split_atoms:                     3
% 2.55/1.07  num_of_reused_defs:                     0
% 2.55/1.07  num_eq_ax_congr_red:                    15
% 2.55/1.07  num_of_sem_filtered_clauses:            1
% 2.55/1.07  num_of_subtypes:                        0
% 2.55/1.07  monotx_restored_types:                  0
% 2.55/1.07  sat_num_of_epr_types:                   0
% 2.55/1.07  sat_num_of_non_cyclic_types:            0
% 2.55/1.07  sat_guarded_non_collapsed_types:        0
% 2.55/1.07  num_pure_diseq_elim:                    0
% 2.55/1.07  simp_replaced_by:                       0
% 2.55/1.07  res_preprocessed:                       107
% 2.55/1.07  prep_upred:                             0
% 2.55/1.07  prep_unflattend:                        53
% 2.55/1.07  smt_new_axioms:                         0
% 2.55/1.07  pred_elim_cands:                        8
% 2.55/1.07  pred_elim:                              6
% 2.55/1.07  pred_elim_cl:                           0
% 2.55/1.07  pred_elim_cycles:                       8
% 2.55/1.07  merged_defs:                            6
% 2.55/1.07  merged_defs_ncl:                        0
% 2.55/1.07  bin_hyper_res:                          6
% 2.55/1.07  prep_cycles:                            3
% 2.55/1.07  pred_elim_time:                         0.028
% 2.55/1.07  splitting_time:                         0.
% 2.55/1.07  sem_filter_time:                        0.
% 2.55/1.07  monotx_time:                            0.001
% 2.55/1.07  subtype_inf_time:                       0.
% 2.55/1.07  
% 2.55/1.07  ------ Problem properties
% 2.55/1.07  
% 2.55/1.07  clauses:                                29
% 2.55/1.07  conjectures:                            3
% 2.55/1.07  epr:                                    4
% 2.55/1.07  horn:                                   23
% 2.55/1.07  ground:                                 9
% 2.55/1.07  unary:                                  5
% 2.55/1.07  binary:                                 7
% 2.55/1.07  lits:                                   85
% 2.55/1.07  lits_eq:                                34
% 2.55/1.07  fd_pure:                                0
% 2.55/1.07  fd_pseudo:                              0
% 2.55/1.07  fd_cond:                                2
% 2.55/1.07  fd_pseudo_cond:                         0
% 2.55/1.07  ac_symbols:                             0
% 2.55/1.07  
% 2.55/1.07  ------ Propositional Solver
% 2.55/1.07  
% 2.55/1.07  prop_solver_calls:                      24
% 2.55/1.07  prop_fast_solver_calls:                 857
% 2.55/1.07  smt_solver_calls:                       0
% 2.55/1.07  smt_fast_solver_calls:                  0
% 2.55/1.07  prop_num_of_clauses:                    1265
% 2.55/1.07  prop_preprocess_simplified:             4517
% 2.55/1.07  prop_fo_subsumed:                       17
% 2.55/1.07  prop_solver_time:                       0.
% 2.55/1.07  smt_solver_time:                        0.
% 2.55/1.07  smt_fast_solver_time:                   0.
% 2.55/1.07  prop_fast_solver_time:                  0.
% 2.55/1.07  prop_unsat_core_time:                   0.
% 2.55/1.07  
% 2.55/1.07  ------ QBF
% 2.55/1.07  
% 2.55/1.07  qbf_q_res:                              0
% 2.55/1.07  qbf_num_tautologies:                    0
% 2.55/1.07  qbf_prep_cycles:                        0
% 2.55/1.07  
% 2.55/1.07  ------ BMC1
% 2.55/1.07  
% 2.55/1.07  bmc1_current_bound:                     -1
% 2.55/1.07  bmc1_last_solved_bound:                 -1
% 2.55/1.07  bmc1_unsat_core_size:                   -1
% 2.55/1.07  bmc1_unsat_core_parents_size:           -1
% 2.55/1.07  bmc1_merge_next_fun:                    0
% 2.55/1.07  bmc1_unsat_core_clauses_time:           0.
% 2.55/1.07  
% 2.55/1.07  ------ Instantiation
% 2.55/1.07  
% 2.55/1.07  inst_num_of_clauses:                    379
% 2.55/1.07  inst_num_in_passive:                    65
% 2.55/1.07  inst_num_in_active:                     274
% 2.55/1.07  inst_num_in_unprocessed:                40
% 2.55/1.07  inst_num_of_loops:                      300
% 2.55/1.07  inst_num_of_learning_restarts:          0
% 2.55/1.07  inst_num_moves_active_passive:          23
% 2.55/1.07  inst_lit_activity:                      0
% 2.55/1.07  inst_lit_activity_moves:                0
% 2.55/1.07  inst_num_tautologies:                   0
% 2.55/1.07  inst_num_prop_implied:                  0
% 2.55/1.07  inst_num_existing_simplified:           0
% 2.55/1.07  inst_num_eq_res_simplified:             0
% 2.55/1.07  inst_num_child_elim:                    0
% 2.55/1.07  inst_num_of_dismatching_blockings:      145
% 2.55/1.07  inst_num_of_non_proper_insts:           449
% 2.55/1.07  inst_num_of_duplicates:                 0
% 2.55/1.07  inst_inst_num_from_inst_to_res:         0
% 2.55/1.07  inst_dismatching_checking_time:         0.
% 2.55/1.07  
% 2.55/1.07  ------ Resolution
% 2.55/1.07  
% 2.55/1.07  res_num_of_clauses:                     0
% 2.55/1.07  res_num_in_passive:                     0
% 2.55/1.07  res_num_in_active:                      0
% 2.55/1.07  res_num_of_loops:                       110
% 2.55/1.07  res_forward_subset_subsumed:            24
% 2.55/1.07  res_backward_subset_subsumed:           0
% 2.55/1.07  res_forward_subsumed:                   0
% 2.55/1.07  res_backward_subsumed:                  0
% 2.55/1.07  res_forward_subsumption_resolution:     3
% 2.55/1.07  res_backward_subsumption_resolution:    0
% 2.55/1.07  res_clause_to_clause_subsumption:       166
% 2.55/1.07  res_orphan_elimination:                 0
% 2.55/1.07  res_tautology_del:                      70
% 2.55/1.07  res_num_eq_res_simplified:              0
% 2.55/1.07  res_num_sel_changes:                    0
% 2.55/1.07  res_moves_from_active_to_pass:          0
% 2.55/1.07  
% 2.55/1.07  ------ Superposition
% 2.55/1.07  
% 2.55/1.07  sup_time_total:                         0.
% 2.55/1.07  sup_time_generating:                    0.
% 2.55/1.07  sup_time_sim_full:                      0.
% 2.55/1.07  sup_time_sim_immed:                     0.
% 2.55/1.07  
% 2.55/1.07  sup_num_of_clauses:                     76
% 2.55/1.07  sup_num_in_active:                      56
% 2.55/1.07  sup_num_in_passive:                     20
% 2.55/1.07  sup_num_of_loops:                       58
% 2.55/1.07  sup_fw_superposition:                   34
% 2.55/1.07  sup_bw_superposition:                   29
% 2.55/1.07  sup_immediate_simplified:               9
% 2.55/1.07  sup_given_eliminated:                   0
% 2.55/1.07  comparisons_done:                       0
% 2.55/1.07  comparisons_avoided:                    5
% 2.55/1.07  
% 2.55/1.07  ------ Simplifications
% 2.55/1.07  
% 2.55/1.07  
% 2.55/1.07  sim_fw_subset_subsumed:                 5
% 2.55/1.07  sim_bw_subset_subsumed:                 2
% 2.55/1.07  sim_fw_subsumed:                        4
% 2.55/1.07  sim_bw_subsumed:                        0
% 2.55/1.07  sim_fw_subsumption_res:                 0
% 2.55/1.07  sim_bw_subsumption_res:                 0
% 2.55/1.07  sim_tautology_del:                      1
% 2.55/1.07  sim_eq_tautology_del:                   0
% 2.55/1.07  sim_eq_res_simp:                        0
% 2.55/1.07  sim_fw_demodulated:                     1
% 2.55/1.07  sim_bw_demodulated:                     2
% 2.55/1.07  sim_light_normalised:                   0
% 2.55/1.07  sim_joinable_taut:                      0
% 2.55/1.07  sim_joinable_simp:                      0
% 2.55/1.07  sim_ac_normalised:                      0
% 2.55/1.07  sim_smt_subsumption:                    0
% 2.55/1.07  
%------------------------------------------------------------------------------
