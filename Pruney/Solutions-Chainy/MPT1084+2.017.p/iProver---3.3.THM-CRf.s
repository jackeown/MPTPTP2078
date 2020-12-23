%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:34 EST 2020

% Result     : Theorem 1.45s
% Output     : CNFRefutation 1.45s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_702)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,X0)
               => k3_funct_2(X0,X0,X1,X2) = X2 )
           => r2_funct_2(X0,X0,X1,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X1,X0,X0)
              & v1_funct_1(X1) )
           => ( ! [X2] :
                  ( m1_subset_1(X2,X0)
                 => k3_funct_2(X0,X0,X1,X2) = X2 )
             => r2_funct_2(X0,X0,X1,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
          & ! [X2] :
              ( k3_funct_2(X0,X0,X1,X2) = X2
              | ~ m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
          & ! [X2] :
              ( k3_funct_2(X0,X0,X1,X2) = X2
              | ~ m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
          & ! [X2] :
              ( k3_funct_2(X0,X0,X1,X2) = X2
              | ~ m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
     => ( ~ r2_funct_2(X0,X0,sK2,k6_partfun1(X0))
        & ! [X2] :
            ( k3_funct_2(X0,X0,sK2,X2) = X2
            | ~ m1_subset_1(X2,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(sK2,X0,X0)
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
            & ! [X2] :
                ( k3_funct_2(X0,X0,X1,X2) = X2
                | ~ m1_subset_1(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ~ r2_funct_2(sK1,sK1,X1,k6_partfun1(sK1))
          & ! [X2] :
              ( k3_funct_2(sK1,sK1,X1,X2) = X2
              | ~ m1_subset_1(X2,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
          & v1_funct_2(X1,sK1,sK1)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ~ r2_funct_2(sK1,sK1,sK2,k6_partfun1(sK1))
    & ! [X2] :
        ( k3_funct_2(sK1,sK1,sK2,X2) = X2
        | ~ m1_subset_1(X2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v1_funct_2(sK2,sK1,sK1)
    & v1_funct_1(sK2)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f38,f37])).

fof(f61,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1)
            & r2_hidden(sK0(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK0(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k6_partfun1(X0) = X1
      | r2_hidden(sK0(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f48,f56])).

fof(f70,plain,(
    ! [X1] :
      ( k6_partfun1(k1_relat_1(X1)) = X1
      | r2_hidden(sK0(k1_relat_1(X1),X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f66])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f19])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f63,plain,(
    ! [X2] :
      ( k3_funct_2(sK1,sK1,sK2,X2) = X2
      | ~ m1_subset_1(X2,sK1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f58])).

fof(f64,plain,(
    ~ r2_funct_2(sK1,sK1,sK2,k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k6_partfun1(X0) = X1
      | k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f49,f56])).

fof(f69,plain,(
    ! [X1] :
      ( k6_partfun1(k1_relat_1(X1)) = X1
      | k1_funct_1(X1,sK0(k1_relat_1(X1),X1)) != sK0(k1_relat_1(X1),X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f65])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_376,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
    | sK2 != X2
    | sK1 != X1
    | sK1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_21])).

cnf(c_377,plain,
    ( ~ m1_subset_1(X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | k3_funct_2(sK1,sK1,sK2,X0) = k1_funct_1(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_23,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_381,plain,
    ( ~ m1_subset_1(X0,sK1)
    | k3_funct_2(sK1,sK1,sK2,X0) = k1_funct_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_377,c_23,c_22,c_20])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_7,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k6_partfun1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_420,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | k6_partfun1(k1_relat_1(X0)) = X0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_22])).

cnf(c_421,plain,
    ( r2_hidden(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_533,plain,
    ( m1_subset_1(X0,X1)
    | ~ v1_relat_1(sK2)
    | v1_xboole_0(X1)
    | sK0(k1_relat_1(sK2),sK2) != X0
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | k1_relat_1(sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_421])).

cnf(c_534,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | v1_xboole_0(k1_relat_1(sK2))
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(unflattening,[status(thm)],[c_533])).

cnf(c_680,plain,
    ( ~ v1_relat_1(sK2)
    | v1_xboole_0(k1_relat_1(sK2))
    | k3_funct_2(sK1,sK1,sK2,X0) = k1_funct_1(sK2,X0)
    | sK0(k1_relat_1(sK2),sK2) != X0
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | k1_relat_1(sK2) != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_381,c_534])).

cnf(c_681,plain,
    ( ~ v1_relat_1(sK2)
    | v1_xboole_0(k1_relat_1(sK2))
    | k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2))
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | k1_relat_1(sK2) != sK1 ),
    inference(unflattening,[status(thm)],[c_680])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_14,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_301,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_11,c_14])).

cnf(c_10,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_305,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_301,c_10])).

cnf(c_362,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1
    | sK2 != X0
    | sK1 != X1
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_305,c_21])).

cnf(c_363,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | v1_xboole_0(sK1)
    | k1_relat_1(sK2) = sK1 ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_365,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_363,c_23,c_22,c_20])).

cnf(c_683,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = sK2
    | k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2))
    | v1_xboole_0(k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_681,c_365])).

cnf(c_684,plain,
    ( ~ v1_relat_1(sK2)
    | v1_xboole_0(k1_relat_1(sK2))
    | k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2))
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(renaming,[status(thm)],[c_683])).

cnf(c_1263,plain,
    ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2))
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | v1_relat_1(sK2) != iProver_top
    | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_684])).

cnf(c_5,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_67,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_994,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1015,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_994])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_625,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_20])).

cnf(c_626,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_625])).

cnf(c_1409,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_626])).

cnf(c_1411,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK1))
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_1409])).

cnf(c_1437,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_994])).

cnf(c_996,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1542,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_relat_1(sK2))
    | X0 != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_996])).

cnf(c_1544,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | v1_xboole_0(sK1)
    | sK1 != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1542])).

cnf(c_995,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1648,plain,
    ( X0 != X1
    | X0 = k1_relat_1(sK2)
    | k1_relat_1(sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_995])).

cnf(c_1649,plain,
    ( k1_relat_1(sK2) != sK1
    | sK1 = k1_relat_1(sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1648])).

cnf(c_1748,plain,
    ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2))
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1263,c_23,c_22,c_20,c_67,c_363,c_684,c_1015,c_1411,c_1437,c_1544,c_1649])).

cnf(c_1266,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_626])).

cnf(c_66,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_68,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_1410,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1409])).

cnf(c_1412,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | v1_relat_1(k2_zfmisc_1(sK1,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1410])).

cnf(c_1472,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1266,c_68,c_1412,c_1437])).

cnf(c_1274,plain,
    ( k1_relat_1(sK2) = sK1
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_365])).

cnf(c_1477,plain,
    ( k1_relat_1(sK2) = sK1 ),
    inference(superposition,[status(thm)],[c_1472,c_1274])).

cnf(c_19,negated_conjecture,
    ( ~ m1_subset_1(X0,sK1)
    | k3_funct_2(sK1,sK1,sK2,X0) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_700,plain,
    ( ~ v1_relat_1(sK2)
    | v1_xboole_0(k1_relat_1(sK2))
    | k3_funct_2(sK1,sK1,sK2,X0) = X0
    | sK0(k1_relat_1(sK2),sK2) != X0
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | k1_relat_1(sK2) != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_534])).

cnf(c_701,plain,
    ( ~ v1_relat_1(sK2)
    | v1_xboole_0(k1_relat_1(sK2))
    | k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | k1_relat_1(sK2) != sK1 ),
    inference(unflattening,[status(thm)],[c_700])).

cnf(c_703,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = sK2
    | k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
    | v1_xboole_0(k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_701,c_23,c_22,c_20,c_363])).

cnf(c_704,plain,
    ( ~ v1_relat_1(sK2)
    | v1_xboole_0(k1_relat_1(sK2))
    | k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(renaming,[status(thm)],[c_703])).

cnf(c_1262,plain,
    ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | v1_relat_1(sK2) != iProver_top
    | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_704])).

cnf(c_705,plain,
    ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | v1_relat_1(sK2) != iProver_top
    | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_704])).

cnf(c_1501,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = sK2
    | k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
    | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1262,c_23,c_22,c_20,c_67,c_68,c_363,c_702,c_1411,c_1412,c_1437])).

cnf(c_1502,plain,
    ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1501])).

cnf(c_1598,plain,
    ( k3_funct_2(sK1,sK1,sK2,sK0(sK1,sK2)) = sK0(sK1,sK2)
    | k6_partfun1(sK1) = sK2
    | v1_xboole_0(sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1477,c_1502])).

cnf(c_24,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_16,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_18,negated_conjecture,
    ( ~ r2_funct_2(sK1,sK1,sK2,k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_341,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k6_partfun1(sK1) != X0
    | sK2 != X0
    | sK1 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_18])).

cnf(c_342,plain,
    ( ~ v1_funct_2(k6_partfun1(sK1),sK1,sK1)
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(k6_partfun1(sK1))
    | sK2 != k6_partfun1(sK1) ),
    inference(unflattening,[status(thm)],[c_341])).

cnf(c_394,plain,
    ( ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(k6_partfun1(sK1))
    | k6_partfun1(sK1) != sK2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_342])).

cnf(c_477,plain,
    ( ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) != sK2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_394])).

cnf(c_720,plain,
    ( k6_partfun1(sK1) != sK2
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_477])).

cnf(c_823,plain,
    ( k6_partfun1(sK1) != sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_720])).

cnf(c_1668,plain,
    ( k3_funct_2(sK1,sK1,sK2,sK0(sK1,sK2)) = sK0(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1598,c_24,c_823])).

cnf(c_1750,plain,
    ( k1_funct_1(sK2,sK0(sK1,sK2)) = sK0(sK1,sK2)
    | k6_partfun1(sK1) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_1748,c_1477,c_1668])).

cnf(c_0,plain,
    ( m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_608,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | k6_partfun1(sK1) != X0
    | k6_partfun1(sK1) != sK2
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_477])).

cnf(c_609,plain,
    ( ~ v1_xboole_0(k6_partfun1(sK1))
    | ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) != sK2 ),
    inference(unflattening,[status(thm)],[c_608])).

cnf(c_829,plain,
    ( k6_partfun1(sK1) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_609,c_823])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK0(k1_relat_1(X0),X0)) != sK0(k1_relat_1(X0),X0)
    | k6_partfun1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_433,plain,
    ( ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK0(k1_relat_1(X0),X0)) != sK0(k1_relat_1(X0),X0)
    | k6_partfun1(k1_relat_1(X0)) = X0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_22])).

cnf(c_434,plain,
    ( ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_1273,plain,
    ( k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_434])).

cnf(c_1548,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = sK2
    | k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1273,c_67,c_434,c_1411,c_1437])).

cnf(c_1549,plain,
    ( k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(renaming,[status(thm)],[c_1548])).

cnf(c_1597,plain,
    ( k1_funct_1(sK2,sK0(sK1,sK2)) != sK0(sK1,sK2)
    | k6_partfun1(sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_1477,c_1549])).

cnf(c_1664,plain,
    ( k1_funct_1(sK2,sK0(sK1,sK2)) != sK0(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1597,c_823])).

cnf(c_1753,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1750,c_829,c_1664])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:42:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.45/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.45/0.98  
% 1.45/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.45/0.98  
% 1.45/0.98  ------  iProver source info
% 1.45/0.98  
% 1.45/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.45/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.45/0.98  git: non_committed_changes: false
% 1.45/0.98  git: last_make_outside_of_git: false
% 1.45/0.98  
% 1.45/0.98  ------ 
% 1.45/0.98  
% 1.45/0.98  ------ Input Options
% 1.45/0.98  
% 1.45/0.98  --out_options                           all
% 1.45/0.98  --tptp_safe_out                         true
% 1.45/0.98  --problem_path                          ""
% 1.45/0.98  --include_path                          ""
% 1.45/0.98  --clausifier                            res/vclausify_rel
% 1.45/0.98  --clausifier_options                    --mode clausify
% 1.45/0.98  --stdin                                 false
% 1.45/0.98  --stats_out                             all
% 1.45/0.98  
% 1.45/0.98  ------ General Options
% 1.45/0.98  
% 1.45/0.98  --fof                                   false
% 1.45/0.98  --time_out_real                         305.
% 1.45/0.98  --time_out_virtual                      -1.
% 1.45/0.98  --symbol_type_check                     false
% 1.45/0.98  --clausify_out                          false
% 1.45/0.98  --sig_cnt_out                           false
% 1.45/0.98  --trig_cnt_out                          false
% 1.45/0.98  --trig_cnt_out_tolerance                1.
% 1.45/0.98  --trig_cnt_out_sk_spl                   false
% 1.45/0.98  --abstr_cl_out                          false
% 1.45/0.98  
% 1.45/0.98  ------ Global Options
% 1.45/0.98  
% 1.45/0.98  --schedule                              default
% 1.45/0.98  --add_important_lit                     false
% 1.45/0.98  --prop_solver_per_cl                    1000
% 1.45/0.98  --min_unsat_core                        false
% 1.45/0.98  --soft_assumptions                      false
% 1.45/0.98  --soft_lemma_size                       3
% 1.45/0.98  --prop_impl_unit_size                   0
% 1.45/0.98  --prop_impl_unit                        []
% 1.45/0.98  --share_sel_clauses                     true
% 1.45/0.98  --reset_solvers                         false
% 1.45/0.98  --bc_imp_inh                            [conj_cone]
% 1.45/0.98  --conj_cone_tolerance                   3.
% 1.45/0.98  --extra_neg_conj                        none
% 1.45/0.98  --large_theory_mode                     true
% 1.45/0.98  --prolific_symb_bound                   200
% 1.45/0.98  --lt_threshold                          2000
% 1.45/0.98  --clause_weak_htbl                      true
% 1.45/0.98  --gc_record_bc_elim                     false
% 1.45/0.98  
% 1.45/0.98  ------ Preprocessing Options
% 1.45/0.98  
% 1.45/0.98  --preprocessing_flag                    true
% 1.45/0.98  --time_out_prep_mult                    0.1
% 1.45/0.98  --splitting_mode                        input
% 1.45/0.98  --splitting_grd                         true
% 1.45/0.98  --splitting_cvd                         false
% 1.45/0.98  --splitting_cvd_svl                     false
% 1.45/0.98  --splitting_nvd                         32
% 1.45/0.98  --sub_typing                            true
% 1.45/0.98  --prep_gs_sim                           true
% 1.45/0.98  --prep_unflatten                        true
% 1.45/0.98  --prep_res_sim                          true
% 1.45/0.98  --prep_upred                            true
% 1.45/0.98  --prep_sem_filter                       exhaustive
% 1.45/0.98  --prep_sem_filter_out                   false
% 1.45/0.98  --pred_elim                             true
% 1.45/0.98  --res_sim_input                         true
% 1.45/0.98  --eq_ax_congr_red                       true
% 1.45/0.98  --pure_diseq_elim                       true
% 1.45/0.98  --brand_transform                       false
% 1.45/0.98  --non_eq_to_eq                          false
% 1.45/0.98  --prep_def_merge                        true
% 1.45/0.98  --prep_def_merge_prop_impl              false
% 1.45/0.98  --prep_def_merge_mbd                    true
% 1.45/0.98  --prep_def_merge_tr_red                 false
% 1.45/0.98  --prep_def_merge_tr_cl                  false
% 1.45/0.98  --smt_preprocessing                     true
% 1.45/0.98  --smt_ac_axioms                         fast
% 1.45/0.98  --preprocessed_out                      false
% 1.45/0.98  --preprocessed_stats                    false
% 1.45/0.98  
% 1.45/0.98  ------ Abstraction refinement Options
% 1.45/0.98  
% 1.45/0.98  --abstr_ref                             []
% 1.45/0.98  --abstr_ref_prep                        false
% 1.45/0.98  --abstr_ref_until_sat                   false
% 1.45/0.98  --abstr_ref_sig_restrict                funpre
% 1.45/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.45/0.98  --abstr_ref_under                       []
% 1.45/0.98  
% 1.45/0.98  ------ SAT Options
% 1.45/0.98  
% 1.45/0.98  --sat_mode                              false
% 1.45/0.98  --sat_fm_restart_options                ""
% 1.45/0.98  --sat_gr_def                            false
% 1.45/0.98  --sat_epr_types                         true
% 1.45/0.98  --sat_non_cyclic_types                  false
% 1.45/0.98  --sat_finite_models                     false
% 1.45/0.98  --sat_fm_lemmas                         false
% 1.45/0.98  --sat_fm_prep                           false
% 1.45/0.98  --sat_fm_uc_incr                        true
% 1.45/0.98  --sat_out_model                         small
% 1.45/0.98  --sat_out_clauses                       false
% 1.45/0.98  
% 1.45/0.98  ------ QBF Options
% 1.45/0.98  
% 1.45/0.98  --qbf_mode                              false
% 1.45/0.98  --qbf_elim_univ                         false
% 1.45/0.98  --qbf_dom_inst                          none
% 1.45/0.98  --qbf_dom_pre_inst                      false
% 1.45/0.98  --qbf_sk_in                             false
% 1.45/0.98  --qbf_pred_elim                         true
% 1.45/0.98  --qbf_split                             512
% 1.45/0.98  
% 1.45/0.98  ------ BMC1 Options
% 1.45/0.98  
% 1.45/0.98  --bmc1_incremental                      false
% 1.45/0.98  --bmc1_axioms                           reachable_all
% 1.45/0.98  --bmc1_min_bound                        0
% 1.45/0.98  --bmc1_max_bound                        -1
% 1.45/0.98  --bmc1_max_bound_default                -1
% 1.45/0.98  --bmc1_symbol_reachability              true
% 1.45/0.98  --bmc1_property_lemmas                  false
% 1.45/0.98  --bmc1_k_induction                      false
% 1.45/0.98  --bmc1_non_equiv_states                 false
% 1.45/0.98  --bmc1_deadlock                         false
% 1.45/0.98  --bmc1_ucm                              false
% 1.45/0.98  --bmc1_add_unsat_core                   none
% 1.45/0.98  --bmc1_unsat_core_children              false
% 1.45/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.45/0.98  --bmc1_out_stat                         full
% 1.45/0.98  --bmc1_ground_init                      false
% 1.45/0.98  --bmc1_pre_inst_next_state              false
% 1.45/0.98  --bmc1_pre_inst_state                   false
% 1.45/0.98  --bmc1_pre_inst_reach_state             false
% 1.45/0.98  --bmc1_out_unsat_core                   false
% 1.45/0.98  --bmc1_aig_witness_out                  false
% 1.45/0.98  --bmc1_verbose                          false
% 1.45/0.98  --bmc1_dump_clauses_tptp                false
% 1.45/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.45/0.98  --bmc1_dump_file                        -
% 1.45/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.45/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.45/0.98  --bmc1_ucm_extend_mode                  1
% 1.45/0.98  --bmc1_ucm_init_mode                    2
% 1.45/0.98  --bmc1_ucm_cone_mode                    none
% 1.45/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.45/0.98  --bmc1_ucm_relax_model                  4
% 1.45/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.45/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.45/0.98  --bmc1_ucm_layered_model                none
% 1.45/0.98  --bmc1_ucm_max_lemma_size               10
% 1.45/0.98  
% 1.45/0.98  ------ AIG Options
% 1.45/0.98  
% 1.45/0.98  --aig_mode                              false
% 1.45/0.98  
% 1.45/0.98  ------ Instantiation Options
% 1.45/0.98  
% 1.45/0.98  --instantiation_flag                    true
% 1.45/0.98  --inst_sos_flag                         false
% 1.45/0.98  --inst_sos_phase                        true
% 1.45/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.45/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.45/0.98  --inst_lit_sel_side                     num_symb
% 1.45/0.98  --inst_solver_per_active                1400
% 1.45/0.98  --inst_solver_calls_frac                1.
% 1.45/0.98  --inst_passive_queue_type               priority_queues
% 1.45/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.45/0.98  --inst_passive_queues_freq              [25;2]
% 1.45/0.98  --inst_dismatching                      true
% 1.45/0.98  --inst_eager_unprocessed_to_passive     true
% 1.45/0.98  --inst_prop_sim_given                   true
% 1.45/0.98  --inst_prop_sim_new                     false
% 1.45/0.98  --inst_subs_new                         false
% 1.45/0.98  --inst_eq_res_simp                      false
% 1.45/0.98  --inst_subs_given                       false
% 1.45/0.98  --inst_orphan_elimination               true
% 1.45/0.98  --inst_learning_loop_flag               true
% 1.45/0.98  --inst_learning_start                   3000
% 1.45/0.98  --inst_learning_factor                  2
% 1.45/0.98  --inst_start_prop_sim_after_learn       3
% 1.45/0.98  --inst_sel_renew                        solver
% 1.45/0.98  --inst_lit_activity_flag                true
% 1.45/0.98  --inst_restr_to_given                   false
% 1.45/0.98  --inst_activity_threshold               500
% 1.45/0.98  --inst_out_proof                        true
% 1.45/0.98  
% 1.45/0.98  ------ Resolution Options
% 1.45/0.98  
% 1.45/0.98  --resolution_flag                       true
% 1.45/0.98  --res_lit_sel                           adaptive
% 1.45/0.98  --res_lit_sel_side                      none
% 1.45/0.98  --res_ordering                          kbo
% 1.45/0.98  --res_to_prop_solver                    active
% 1.45/0.98  --res_prop_simpl_new                    false
% 1.45/0.98  --res_prop_simpl_given                  true
% 1.45/0.98  --res_passive_queue_type                priority_queues
% 1.45/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.45/0.98  --res_passive_queues_freq               [15;5]
% 1.45/0.98  --res_forward_subs                      full
% 1.45/0.98  --res_backward_subs                     full
% 1.45/0.98  --res_forward_subs_resolution           true
% 1.45/0.98  --res_backward_subs_resolution          true
% 1.45/0.98  --res_orphan_elimination                true
% 1.45/0.98  --res_time_limit                        2.
% 1.45/0.98  --res_out_proof                         true
% 1.45/0.98  
% 1.45/0.98  ------ Superposition Options
% 1.45/0.98  
% 1.45/0.98  --superposition_flag                    true
% 1.45/0.98  --sup_passive_queue_type                priority_queues
% 1.45/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.45/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.45/0.98  --demod_completeness_check              fast
% 1.45/0.98  --demod_use_ground                      true
% 1.45/0.98  --sup_to_prop_solver                    passive
% 1.45/0.98  --sup_prop_simpl_new                    true
% 1.45/0.98  --sup_prop_simpl_given                  true
% 1.45/0.98  --sup_fun_splitting                     false
% 1.45/0.98  --sup_smt_interval                      50000
% 1.45/0.98  
% 1.45/0.98  ------ Superposition Simplification Setup
% 1.45/0.98  
% 1.45/0.98  --sup_indices_passive                   []
% 1.45/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.45/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.45/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.45/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.45/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.45/0.98  --sup_full_bw                           [BwDemod]
% 1.45/0.98  --sup_immed_triv                        [TrivRules]
% 1.45/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.45/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.45/0.98  --sup_immed_bw_main                     []
% 1.45/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.45/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.45/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.45/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.45/0.98  
% 1.45/0.98  ------ Combination Options
% 1.45/0.98  
% 1.45/0.98  --comb_res_mult                         3
% 1.45/0.98  --comb_sup_mult                         2
% 1.45/0.98  --comb_inst_mult                        10
% 1.45/0.98  
% 1.45/0.98  ------ Debug Options
% 1.45/0.98  
% 1.45/0.98  --dbg_backtrace                         false
% 1.45/0.98  --dbg_dump_prop_clauses                 false
% 1.45/0.98  --dbg_dump_prop_clauses_file            -
% 1.45/0.98  --dbg_out_stat                          false
% 1.45/0.98  ------ Parsing...
% 1.45/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.45/0.98  
% 1.45/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 1.45/0.98  
% 1.45/0.98  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.45/0.98  
% 1.45/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.45/0.98  ------ Proving...
% 1.45/0.98  ------ Problem Properties 
% 1.45/0.98  
% 1.45/0.98  
% 1.45/0.98  clauses                                 18
% 1.45/0.98  conjectures                             1
% 1.45/0.98  EPR                                     3
% 1.45/0.98  Horn                                    13
% 1.45/0.98  unary                                   3
% 1.45/0.98  binary                                  5
% 1.45/0.98  lits                                    48
% 1.45/0.98  lits eq                                 19
% 1.45/0.98  fd_pure                                 0
% 1.45/0.98  fd_pseudo                               0
% 1.45/0.98  fd_cond                                 0
% 1.45/0.98  fd_pseudo_cond                          0
% 1.45/0.98  AC symbols                              0
% 1.45/0.98  
% 1.45/0.98  ------ Schedule dynamic 5 is on 
% 1.45/0.98  
% 1.45/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.45/0.98  
% 1.45/0.98  
% 1.45/0.98  ------ 
% 1.45/0.98  Current options:
% 1.45/0.98  ------ 
% 1.45/0.98  
% 1.45/0.98  ------ Input Options
% 1.45/0.98  
% 1.45/0.98  --out_options                           all
% 1.45/0.98  --tptp_safe_out                         true
% 1.45/0.98  --problem_path                          ""
% 1.45/0.98  --include_path                          ""
% 1.45/0.98  --clausifier                            res/vclausify_rel
% 1.45/0.98  --clausifier_options                    --mode clausify
% 1.45/0.98  --stdin                                 false
% 1.45/0.98  --stats_out                             all
% 1.45/0.98  
% 1.45/0.98  ------ General Options
% 1.45/0.98  
% 1.45/0.98  --fof                                   false
% 1.45/0.98  --time_out_real                         305.
% 1.45/0.98  --time_out_virtual                      -1.
% 1.45/0.98  --symbol_type_check                     false
% 1.45/0.98  --clausify_out                          false
% 1.45/0.98  --sig_cnt_out                           false
% 1.45/0.98  --trig_cnt_out                          false
% 1.45/0.98  --trig_cnt_out_tolerance                1.
% 1.45/0.98  --trig_cnt_out_sk_spl                   false
% 1.45/0.98  --abstr_cl_out                          false
% 1.45/0.98  
% 1.45/0.98  ------ Global Options
% 1.45/0.98  
% 1.45/0.98  --schedule                              default
% 1.45/0.98  --add_important_lit                     false
% 1.45/0.98  --prop_solver_per_cl                    1000
% 1.45/0.98  --min_unsat_core                        false
% 1.45/0.98  --soft_assumptions                      false
% 1.45/0.98  --soft_lemma_size                       3
% 1.45/0.98  --prop_impl_unit_size                   0
% 1.45/0.98  --prop_impl_unit                        []
% 1.45/0.98  --share_sel_clauses                     true
% 1.45/0.98  --reset_solvers                         false
% 1.45/0.98  --bc_imp_inh                            [conj_cone]
% 1.45/0.98  --conj_cone_tolerance                   3.
% 1.45/0.98  --extra_neg_conj                        none
% 1.45/0.98  --large_theory_mode                     true
% 1.45/0.98  --prolific_symb_bound                   200
% 1.45/0.98  --lt_threshold                          2000
% 1.45/0.98  --clause_weak_htbl                      true
% 1.45/0.98  --gc_record_bc_elim                     false
% 1.45/0.98  
% 1.45/0.98  ------ Preprocessing Options
% 1.45/0.98  
% 1.45/0.98  --preprocessing_flag                    true
% 1.45/0.98  --time_out_prep_mult                    0.1
% 1.45/0.98  --splitting_mode                        input
% 1.45/0.98  --splitting_grd                         true
% 1.45/0.98  --splitting_cvd                         false
% 1.45/0.98  --splitting_cvd_svl                     false
% 1.45/0.98  --splitting_nvd                         32
% 1.45/0.98  --sub_typing                            true
% 1.45/0.98  --prep_gs_sim                           true
% 1.45/0.98  --prep_unflatten                        true
% 1.45/0.98  --prep_res_sim                          true
% 1.45/0.98  --prep_upred                            true
% 1.45/0.98  --prep_sem_filter                       exhaustive
% 1.45/0.98  --prep_sem_filter_out                   false
% 1.45/0.98  --pred_elim                             true
% 1.45/0.98  --res_sim_input                         true
% 1.45/0.98  --eq_ax_congr_red                       true
% 1.45/0.98  --pure_diseq_elim                       true
% 1.45/0.98  --brand_transform                       false
% 1.45/0.98  --non_eq_to_eq                          false
% 1.45/0.98  --prep_def_merge                        true
% 1.45/0.98  --prep_def_merge_prop_impl              false
% 1.45/0.98  --prep_def_merge_mbd                    true
% 1.45/0.98  --prep_def_merge_tr_red                 false
% 1.45/0.98  --prep_def_merge_tr_cl                  false
% 1.45/0.98  --smt_preprocessing                     true
% 1.45/0.98  --smt_ac_axioms                         fast
% 1.45/0.98  --preprocessed_out                      false
% 1.45/0.98  --preprocessed_stats                    false
% 1.45/0.98  
% 1.45/0.98  ------ Abstraction refinement Options
% 1.45/0.98  
% 1.45/0.98  --abstr_ref                             []
% 1.45/0.98  --abstr_ref_prep                        false
% 1.45/0.98  --abstr_ref_until_sat                   false
% 1.45/0.98  --abstr_ref_sig_restrict                funpre
% 1.45/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.45/0.98  --abstr_ref_under                       []
% 1.45/0.98  
% 1.45/0.98  ------ SAT Options
% 1.45/0.98  
% 1.45/0.98  --sat_mode                              false
% 1.45/0.98  --sat_fm_restart_options                ""
% 1.45/0.98  --sat_gr_def                            false
% 1.45/0.98  --sat_epr_types                         true
% 1.45/0.98  --sat_non_cyclic_types                  false
% 1.45/0.98  --sat_finite_models                     false
% 1.45/0.98  --sat_fm_lemmas                         false
% 1.45/0.98  --sat_fm_prep                           false
% 1.45/0.98  --sat_fm_uc_incr                        true
% 1.45/0.98  --sat_out_model                         small
% 1.45/0.98  --sat_out_clauses                       false
% 1.45/0.98  
% 1.45/0.98  ------ QBF Options
% 1.45/0.98  
% 1.45/0.98  --qbf_mode                              false
% 1.45/0.98  --qbf_elim_univ                         false
% 1.45/0.98  --qbf_dom_inst                          none
% 1.45/0.98  --qbf_dom_pre_inst                      false
% 1.45/0.98  --qbf_sk_in                             false
% 1.45/0.98  --qbf_pred_elim                         true
% 1.45/0.98  --qbf_split                             512
% 1.45/0.98  
% 1.45/0.98  ------ BMC1 Options
% 1.45/0.98  
% 1.45/0.98  --bmc1_incremental                      false
% 1.45/0.98  --bmc1_axioms                           reachable_all
% 1.45/0.98  --bmc1_min_bound                        0
% 1.45/0.98  --bmc1_max_bound                        -1
% 1.45/0.98  --bmc1_max_bound_default                -1
% 1.45/0.98  --bmc1_symbol_reachability              true
% 1.45/0.98  --bmc1_property_lemmas                  false
% 1.45/0.98  --bmc1_k_induction                      false
% 1.45/0.98  --bmc1_non_equiv_states                 false
% 1.45/0.98  --bmc1_deadlock                         false
% 1.45/0.98  --bmc1_ucm                              false
% 1.45/0.98  --bmc1_add_unsat_core                   none
% 1.45/0.98  --bmc1_unsat_core_children              false
% 1.45/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.45/0.98  --bmc1_out_stat                         full
% 1.45/0.98  --bmc1_ground_init                      false
% 1.45/0.98  --bmc1_pre_inst_next_state              false
% 1.45/0.98  --bmc1_pre_inst_state                   false
% 1.45/0.98  --bmc1_pre_inst_reach_state             false
% 1.45/0.98  --bmc1_out_unsat_core                   false
% 1.45/0.98  --bmc1_aig_witness_out                  false
% 1.45/0.98  --bmc1_verbose                          false
% 1.45/0.98  --bmc1_dump_clauses_tptp                false
% 1.45/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.45/0.98  --bmc1_dump_file                        -
% 1.45/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.45/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.45/0.98  --bmc1_ucm_extend_mode                  1
% 1.45/0.98  --bmc1_ucm_init_mode                    2
% 1.45/0.98  --bmc1_ucm_cone_mode                    none
% 1.45/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.45/0.98  --bmc1_ucm_relax_model                  4
% 1.45/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.45/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.45/0.98  --bmc1_ucm_layered_model                none
% 1.45/0.98  --bmc1_ucm_max_lemma_size               10
% 1.45/0.98  
% 1.45/0.98  ------ AIG Options
% 1.45/0.98  
% 1.45/0.98  --aig_mode                              false
% 1.45/0.98  
% 1.45/0.98  ------ Instantiation Options
% 1.45/0.98  
% 1.45/0.98  --instantiation_flag                    true
% 1.45/0.98  --inst_sos_flag                         false
% 1.45/0.98  --inst_sos_phase                        true
% 1.45/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.45/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.45/0.98  --inst_lit_sel_side                     none
% 1.45/0.98  --inst_solver_per_active                1400
% 1.45/0.98  --inst_solver_calls_frac                1.
% 1.45/0.98  --inst_passive_queue_type               priority_queues
% 1.45/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.45/0.98  --inst_passive_queues_freq              [25;2]
% 1.45/0.98  --inst_dismatching                      true
% 1.45/0.98  --inst_eager_unprocessed_to_passive     true
% 1.45/0.98  --inst_prop_sim_given                   true
% 1.45/0.98  --inst_prop_sim_new                     false
% 1.45/0.98  --inst_subs_new                         false
% 1.45/0.98  --inst_eq_res_simp                      false
% 1.45/0.98  --inst_subs_given                       false
% 1.45/0.98  --inst_orphan_elimination               true
% 1.45/0.98  --inst_learning_loop_flag               true
% 1.45/0.98  --inst_learning_start                   3000
% 1.45/0.98  --inst_learning_factor                  2
% 1.45/0.98  --inst_start_prop_sim_after_learn       3
% 1.45/0.98  --inst_sel_renew                        solver
% 1.45/0.98  --inst_lit_activity_flag                true
% 1.45/0.98  --inst_restr_to_given                   false
% 1.45/0.98  --inst_activity_threshold               500
% 1.45/0.98  --inst_out_proof                        true
% 1.45/0.98  
% 1.45/0.98  ------ Resolution Options
% 1.45/0.98  
% 1.45/0.98  --resolution_flag                       false
% 1.45/0.98  --res_lit_sel                           adaptive
% 1.45/0.98  --res_lit_sel_side                      none
% 1.45/0.98  --res_ordering                          kbo
% 1.45/0.98  --res_to_prop_solver                    active
% 1.45/0.98  --res_prop_simpl_new                    false
% 1.45/0.98  --res_prop_simpl_given                  true
% 1.45/0.98  --res_passive_queue_type                priority_queues
% 1.45/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.45/0.98  --res_passive_queues_freq               [15;5]
% 1.45/0.98  --res_forward_subs                      full
% 1.45/0.98  --res_backward_subs                     full
% 1.45/0.98  --res_forward_subs_resolution           true
% 1.45/0.98  --res_backward_subs_resolution          true
% 1.45/0.98  --res_orphan_elimination                true
% 1.45/0.98  --res_time_limit                        2.
% 1.45/0.98  --res_out_proof                         true
% 1.45/0.98  
% 1.45/0.98  ------ Superposition Options
% 1.45/0.98  
% 1.45/0.98  --superposition_flag                    true
% 1.45/0.98  --sup_passive_queue_type                priority_queues
% 1.45/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.45/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.45/0.98  --demod_completeness_check              fast
% 1.45/0.98  --demod_use_ground                      true
% 1.45/0.98  --sup_to_prop_solver                    passive
% 1.45/0.98  --sup_prop_simpl_new                    true
% 1.45/0.98  --sup_prop_simpl_given                  true
% 1.45/0.98  --sup_fun_splitting                     false
% 1.45/0.98  --sup_smt_interval                      50000
% 1.45/0.98  
% 1.45/0.98  ------ Superposition Simplification Setup
% 1.45/0.98  
% 1.45/0.98  --sup_indices_passive                   []
% 1.45/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.45/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.45/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.45/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.45/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.45/0.98  --sup_full_bw                           [BwDemod]
% 1.45/0.98  --sup_immed_triv                        [TrivRules]
% 1.45/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.45/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.45/0.98  --sup_immed_bw_main                     []
% 1.45/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.45/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.45/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.45/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.45/0.98  
% 1.45/0.98  ------ Combination Options
% 1.45/0.98  
% 1.45/0.98  --comb_res_mult                         3
% 1.45/0.98  --comb_sup_mult                         2
% 1.45/0.98  --comb_inst_mult                        10
% 1.45/0.98  
% 1.45/0.98  ------ Debug Options
% 1.45/0.98  
% 1.45/0.98  --dbg_backtrace                         false
% 1.45/0.98  --dbg_dump_prop_clauses                 false
% 1.45/0.98  --dbg_dump_prop_clauses_file            -
% 1.45/0.98  --dbg_out_stat                          false
% 1.45/0.98  
% 1.45/0.98  
% 1.45/0.98  
% 1.45/0.98  
% 1.45/0.98  ------ Proving...
% 1.45/0.98  
% 1.45/0.98  
% 1.45/0.98  % SZS status Theorem for theBenchmark.p
% 1.45/0.98  
% 1.45/0.98   Resolution empty clause
% 1.45/0.98  
% 1.45/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.45/0.98  
% 1.45/0.98  fof(f8,axiom,(
% 1.45/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3))),
% 1.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.45/0.98  
% 1.45/0.98  fof(f23,plain,(
% 1.45/0.98    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 1.45/0.98    inference(ennf_transformation,[],[f8])).
% 1.45/0.98  
% 1.45/0.98  fof(f24,plain,(
% 1.45/0.98    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 1.45/0.98    inference(flattening,[],[f23])).
% 1.45/0.98  
% 1.45/0.98  fof(f55,plain,(
% 1.45/0.98    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 1.45/0.98    inference(cnf_transformation,[],[f24])).
% 1.45/0.98  
% 1.45/0.98  fof(f11,conjecture,(
% 1.45/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (! [X2] : (m1_subset_1(X2,X0) => k3_funct_2(X0,X0,X1,X2) = X2) => r2_funct_2(X0,X0,X1,k6_partfun1(X0)))))),
% 1.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.45/0.98  
% 1.45/0.98  fof(f12,negated_conjecture,(
% 1.45/0.98    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (! [X2] : (m1_subset_1(X2,X0) => k3_funct_2(X0,X0,X1,X2) = X2) => r2_funct_2(X0,X0,X1,k6_partfun1(X0)))))),
% 1.45/0.98    inference(negated_conjecture,[],[f11])).
% 1.45/0.98  
% 1.45/0.98  fof(f27,plain,(
% 1.45/0.98    ? [X0] : (? [X1] : ((~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))) & ~v1_xboole_0(X0))),
% 1.45/0.98    inference(ennf_transformation,[],[f12])).
% 1.45/0.98  
% 1.45/0.98  fof(f28,plain,(
% 1.45/0.98    ? [X0] : (? [X1] : (~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0))),
% 1.45/0.98    inference(flattening,[],[f27])).
% 1.45/0.98  
% 1.45/0.98  fof(f38,plain,(
% 1.45/0.98    ( ! [X0] : (? [X1] : (~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (~r2_funct_2(X0,X0,sK2,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,sK2,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 1.45/0.98    introduced(choice_axiom,[])).
% 1.45/0.98  
% 1.45/0.98  fof(f37,plain,(
% 1.45/0.98    ? [X0] : (? [X1] : (~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (~r2_funct_2(sK1,sK1,X1,k6_partfun1(sK1)) & ! [X2] : (k3_funct_2(sK1,sK1,X1,X2) = X2 | ~m1_subset_1(X2,sK1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_2(X1,sK1,sK1) & v1_funct_1(X1)) & ~v1_xboole_0(sK1))),
% 1.45/0.98    introduced(choice_axiom,[])).
% 1.45/0.98  
% 1.45/0.98  fof(f39,plain,(
% 1.45/0.98    (~r2_funct_2(sK1,sK1,sK2,k6_partfun1(sK1)) & ! [X2] : (k3_funct_2(sK1,sK1,sK2,X2) = X2 | ~m1_subset_1(X2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)) & ~v1_xboole_0(sK1)),
% 1.45/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f38,f37])).
% 1.45/0.98  
% 1.45/0.98  fof(f61,plain,(
% 1.45/0.98    v1_funct_2(sK2,sK1,sK1)),
% 1.45/0.98    inference(cnf_transformation,[],[f39])).
% 1.45/0.98  
% 1.45/0.98  fof(f59,plain,(
% 1.45/0.98    ~v1_xboole_0(sK1)),
% 1.45/0.98    inference(cnf_transformation,[],[f39])).
% 1.45/0.98  
% 1.45/0.98  fof(f60,plain,(
% 1.45/0.98    v1_funct_1(sK2)),
% 1.45/0.98    inference(cnf_transformation,[],[f39])).
% 1.45/0.98  
% 1.45/0.98  fof(f62,plain,(
% 1.45/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 1.45/0.98    inference(cnf_transformation,[],[f39])).
% 1.45/0.98  
% 1.45/0.98  fof(f1,axiom,(
% 1.45/0.98    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.45/0.98  
% 1.45/0.98  fof(f14,plain,(
% 1.45/0.98    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.45/0.98    inference(ennf_transformation,[],[f1])).
% 1.45/0.98  
% 1.45/0.98  fof(f29,plain,(
% 1.45/0.98    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.45/0.98    inference(nnf_transformation,[],[f14])).
% 1.45/0.98  
% 1.45/0.98  fof(f41,plain,(
% 1.45/0.98    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.45/0.98    inference(cnf_transformation,[],[f29])).
% 1.45/0.98  
% 1.45/0.98  fof(f4,axiom,(
% 1.45/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 1.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.45/0.98  
% 1.45/0.98  fof(f16,plain,(
% 1.45/0.98    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.45/0.98    inference(ennf_transformation,[],[f4])).
% 1.45/0.98  
% 1.45/0.98  fof(f17,plain,(
% 1.45/0.98    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.45/0.98    inference(flattening,[],[f16])).
% 1.45/0.98  
% 1.45/0.98  fof(f30,plain,(
% 1.45/0.98    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.45/0.98    inference(nnf_transformation,[],[f17])).
% 1.45/0.98  
% 1.45/0.98  fof(f31,plain,(
% 1.45/0.98    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.45/0.98    inference(flattening,[],[f30])).
% 1.45/0.98  
% 1.45/0.98  fof(f32,plain,(
% 1.45/0.98    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.45/0.98    inference(rectify,[],[f31])).
% 1.45/0.98  
% 1.45/0.98  fof(f33,plain,(
% 1.45/0.98    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.45/0.98    introduced(choice_axiom,[])).
% 1.45/0.98  
% 1.45/0.98  fof(f34,plain,(
% 1.45/0.98    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1) & r2_hidden(sK0(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.45/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 1.45/0.98  
% 1.45/0.98  fof(f48,plain,(
% 1.45/0.98    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | r2_hidden(sK0(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.45/0.98    inference(cnf_transformation,[],[f34])).
% 1.45/0.98  
% 1.45/0.98  fof(f9,axiom,(
% 1.45/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.45/0.98  
% 1.45/0.98  fof(f56,plain,(
% 1.45/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.45/0.98    inference(cnf_transformation,[],[f9])).
% 1.45/0.98  
% 1.45/0.98  fof(f66,plain,(
% 1.45/0.98    ( ! [X0,X1] : (k6_partfun1(X0) = X1 | r2_hidden(sK0(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.45/0.98    inference(definition_unfolding,[],[f48,f56])).
% 1.45/0.98  
% 1.45/0.98  fof(f70,plain,(
% 1.45/0.98    ( ! [X1] : (k6_partfun1(k1_relat_1(X1)) = X1 | r2_hidden(sK0(k1_relat_1(X1),X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.45/0.98    inference(equality_resolution,[],[f66])).
% 1.45/0.98  
% 1.45/0.98  fof(f6,axiom,(
% 1.45/0.98    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.45/0.98  
% 1.45/0.98  fof(f19,plain,(
% 1.45/0.98    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.45/0.98    inference(ennf_transformation,[],[f6])).
% 1.45/0.98  
% 1.45/0.98  fof(f20,plain,(
% 1.45/0.98    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.45/0.98    inference(flattening,[],[f19])).
% 1.45/0.98  
% 1.45/0.98  fof(f52,plain,(
% 1.45/0.98    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 1.45/0.98    inference(cnf_transformation,[],[f20])).
% 1.45/0.98  
% 1.45/0.98  fof(f7,axiom,(
% 1.45/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.45/0.98  
% 1.45/0.98  fof(f21,plain,(
% 1.45/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.45/0.98    inference(ennf_transformation,[],[f7])).
% 1.45/0.98  
% 1.45/0.98  fof(f22,plain,(
% 1.45/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.45/0.98    inference(flattening,[],[f21])).
% 1.45/0.98  
% 1.45/0.98  fof(f35,plain,(
% 1.45/0.98    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.45/0.98    inference(nnf_transformation,[],[f22])).
% 1.45/0.98  
% 1.45/0.98  fof(f53,plain,(
% 1.45/0.98    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.45/0.98    inference(cnf_transformation,[],[f35])).
% 1.45/0.98  
% 1.45/0.98  fof(f5,axiom,(
% 1.45/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.45/0.98  
% 1.45/0.98  fof(f13,plain,(
% 1.45/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.45/0.98    inference(pure_predicate_removal,[],[f5])).
% 1.45/0.98  
% 1.45/0.98  fof(f18,plain,(
% 1.45/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.98    inference(ennf_transformation,[],[f13])).
% 1.45/0.98  
% 1.45/0.98  fof(f50,plain,(
% 1.45/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.45/0.98    inference(cnf_transformation,[],[f18])).
% 1.45/0.98  
% 1.45/0.98  fof(f3,axiom,(
% 1.45/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.45/0.98  
% 1.45/0.98  fof(f45,plain,(
% 1.45/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.45/0.98    inference(cnf_transformation,[],[f3])).
% 1.45/0.98  
% 1.45/0.98  fof(f2,axiom,(
% 1.45/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.45/0.98  
% 1.45/0.98  fof(f15,plain,(
% 1.45/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.45/0.98    inference(ennf_transformation,[],[f2])).
% 1.45/0.98  
% 1.45/0.98  fof(f44,plain,(
% 1.45/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.45/0.98    inference(cnf_transformation,[],[f15])).
% 1.45/0.98  
% 1.45/0.98  fof(f63,plain,(
% 1.45/0.98    ( ! [X2] : (k3_funct_2(sK1,sK1,sK2,X2) = X2 | ~m1_subset_1(X2,sK1)) )),
% 1.45/0.98    inference(cnf_transformation,[],[f39])).
% 1.45/0.98  
% 1.45/0.98  fof(f10,axiom,(
% 1.45/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.45/0.98  
% 1.45/0.98  fof(f25,plain,(
% 1.45/0.98    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.45/0.98    inference(ennf_transformation,[],[f10])).
% 1.45/0.98  
% 1.45/0.98  fof(f26,plain,(
% 1.45/0.98    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.45/0.98    inference(flattening,[],[f25])).
% 1.45/0.98  
% 1.45/0.98  fof(f36,plain,(
% 1.45/0.98    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.45/0.98    inference(nnf_transformation,[],[f26])).
% 1.45/0.98  
% 1.45/0.98  fof(f58,plain,(
% 1.45/0.98    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.45/0.98    inference(cnf_transformation,[],[f36])).
% 1.45/0.98  
% 1.45/0.98  fof(f74,plain,(
% 1.45/0.98    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.45/0.98    inference(equality_resolution,[],[f58])).
% 1.45/0.98  
% 1.45/0.98  fof(f64,plain,(
% 1.45/0.98    ~r2_funct_2(sK1,sK1,sK2,k6_partfun1(sK1))),
% 1.45/0.98    inference(cnf_transformation,[],[f39])).
% 1.45/0.98  
% 1.45/0.98  fof(f43,plain,(
% 1.45/0.98    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 1.45/0.98    inference(cnf_transformation,[],[f29])).
% 1.45/0.98  
% 1.45/0.98  fof(f49,plain,(
% 1.45/0.98    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.45/0.98    inference(cnf_transformation,[],[f34])).
% 1.45/0.98  
% 1.45/0.98  fof(f65,plain,(
% 1.45/0.98    ( ! [X0,X1] : (k6_partfun1(X0) = X1 | k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.45/0.98    inference(definition_unfolding,[],[f49,f56])).
% 1.45/0.98  
% 1.45/0.98  fof(f69,plain,(
% 1.45/0.98    ( ! [X1] : (k6_partfun1(k1_relat_1(X1)) = X1 | k1_funct_1(X1,sK0(k1_relat_1(X1),X1)) != sK0(k1_relat_1(X1),X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.45/0.98    inference(equality_resolution,[],[f65])).
% 1.45/0.98  
% 1.45/0.98  cnf(c_15,plain,
% 1.45/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.45/0.98      | ~ m1_subset_1(X3,X1)
% 1.45/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.45/0.98      | ~ v1_funct_1(X0)
% 1.45/0.98      | v1_xboole_0(X1)
% 1.45/0.98      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 1.45/0.98      inference(cnf_transformation,[],[f55]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_21,negated_conjecture,
% 1.45/0.98      ( v1_funct_2(sK2,sK1,sK1) ),
% 1.45/0.98      inference(cnf_transformation,[],[f61]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_376,plain,
% 1.45/0.98      ( ~ m1_subset_1(X0,X1)
% 1.45/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 1.45/0.98      | ~ v1_funct_1(X2)
% 1.45/0.98      | v1_xboole_0(X1)
% 1.45/0.98      | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
% 1.45/0.98      | sK2 != X2
% 1.45/0.98      | sK1 != X1
% 1.45/0.98      | sK1 != X3 ),
% 1.45/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_21]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_377,plain,
% 1.45/0.98      ( ~ m1_subset_1(X0,sK1)
% 1.45/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.45/0.98      | ~ v1_funct_1(sK2)
% 1.45/0.98      | v1_xboole_0(sK1)
% 1.45/0.98      | k3_funct_2(sK1,sK1,sK2,X0) = k1_funct_1(sK2,X0) ),
% 1.45/0.98      inference(unflattening,[status(thm)],[c_376]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_23,negated_conjecture,
% 1.45/0.98      ( ~ v1_xboole_0(sK1) ),
% 1.45/0.98      inference(cnf_transformation,[],[f59]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_22,negated_conjecture,
% 1.45/0.98      ( v1_funct_1(sK2) ),
% 1.45/0.98      inference(cnf_transformation,[],[f60]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_20,negated_conjecture,
% 1.45/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 1.45/0.98      inference(cnf_transformation,[],[f62]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_381,plain,
% 1.45/0.98      ( ~ m1_subset_1(X0,sK1)
% 1.45/0.98      | k3_funct_2(sK1,sK1,sK2,X0) = k1_funct_1(sK2,X0) ),
% 1.45/0.98      inference(global_propositional_subsumption,
% 1.45/0.98                [status(thm)],
% 1.45/0.98                [c_377,c_23,c_22,c_20]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_2,plain,
% 1.45/0.98      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 1.45/0.98      inference(cnf_transformation,[],[f41]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_7,plain,
% 1.45/0.98      ( r2_hidden(sK0(k1_relat_1(X0),X0),k1_relat_1(X0))
% 1.45/0.98      | ~ v1_funct_1(X0)
% 1.45/0.98      | ~ v1_relat_1(X0)
% 1.45/0.98      | k6_partfun1(k1_relat_1(X0)) = X0 ),
% 1.45/0.98      inference(cnf_transformation,[],[f70]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_420,plain,
% 1.45/0.98      ( r2_hidden(sK0(k1_relat_1(X0),X0),k1_relat_1(X0))
% 1.45/0.98      | ~ v1_relat_1(X0)
% 1.45/0.98      | k6_partfun1(k1_relat_1(X0)) = X0
% 1.45/0.98      | sK2 != X0 ),
% 1.45/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_22]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_421,plain,
% 1.45/0.98      ( r2_hidden(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
% 1.45/0.98      | ~ v1_relat_1(sK2)
% 1.45/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.45/0.98      inference(unflattening,[status(thm)],[c_420]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_533,plain,
% 1.45/0.98      ( m1_subset_1(X0,X1)
% 1.45/0.98      | ~ v1_relat_1(sK2)
% 1.45/0.98      | v1_xboole_0(X1)
% 1.45/0.98      | sK0(k1_relat_1(sK2),sK2) != X0
% 1.45/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.45/0.98      | k1_relat_1(sK2) != X1 ),
% 1.45/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_421]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_534,plain,
% 1.45/0.98      ( m1_subset_1(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
% 1.45/0.98      | ~ v1_relat_1(sK2)
% 1.45/0.98      | v1_xboole_0(k1_relat_1(sK2))
% 1.45/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.45/0.98      inference(unflattening,[status(thm)],[c_533]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_680,plain,
% 1.45/0.98      ( ~ v1_relat_1(sK2)
% 1.45/0.98      | v1_xboole_0(k1_relat_1(sK2))
% 1.45/0.98      | k3_funct_2(sK1,sK1,sK2,X0) = k1_funct_1(sK2,X0)
% 1.45/0.98      | sK0(k1_relat_1(sK2),sK2) != X0
% 1.45/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.45/0.98      | k1_relat_1(sK2) != sK1 ),
% 1.45/0.98      inference(resolution_lifted,[status(thm)],[c_381,c_534]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_681,plain,
% 1.45/0.98      ( ~ v1_relat_1(sK2)
% 1.45/0.98      | v1_xboole_0(k1_relat_1(sK2))
% 1.45/0.98      | k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2))
% 1.45/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.45/0.98      | k1_relat_1(sK2) != sK1 ),
% 1.45/0.98      inference(unflattening,[status(thm)],[c_680]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_11,plain,
% 1.45/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.45/0.98      | v1_partfun1(X0,X1)
% 1.45/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.45/0.98      | ~ v1_funct_1(X0)
% 1.45/0.98      | v1_xboole_0(X2) ),
% 1.45/0.98      inference(cnf_transformation,[],[f52]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_14,plain,
% 1.45/0.98      ( ~ v1_partfun1(X0,X1)
% 1.45/0.98      | ~ v4_relat_1(X0,X1)
% 1.45/0.98      | ~ v1_relat_1(X0)
% 1.45/0.98      | k1_relat_1(X0) = X1 ),
% 1.45/0.98      inference(cnf_transformation,[],[f53]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_301,plain,
% 1.45/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.45/0.98      | ~ v4_relat_1(X0,X1)
% 1.45/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.45/0.98      | ~ v1_funct_1(X0)
% 1.45/0.98      | ~ v1_relat_1(X0)
% 1.45/0.98      | v1_xboole_0(X2)
% 1.45/0.98      | k1_relat_1(X0) = X1 ),
% 1.45/0.98      inference(resolution,[status(thm)],[c_11,c_14]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_10,plain,
% 1.45/0.98      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.45/0.98      inference(cnf_transformation,[],[f50]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_305,plain,
% 1.45/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.45/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.45/0.98      | ~ v1_funct_1(X0)
% 1.45/0.98      | ~ v1_relat_1(X0)
% 1.45/0.98      | v1_xboole_0(X2)
% 1.45/0.98      | k1_relat_1(X0) = X1 ),
% 1.45/0.98      inference(global_propositional_subsumption,[status(thm)],[c_301,c_10]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_362,plain,
% 1.45/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.45/0.98      | ~ v1_funct_1(X0)
% 1.45/0.98      | ~ v1_relat_1(X0)
% 1.45/0.98      | v1_xboole_0(X2)
% 1.45/0.98      | k1_relat_1(X0) = X1
% 1.45/0.98      | sK2 != X0
% 1.45/0.98      | sK1 != X1
% 1.45/0.98      | sK1 != X2 ),
% 1.45/0.98      inference(resolution_lifted,[status(thm)],[c_305,c_21]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_363,plain,
% 1.45/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.45/0.98      | ~ v1_funct_1(sK2)
% 1.45/0.98      | ~ v1_relat_1(sK2)
% 1.45/0.98      | v1_xboole_0(sK1)
% 1.45/0.98      | k1_relat_1(sK2) = sK1 ),
% 1.45/0.98      inference(unflattening,[status(thm)],[c_362]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_365,plain,
% 1.45/0.98      ( ~ v1_relat_1(sK2) | k1_relat_1(sK2) = sK1 ),
% 1.45/0.98      inference(global_propositional_subsumption,
% 1.45/0.98                [status(thm)],
% 1.45/0.98                [c_363,c_23,c_22,c_20]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_683,plain,
% 1.45/0.98      ( k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.45/0.98      | k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2))
% 1.45/0.98      | v1_xboole_0(k1_relat_1(sK2))
% 1.45/0.98      | ~ v1_relat_1(sK2) ),
% 1.45/0.98      inference(global_propositional_subsumption,[status(thm)],[c_681,c_365]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_684,plain,
% 1.45/0.98      ( ~ v1_relat_1(sK2)
% 1.45/0.98      | v1_xboole_0(k1_relat_1(sK2))
% 1.45/0.98      | k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2))
% 1.45/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.45/0.98      inference(renaming,[status(thm)],[c_683]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1263,plain,
% 1.45/0.98      ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2))
% 1.45/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.45/0.98      | v1_relat_1(sK2) != iProver_top
% 1.45/0.98      | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
% 1.45/0.98      inference(predicate_to_equality,[status(thm)],[c_684]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_5,plain,
% 1.45/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.45/0.98      inference(cnf_transformation,[],[f45]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_67,plain,
% 1.45/0.98      ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) ),
% 1.45/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_994,plain,( X0 = X0 ),theory(equality) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1015,plain,
% 1.45/0.98      ( sK1 = sK1 ),
% 1.45/0.98      inference(instantiation,[status(thm)],[c_994]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_4,plain,
% 1.45/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 1.45/0.98      inference(cnf_transformation,[],[f44]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_625,plain,
% 1.45/0.98      ( ~ v1_relat_1(X0)
% 1.45/0.98      | v1_relat_1(X1)
% 1.45/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(X0)
% 1.45/0.98      | sK2 != X1 ),
% 1.45/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_20]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_626,plain,
% 1.45/0.98      ( ~ v1_relat_1(X0)
% 1.45/0.98      | v1_relat_1(sK2)
% 1.45/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(X0) ),
% 1.45/0.98      inference(unflattening,[status(thm)],[c_625]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1409,plain,
% 1.45/0.98      ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 1.45/0.98      | v1_relat_1(sK2)
% 1.45/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.45/0.98      inference(instantiation,[status(thm)],[c_626]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1411,plain,
% 1.45/0.98      ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK1))
% 1.45/0.98      | v1_relat_1(sK2)
% 1.45/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
% 1.45/0.98      inference(instantiation,[status(thm)],[c_1409]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1437,plain,
% 1.45/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
% 1.45/0.98      inference(instantiation,[status(thm)],[c_994]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_996,plain,
% 1.45/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 1.45/0.98      theory(equality) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1542,plain,
% 1.45/0.98      ( v1_xboole_0(X0)
% 1.45/0.98      | ~ v1_xboole_0(k1_relat_1(sK2))
% 1.45/0.98      | X0 != k1_relat_1(sK2) ),
% 1.45/0.98      inference(instantiation,[status(thm)],[c_996]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1544,plain,
% 1.45/0.98      ( ~ v1_xboole_0(k1_relat_1(sK2))
% 1.45/0.98      | v1_xboole_0(sK1)
% 1.45/0.98      | sK1 != k1_relat_1(sK2) ),
% 1.45/0.98      inference(instantiation,[status(thm)],[c_1542]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_995,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1648,plain,
% 1.45/0.98      ( X0 != X1 | X0 = k1_relat_1(sK2) | k1_relat_1(sK2) != X1 ),
% 1.45/0.98      inference(instantiation,[status(thm)],[c_995]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1649,plain,
% 1.45/0.98      ( k1_relat_1(sK2) != sK1 | sK1 = k1_relat_1(sK2) | sK1 != sK1 ),
% 1.45/0.98      inference(instantiation,[status(thm)],[c_1648]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1748,plain,
% 1.45/0.98      ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2))
% 1.45/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.45/0.98      inference(global_propositional_subsumption,
% 1.45/0.98                [status(thm)],
% 1.45/0.98                [c_1263,c_23,c_22,c_20,c_67,c_363,c_684,c_1015,c_1411,c_1437,
% 1.45/0.98                 c_1544,c_1649]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1266,plain,
% 1.45/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(X0)
% 1.45/0.98      | v1_relat_1(X0) != iProver_top
% 1.45/0.98      | v1_relat_1(sK2) = iProver_top ),
% 1.45/0.98      inference(predicate_to_equality,[status(thm)],[c_626]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_66,plain,
% 1.45/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 1.45/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_68,plain,
% 1.45/0.98      ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) = iProver_top ),
% 1.45/0.98      inference(instantiation,[status(thm)],[c_66]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1410,plain,
% 1.45/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.45/0.98      | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top
% 1.45/0.98      | v1_relat_1(sK2) = iProver_top ),
% 1.45/0.98      inference(predicate_to_equality,[status(thm)],[c_1409]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1412,plain,
% 1.45/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.45/0.98      | v1_relat_1(k2_zfmisc_1(sK1,sK1)) != iProver_top
% 1.45/0.98      | v1_relat_1(sK2) = iProver_top ),
% 1.45/0.98      inference(instantiation,[status(thm)],[c_1410]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1472,plain,
% 1.45/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 1.45/0.98      inference(global_propositional_subsumption,
% 1.45/0.98                [status(thm)],
% 1.45/0.98                [c_1266,c_68,c_1412,c_1437]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1274,plain,
% 1.45/0.98      ( k1_relat_1(sK2) = sK1 | v1_relat_1(sK2) != iProver_top ),
% 1.45/0.98      inference(predicate_to_equality,[status(thm)],[c_365]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1477,plain,
% 1.45/0.98      ( k1_relat_1(sK2) = sK1 ),
% 1.45/0.98      inference(superposition,[status(thm)],[c_1472,c_1274]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_19,negated_conjecture,
% 1.45/0.98      ( ~ m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK1,sK2,X0) = X0 ),
% 1.45/0.98      inference(cnf_transformation,[],[f63]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_700,plain,
% 1.45/0.98      ( ~ v1_relat_1(sK2)
% 1.45/0.98      | v1_xboole_0(k1_relat_1(sK2))
% 1.45/0.98      | k3_funct_2(sK1,sK1,sK2,X0) = X0
% 1.45/0.98      | sK0(k1_relat_1(sK2),sK2) != X0
% 1.45/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.45/0.98      | k1_relat_1(sK2) != sK1 ),
% 1.45/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_534]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_701,plain,
% 1.45/0.98      ( ~ v1_relat_1(sK2)
% 1.45/0.98      | v1_xboole_0(k1_relat_1(sK2))
% 1.45/0.98      | k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
% 1.45/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.45/0.98      | k1_relat_1(sK2) != sK1 ),
% 1.45/0.98      inference(unflattening,[status(thm)],[c_700]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_703,plain,
% 1.45/0.98      ( k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.45/0.98      | k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
% 1.45/0.98      | v1_xboole_0(k1_relat_1(sK2))
% 1.45/0.98      | ~ v1_relat_1(sK2) ),
% 1.45/0.98      inference(global_propositional_subsumption,
% 1.45/0.98                [status(thm)],
% 1.45/0.98                [c_701,c_23,c_22,c_20,c_363]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_704,plain,
% 1.45/0.98      ( ~ v1_relat_1(sK2)
% 1.45/0.98      | v1_xboole_0(k1_relat_1(sK2))
% 1.45/0.98      | k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
% 1.45/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.45/0.98      inference(renaming,[status(thm)],[c_703]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1262,plain,
% 1.45/0.98      ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
% 1.45/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.45/0.98      | v1_relat_1(sK2) != iProver_top
% 1.45/0.98      | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
% 1.45/0.98      inference(predicate_to_equality,[status(thm)],[c_704]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_705,plain,
% 1.45/0.98      ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
% 1.45/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.45/0.98      | v1_relat_1(sK2) != iProver_top
% 1.45/0.98      | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
% 1.45/0.98      inference(predicate_to_equality,[status(thm)],[c_704]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1501,plain,
% 1.45/0.98      ( k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.45/0.98      | k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
% 1.45/0.98      | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
% 1.45/0.98      inference(global_propositional_subsumption,
% 1.45/0.98                [status(thm)],
% 1.45/0.98                [c_1262,c_23,c_22,c_20,c_67,c_68,c_363,c_702,c_1411,c_1412,
% 1.45/0.98                 c_1437]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1502,plain,
% 1.45/0.98      ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
% 1.45/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.45/0.98      | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
% 1.45/0.98      inference(renaming,[status(thm)],[c_1501]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1598,plain,
% 1.45/0.98      ( k3_funct_2(sK1,sK1,sK2,sK0(sK1,sK2)) = sK0(sK1,sK2)
% 1.45/0.98      | k6_partfun1(sK1) = sK2
% 1.45/0.98      | v1_xboole_0(sK1) = iProver_top ),
% 1.45/0.98      inference(demodulation,[status(thm)],[c_1477,c_1502]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_24,plain,
% 1.45/0.98      ( v1_xboole_0(sK1) != iProver_top ),
% 1.45/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_16,plain,
% 1.45/0.98      ( r2_funct_2(X0,X1,X2,X2)
% 1.45/0.98      | ~ v1_funct_2(X2,X0,X1)
% 1.45/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.45/0.98      | ~ v1_funct_1(X2) ),
% 1.45/0.98      inference(cnf_transformation,[],[f74]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_18,negated_conjecture,
% 1.45/0.98      ( ~ r2_funct_2(sK1,sK1,sK2,k6_partfun1(sK1)) ),
% 1.45/0.98      inference(cnf_transformation,[],[f64]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_341,plain,
% 1.45/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.45/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.45/0.98      | ~ v1_funct_1(X0)
% 1.45/0.98      | k6_partfun1(sK1) != X0
% 1.45/0.98      | sK2 != X0
% 1.45/0.98      | sK1 != X2
% 1.45/0.98      | sK1 != X1 ),
% 1.45/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_18]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_342,plain,
% 1.45/0.98      ( ~ v1_funct_2(k6_partfun1(sK1),sK1,sK1)
% 1.45/0.98      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.45/0.98      | ~ v1_funct_1(k6_partfun1(sK1))
% 1.45/0.98      | sK2 != k6_partfun1(sK1) ),
% 1.45/0.98      inference(unflattening,[status(thm)],[c_341]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_394,plain,
% 1.45/0.98      ( ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.45/0.98      | ~ v1_funct_1(k6_partfun1(sK1))
% 1.45/0.98      | k6_partfun1(sK1) != sK2
% 1.45/0.98      | sK1 != sK1 ),
% 1.45/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_342]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_477,plain,
% 1.45/0.98      ( ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.45/0.98      | k6_partfun1(sK1) != sK2
% 1.45/0.98      | sK1 != sK1 ),
% 1.45/0.98      inference(resolution_lifted,[status(thm)],[c_22,c_394]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_720,plain,
% 1.45/0.98      ( k6_partfun1(sK1) != sK2
% 1.45/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.45/0.98      | sK1 != sK1 ),
% 1.45/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_477]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_823,plain,
% 1.45/0.98      ( k6_partfun1(sK1) != sK2 ),
% 1.45/0.98      inference(equality_resolution_simp,[status(thm)],[c_720]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1668,plain,
% 1.45/0.98      ( k3_funct_2(sK1,sK1,sK2,sK0(sK1,sK2)) = sK0(sK1,sK2) ),
% 1.45/0.98      inference(global_propositional_subsumption,
% 1.45/0.98                [status(thm)],
% 1.45/0.98                [c_1598,c_24,c_823]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1750,plain,
% 1.45/0.98      ( k1_funct_1(sK2,sK0(sK1,sK2)) = sK0(sK1,sK2) | k6_partfun1(sK1) = sK2 ),
% 1.45/0.98      inference(light_normalisation,[status(thm)],[c_1748,c_1477,c_1668]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_0,plain,
% 1.45/0.98      ( m1_subset_1(X0,X1) | ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) ),
% 1.45/0.98      inference(cnf_transformation,[],[f43]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_608,plain,
% 1.45/0.98      ( ~ v1_xboole_0(X0)
% 1.45/0.98      | ~ v1_xboole_0(X1)
% 1.45/0.98      | k6_partfun1(sK1) != X0
% 1.45/0.98      | k6_partfun1(sK1) != sK2
% 1.45/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != X1
% 1.45/0.98      | sK1 != sK1 ),
% 1.45/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_477]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_609,plain,
% 1.45/0.98      ( ~ v1_xboole_0(k6_partfun1(sK1))
% 1.45/0.98      | ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.45/0.98      | k6_partfun1(sK1) != sK2 ),
% 1.45/0.98      inference(unflattening,[status(thm)],[c_608]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_829,plain,
% 1.45/0.98      ( k6_partfun1(sK1) != sK2 ),
% 1.45/0.98      inference(global_propositional_subsumption,[status(thm)],[c_609,c_823]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_6,plain,
% 1.45/0.98      ( ~ v1_funct_1(X0)
% 1.45/0.98      | ~ v1_relat_1(X0)
% 1.45/0.98      | k1_funct_1(X0,sK0(k1_relat_1(X0),X0)) != sK0(k1_relat_1(X0),X0)
% 1.45/0.98      | k6_partfun1(k1_relat_1(X0)) = X0 ),
% 1.45/0.98      inference(cnf_transformation,[],[f69]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_433,plain,
% 1.45/0.98      ( ~ v1_relat_1(X0)
% 1.45/0.98      | k1_funct_1(X0,sK0(k1_relat_1(X0),X0)) != sK0(k1_relat_1(X0),X0)
% 1.45/0.98      | k6_partfun1(k1_relat_1(X0)) = X0
% 1.45/0.98      | sK2 != X0 ),
% 1.45/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_22]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_434,plain,
% 1.45/0.98      ( ~ v1_relat_1(sK2)
% 1.45/0.98      | k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
% 1.45/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.45/0.98      inference(unflattening,[status(thm)],[c_433]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1273,plain,
% 1.45/0.98      ( k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
% 1.45/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.45/0.98      | v1_relat_1(sK2) != iProver_top ),
% 1.45/0.98      inference(predicate_to_equality,[status(thm)],[c_434]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1548,plain,
% 1.45/0.98      ( k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.45/0.98      | k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2) ),
% 1.45/0.98      inference(global_propositional_subsumption,
% 1.45/0.98                [status(thm)],
% 1.45/0.98                [c_1273,c_67,c_434,c_1411,c_1437]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1549,plain,
% 1.45/0.98      ( k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
% 1.45/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.45/0.98      inference(renaming,[status(thm)],[c_1548]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1597,plain,
% 1.45/0.98      ( k1_funct_1(sK2,sK0(sK1,sK2)) != sK0(sK1,sK2) | k6_partfun1(sK1) = sK2 ),
% 1.45/0.98      inference(demodulation,[status(thm)],[c_1477,c_1549]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1664,plain,
% 1.45/0.98      ( k1_funct_1(sK2,sK0(sK1,sK2)) != sK0(sK1,sK2) ),
% 1.45/0.98      inference(global_propositional_subsumption,[status(thm)],[c_1597,c_823]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1753,plain,
% 1.45/0.98      ( $false ),
% 1.45/0.98      inference(forward_subsumption_resolution,
% 1.45/0.98                [status(thm)],
% 1.45/0.98                [c_1750,c_829,c_1664]) ).
% 1.45/0.98  
% 1.45/0.98  
% 1.45/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.45/0.98  
% 1.45/0.98  ------                               Statistics
% 1.45/0.98  
% 1.45/0.98  ------ General
% 1.45/0.98  
% 1.45/0.98  abstr_ref_over_cycles:                  0
% 1.45/0.98  abstr_ref_under_cycles:                 0
% 1.45/0.98  gc_basic_clause_elim:                   0
% 1.45/0.98  forced_gc_time:                         0
% 1.45/0.98  parsing_time:                           0.008
% 1.45/0.98  unif_index_cands_time:                  0.
% 1.45/0.98  unif_index_add_time:                    0.
% 1.45/0.98  orderings_time:                         0.
% 1.45/0.98  out_proof_time:                         0.013
% 1.45/0.98  total_time:                             0.087
% 1.45/0.98  num_of_symbols:                         52
% 1.45/0.98  num_of_terms:                           1050
% 1.45/0.98  
% 1.45/0.98  ------ Preprocessing
% 1.45/0.98  
% 1.45/0.98  num_of_splits:                          3
% 1.45/0.98  num_of_split_atoms:                     3
% 1.45/0.98  num_of_reused_defs:                     0
% 1.45/0.98  num_eq_ax_congr_red:                    4
% 1.45/0.98  num_of_sem_filtered_clauses:            1
% 1.45/0.98  num_of_subtypes:                        0
% 1.45/0.98  monotx_restored_types:                  0
% 1.45/0.98  sat_num_of_epr_types:                   0
% 1.45/0.98  sat_num_of_non_cyclic_types:            0
% 1.45/0.98  sat_guarded_non_collapsed_types:        0
% 1.45/0.98  num_pure_diseq_elim:                    0
% 1.45/0.98  simp_replaced_by:                       0
% 1.45/0.98  res_preprocessed:                       112
% 1.45/0.98  prep_upred:                             0
% 1.45/0.98  prep_unflattend:                        45
% 1.45/0.98  smt_new_axioms:                         0
% 1.45/0.98  pred_elim_cands:                        2
% 1.45/0.98  pred_elim:                              7
% 1.45/0.98  pred_elim_cl:                           6
% 1.45/0.98  pred_elim_cycles:                       11
% 1.45/0.98  merged_defs:                            0
% 1.45/0.98  merged_defs_ncl:                        0
% 1.45/0.98  bin_hyper_res:                          0
% 1.45/0.98  prep_cycles:                            5
% 1.45/0.98  pred_elim_time:                         0.011
% 1.45/0.98  splitting_time:                         0.
% 1.45/0.98  sem_filter_time:                        0.
% 1.45/0.98  monotx_time:                            0.
% 1.45/0.98  subtype_inf_time:                       0.
% 1.45/0.98  
% 1.45/0.98  ------ Problem properties
% 1.45/0.98  
% 1.45/0.98  clauses:                                18
% 1.45/0.98  conjectures:                            1
% 1.45/0.98  epr:                                    3
% 1.45/0.98  horn:                                   13
% 1.45/0.98  ground:                                 12
% 1.45/0.98  unary:                                  3
% 1.45/0.98  binary:                                 5
% 1.45/0.98  lits:                                   48
% 1.45/0.98  lits_eq:                                19
% 1.45/0.98  fd_pure:                                0
% 1.45/0.98  fd_pseudo:                              0
% 1.45/0.98  fd_cond:                                0
% 1.45/0.98  fd_pseudo_cond:                         0
% 1.45/0.98  ac_symbols:                             0
% 1.45/0.98  
% 1.45/0.98  ------ Propositional Solver
% 1.45/0.98  
% 1.45/0.98  prop_solver_calls:                      30
% 1.45/0.98  prop_fast_solver_calls:                 803
% 1.45/0.98  smt_solver_calls:                       0
% 1.45/0.98  smt_fast_solver_calls:                  0
% 1.45/0.98  prop_num_of_clauses:                    308
% 1.45/0.98  prop_preprocess_simplified:             2546
% 1.45/0.98  prop_fo_subsumed:                       20
% 1.45/0.98  prop_solver_time:                       0.
% 1.45/0.98  smt_solver_time:                        0.
% 1.45/0.98  smt_fast_solver_time:                   0.
% 1.45/0.98  prop_fast_solver_time:                  0.
% 1.45/0.98  prop_unsat_core_time:                   0.
% 1.45/0.98  
% 1.45/0.98  ------ QBF
% 1.45/0.98  
% 1.45/0.98  qbf_q_res:                              0
% 1.45/0.98  qbf_num_tautologies:                    0
% 1.45/0.98  qbf_prep_cycles:                        0
% 1.45/0.98  
% 1.45/0.98  ------ BMC1
% 1.45/0.98  
% 1.45/0.98  bmc1_current_bound:                     -1
% 1.45/0.98  bmc1_last_solved_bound:                 -1
% 1.45/0.98  bmc1_unsat_core_size:                   -1
% 1.45/0.98  bmc1_unsat_core_parents_size:           -1
% 1.45/0.98  bmc1_merge_next_fun:                    0
% 1.45/0.98  bmc1_unsat_core_clauses_time:           0.
% 1.45/0.98  
% 1.45/0.98  ------ Instantiation
% 1.45/0.98  
% 1.45/0.98  inst_num_of_clauses:                    89
% 1.45/0.98  inst_num_in_passive:                    14
% 1.45/0.98  inst_num_in_active:                     75
% 1.45/0.98  inst_num_in_unprocessed:                0
% 1.45/0.98  inst_num_of_loops:                      90
% 1.45/0.98  inst_num_of_learning_restarts:          0
% 1.45/0.98  inst_num_moves_active_passive:          10
% 1.45/0.98  inst_lit_activity:                      0
% 1.45/0.98  inst_lit_activity_moves:                0
% 1.45/0.98  inst_num_tautologies:                   0
% 1.45/0.98  inst_num_prop_implied:                  0
% 1.45/0.98  inst_num_existing_simplified:           0
% 1.45/0.98  inst_num_eq_res_simplified:             0
% 1.45/0.98  inst_num_child_elim:                    0
% 1.45/0.98  inst_num_of_dismatching_blockings:      28
% 1.45/0.98  inst_num_of_non_proper_insts:           85
% 1.45/0.98  inst_num_of_duplicates:                 0
% 1.45/0.98  inst_inst_num_from_inst_to_res:         0
% 1.45/0.98  inst_dismatching_checking_time:         0.
% 1.45/0.98  
% 1.45/0.98  ------ Resolution
% 1.45/0.98  
% 1.45/0.98  res_num_of_clauses:                     0
% 1.45/0.98  res_num_in_passive:                     0
% 1.45/0.98  res_num_in_active:                      0
% 1.45/0.98  res_num_of_loops:                       117
% 1.45/0.98  res_forward_subset_subsumed:            30
% 1.45/0.98  res_backward_subset_subsumed:           0
% 1.45/0.98  res_forward_subsumed:                   0
% 1.45/0.98  res_backward_subsumed:                  0
% 1.45/0.98  res_forward_subsumption_resolution:     0
% 1.45/0.98  res_backward_subsumption_resolution:    0
% 1.45/0.98  res_clause_to_clause_subsumption:       27
% 1.45/0.98  res_orphan_elimination:                 0
% 1.45/0.98  res_tautology_del:                      30
% 1.45/0.98  res_num_eq_res_simplified:              2
% 1.45/0.98  res_num_sel_changes:                    0
% 1.45/0.98  res_moves_from_active_to_pass:          0
% 1.45/0.98  
% 1.45/0.98  ------ Superposition
% 1.45/0.98  
% 1.45/0.98  sup_time_total:                         0.
% 1.45/0.98  sup_time_generating:                    0.
% 1.45/0.98  sup_time_sim_full:                      0.
% 1.45/0.98  sup_time_sim_immed:                     0.
% 1.45/0.98  
% 1.45/0.98  sup_num_of_clauses:                     17
% 1.45/0.98  sup_num_in_active:                      13
% 1.45/0.98  sup_num_in_passive:                     4
% 1.45/0.98  sup_num_of_loops:                       16
% 1.45/0.98  sup_fw_superposition:                   0
% 1.45/0.98  sup_bw_superposition:                   1
% 1.45/0.98  sup_immediate_simplified:               0
% 1.45/0.98  sup_given_eliminated:                   0
% 1.45/0.98  comparisons_done:                       0
% 1.45/0.98  comparisons_avoided:                    3
% 1.45/0.98  
% 1.45/0.98  ------ Simplifications
% 1.45/0.98  
% 1.45/0.98  
% 1.45/0.98  sim_fw_subset_subsumed:                 0
% 1.45/0.98  sim_bw_subset_subsumed:                 1
% 1.45/0.98  sim_fw_subsumed:                        0
% 1.45/0.98  sim_bw_subsumed:                        0
% 1.45/0.98  sim_fw_subsumption_res:                 2
% 1.45/0.98  sim_bw_subsumption_res:                 0
% 1.45/0.98  sim_tautology_del:                      0
% 1.45/0.98  sim_eq_tautology_del:                   0
% 1.45/0.98  sim_eq_res_simp:                        0
% 1.45/0.98  sim_fw_demodulated:                     0
% 1.45/0.98  sim_bw_demodulated:                     2
% 1.45/0.98  sim_light_normalised:                   1
% 1.45/0.98  sim_joinable_taut:                      0
% 1.45/0.98  sim_joinable_simp:                      0
% 1.45/0.98  sim_ac_normalised:                      0
% 1.45/0.98  sim_smt_subsumption:                    0
% 1.45/0.98  
%------------------------------------------------------------------------------
