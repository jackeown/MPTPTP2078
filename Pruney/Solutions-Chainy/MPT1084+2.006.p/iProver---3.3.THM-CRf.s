%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:32 EST 2020

% Result     : Theorem 1.29s
% Output     : CNFRefutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 947 expanded)
%              Number of clauses        :   65 ( 244 expanded)
%              Number of leaves         :   13 ( 220 expanded)
%              Depth                    :   26
%              Number of atoms          :  507 (5051 expanded)
%              Number of equality atoms :  175 (1029 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f11])).

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
    inference(flattening,[],[f26])).

fof(f36,plain,(
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

fof(f35,plain,
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

fof(f37,plain,
    ( ~ r2_funct_2(sK1,sK1,sK2,k6_partfun1(sK1))
    & ! [X2] :
        ( k3_funct_2(sK1,sK1,sK2,X2) = X2
        | ~ m1_subset_1(X2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v1_funct_2(sK2,sK1,sK1)
    & v1_funct_1(sK2)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f36,f35])).

fof(f55,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK0(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k6_partfun1(X0) = X1
      | r2_hidden(sK0(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f41,f50])).

fof(f64,plain,(
    ! [X1] :
      ( k6_partfun1(k1_relat_1(X1)) = X1
      | r2_hidden(sK0(k1_relat_1(X1),X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f60])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f18])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    ! [X2] :
      ( k3_funct_2(sK1,sK1,sK2,X2) = X2
      | ~ m1_subset_1(X2,sK1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f24])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f52])).

fof(f58,plain,(
    ~ r2_funct_2(sK1,sK1,sK2,k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k6_partfun1(X0) = X1
      | k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f42,f50])).

fof(f63,plain,(
    ! [X1] :
      ( k6_partfun1(k1_relat_1(X1)) = X1
      | k1_funct_1(X1,sK0(k1_relat_1(X1),X1)) != sK0(k1_relat_1(X1),X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f59])).

cnf(c_17,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_19,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_302,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_19])).

cnf(c_303,plain,
    ( ~ v1_funct_2(X0,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ m1_subset_1(X2,sK1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(sK1,X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(unflattening,[status(thm)],[c_302])).

cnf(c_427,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ m1_subset_1(X2,sK1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(sK1,X1,X0,X2) = k1_funct_1(X0,X2)
    | sK2 != X0
    | sK1 != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_303])).

cnf(c_428,plain,
    ( ~ m1_subset_1(X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k3_funct_2(sK1,sK1,sK2,X0) = k1_funct_1(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_432,plain,
    ( ~ m1_subset_1(X0,sK1)
    | k3_funct_2(sK1,sK1,sK2,X0) = k1_funct_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_428,c_18,c_16])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k6_partfun1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_477,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | k6_partfun1(k1_relat_1(X0)) = X0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_18])).

cnf(c_478,plain,
    ( r2_hidden(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_569,plain,
    ( m1_subset_1(X0,X1)
    | ~ v1_relat_1(sK2)
    | sK0(k1_relat_1(sK2),sK2) != X0
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | k1_relat_1(sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_478])).

cnf(c_570,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(unflattening,[status(thm)],[c_569])).

cnf(c_601,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_570])).

cnf(c_602,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(unflattening,[status(thm)],[c_601])).

cnf(c_604,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_602])).

cnf(c_606,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_602,c_16,c_604])).

cnf(c_697,plain,
    ( k3_funct_2(sK1,sK1,sK2,X0) = k1_funct_1(sK2,X0)
    | sK0(k1_relat_1(sK2),sK2) != X0
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | k1_relat_1(sK2) != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_432,c_606])).

cnf(c_698,plain,
    ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2))
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | k1_relat_1(sK2) != sK1 ),
    inference(unflattening,[status(thm)],[c_697])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_6,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_10,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_226,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_6,c_10])).

cnf(c_230,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_226,c_10,c_6,c_5])).

cnf(c_231,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_230])).

cnf(c_270,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_7,c_231])).

cnf(c_274,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_270,c_10,c_7,c_6,c_5])).

cnf(c_275,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_274])).

cnf(c_323,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_275,c_19])).

cnf(c_324,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_445,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | sK2 != X0
    | sK1 != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_324])).

cnf(c_446,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k1_relat_1(sK2) = sK1 ),
    inference(unflattening,[status(thm)],[c_445])).

cnf(c_699,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = sK2
    | k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_698,c_18,c_16,c_446])).

cnf(c_700,plain,
    ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2))
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(renaming,[status(thm)],[c_699])).

cnf(c_448,plain,
    ( k1_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_446,c_18,c_16])).

cnf(c_15,negated_conjecture,
    ( ~ m1_subset_1(X0,sK1)
    | k3_funct_2(sK1,sK1,sK2,X0) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_707,plain,
    ( k3_funct_2(sK1,sK1,sK2,X0) = X0
    | sK0(k1_relat_1(sK2),sK2) != X0
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | k1_relat_1(sK2) != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_606])).

cnf(c_708,plain,
    ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | k1_relat_1(sK2) != sK1 ),
    inference(unflattening,[status(thm)],[c_707])).

cnf(c_709,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = sK2
    | k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_708,c_18,c_16,c_446])).

cnf(c_710,plain,
    ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(renaming,[status(thm)],[c_709])).

cnf(c_1073,plain,
    ( k3_funct_2(sK1,sK1,sK2,sK0(sK1,sK2)) = sK0(sK1,sK2)
    | k6_partfun1(sK1) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_710,c_448])).

cnf(c_12,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_14,negated_conjecture,
    ( ~ r2_funct_2(sK1,sK1,sK2,k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_406,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k6_partfun1(sK1) != X0
    | sK2 != X0
    | sK1 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_14])).

cnf(c_407,plain,
    ( ~ v1_funct_2(k6_partfun1(sK1),sK1,sK1)
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(k6_partfun1(sK1))
    | sK2 != k6_partfun1(sK1) ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_453,plain,
    ( ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(k6_partfun1(sK1))
    | k6_partfun1(sK1) != sK2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_407])).

cnf(c_534,plain,
    ( ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) != sK2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_453])).

cnf(c_717,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | k6_partfun1(sK1) != sK2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_534])).

cnf(c_806,plain,
    ( k6_partfun1(sK1) != sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_717])).

cnf(c_1076,plain,
    ( k3_funct_2(sK1,sK1,sK2,sK0(sK1,sK2)) = sK0(sK1,sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1073,c_806])).

cnf(c_1078,plain,
    ( k1_funct_1(sK2,sK0(sK1,sK2)) = sK0(sK1,sK2)
    | k6_partfun1(sK1) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_700,c_448,c_1076])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK0(k1_relat_1(X0),X0)) != sK0(k1_relat_1(X0),X0)
    | k6_partfun1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_490,plain,
    ( ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK0(k1_relat_1(X0),X0)) != sK0(k1_relat_1(X0),X0)
    | k6_partfun1(k1_relat_1(X0)) = X0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_18])).

cnf(c_491,plain,
    ( ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_617,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_491])).

cnf(c_618,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(unflattening,[status(thm)],[c_617])).

cnf(c_620,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_618])).

cnf(c_622,plain,
    ( k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_618,c_16,c_620])).

cnf(c_1062,plain,
    ( k1_funct_1(sK2,sK0(sK1,sK2)) != sK0(sK1,sK2)
    | k6_partfun1(sK1) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_622,c_448])).

cnf(c_1065,plain,
    ( k1_funct_1(sK2,sK0(sK1,sK2)) != sK0(sK1,sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1062,c_806])).

cnf(c_1081,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1078,c_806,c_1065])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:19:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.29/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.29/0.99  
% 1.29/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.29/0.99  
% 1.29/0.99  ------  iProver source info
% 1.29/0.99  
% 1.29/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.29/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.29/0.99  git: non_committed_changes: false
% 1.29/0.99  git: last_make_outside_of_git: false
% 1.29/0.99  
% 1.29/0.99  ------ 
% 1.29/0.99  
% 1.29/0.99  ------ Input Options
% 1.29/0.99  
% 1.29/0.99  --out_options                           all
% 1.29/0.99  --tptp_safe_out                         true
% 1.29/0.99  --problem_path                          ""
% 1.29/0.99  --include_path                          ""
% 1.29/0.99  --clausifier                            res/vclausify_rel
% 1.29/0.99  --clausifier_options                    --mode clausify
% 1.29/0.99  --stdin                                 false
% 1.29/0.99  --stats_out                             all
% 1.29/0.99  
% 1.29/0.99  ------ General Options
% 1.29/0.99  
% 1.29/0.99  --fof                                   false
% 1.29/0.99  --time_out_real                         305.
% 1.29/0.99  --time_out_virtual                      -1.
% 1.29/0.99  --symbol_type_check                     false
% 1.29/0.99  --clausify_out                          false
% 1.29/0.99  --sig_cnt_out                           false
% 1.29/0.99  --trig_cnt_out                          false
% 1.29/0.99  --trig_cnt_out_tolerance                1.
% 1.29/0.99  --trig_cnt_out_sk_spl                   false
% 1.29/0.99  --abstr_cl_out                          false
% 1.29/0.99  
% 1.29/0.99  ------ Global Options
% 1.29/0.99  
% 1.29/0.99  --schedule                              default
% 1.29/0.99  --add_important_lit                     false
% 1.29/0.99  --prop_solver_per_cl                    1000
% 1.29/0.99  --min_unsat_core                        false
% 1.29/0.99  --soft_assumptions                      false
% 1.29/0.99  --soft_lemma_size                       3
% 1.29/0.99  --prop_impl_unit_size                   0
% 1.29/0.99  --prop_impl_unit                        []
% 1.29/0.99  --share_sel_clauses                     true
% 1.29/0.99  --reset_solvers                         false
% 1.29/0.99  --bc_imp_inh                            [conj_cone]
% 1.29/0.99  --conj_cone_tolerance                   3.
% 1.29/0.99  --extra_neg_conj                        none
% 1.29/0.99  --large_theory_mode                     true
% 1.29/0.99  --prolific_symb_bound                   200
% 1.29/0.99  --lt_threshold                          2000
% 1.29/0.99  --clause_weak_htbl                      true
% 1.29/0.99  --gc_record_bc_elim                     false
% 1.29/0.99  
% 1.29/0.99  ------ Preprocessing Options
% 1.29/0.99  
% 1.29/0.99  --preprocessing_flag                    true
% 1.29/0.99  --time_out_prep_mult                    0.1
% 1.29/0.99  --splitting_mode                        input
% 1.29/0.99  --splitting_grd                         true
% 1.29/0.99  --splitting_cvd                         false
% 1.29/0.99  --splitting_cvd_svl                     false
% 1.29/0.99  --splitting_nvd                         32
% 1.29/0.99  --sub_typing                            true
% 1.29/0.99  --prep_gs_sim                           true
% 1.29/0.99  --prep_unflatten                        true
% 1.29/0.99  --prep_res_sim                          true
% 1.29/0.99  --prep_upred                            true
% 1.29/0.99  --prep_sem_filter                       exhaustive
% 1.29/0.99  --prep_sem_filter_out                   false
% 1.29/0.99  --pred_elim                             true
% 1.29/0.99  --res_sim_input                         true
% 1.29/0.99  --eq_ax_congr_red                       true
% 1.29/0.99  --pure_diseq_elim                       true
% 1.29/0.99  --brand_transform                       false
% 1.29/0.99  --non_eq_to_eq                          false
% 1.29/0.99  --prep_def_merge                        true
% 1.29/0.99  --prep_def_merge_prop_impl              false
% 1.29/0.99  --prep_def_merge_mbd                    true
% 1.29/0.99  --prep_def_merge_tr_red                 false
% 1.29/0.99  --prep_def_merge_tr_cl                  false
% 1.29/0.99  --smt_preprocessing                     true
% 1.29/0.99  --smt_ac_axioms                         fast
% 1.29/0.99  --preprocessed_out                      false
% 1.29/0.99  --preprocessed_stats                    false
% 1.29/0.99  
% 1.29/0.99  ------ Abstraction refinement Options
% 1.29/0.99  
% 1.29/0.99  --abstr_ref                             []
% 1.29/0.99  --abstr_ref_prep                        false
% 1.29/0.99  --abstr_ref_until_sat                   false
% 1.29/0.99  --abstr_ref_sig_restrict                funpre
% 1.29/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.29/0.99  --abstr_ref_under                       []
% 1.29/0.99  
% 1.29/0.99  ------ SAT Options
% 1.29/0.99  
% 1.29/0.99  --sat_mode                              false
% 1.29/0.99  --sat_fm_restart_options                ""
% 1.29/0.99  --sat_gr_def                            false
% 1.29/0.99  --sat_epr_types                         true
% 1.29/0.99  --sat_non_cyclic_types                  false
% 1.29/0.99  --sat_finite_models                     false
% 1.29/0.99  --sat_fm_lemmas                         false
% 1.29/0.99  --sat_fm_prep                           false
% 1.29/1.00  --sat_fm_uc_incr                        true
% 1.29/1.00  --sat_out_model                         small
% 1.29/1.00  --sat_out_clauses                       false
% 1.29/1.00  
% 1.29/1.00  ------ QBF Options
% 1.29/1.00  
% 1.29/1.00  --qbf_mode                              false
% 1.29/1.00  --qbf_elim_univ                         false
% 1.29/1.00  --qbf_dom_inst                          none
% 1.29/1.00  --qbf_dom_pre_inst                      false
% 1.29/1.00  --qbf_sk_in                             false
% 1.29/1.00  --qbf_pred_elim                         true
% 1.29/1.00  --qbf_split                             512
% 1.29/1.00  
% 1.29/1.00  ------ BMC1 Options
% 1.29/1.00  
% 1.29/1.00  --bmc1_incremental                      false
% 1.29/1.00  --bmc1_axioms                           reachable_all
% 1.29/1.00  --bmc1_min_bound                        0
% 1.29/1.00  --bmc1_max_bound                        -1
% 1.29/1.00  --bmc1_max_bound_default                -1
% 1.29/1.00  --bmc1_symbol_reachability              true
% 1.29/1.00  --bmc1_property_lemmas                  false
% 1.29/1.00  --bmc1_k_induction                      false
% 1.29/1.00  --bmc1_non_equiv_states                 false
% 1.29/1.00  --bmc1_deadlock                         false
% 1.29/1.00  --bmc1_ucm                              false
% 1.29/1.00  --bmc1_add_unsat_core                   none
% 1.29/1.00  --bmc1_unsat_core_children              false
% 1.29/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.29/1.00  --bmc1_out_stat                         full
% 1.29/1.00  --bmc1_ground_init                      false
% 1.29/1.00  --bmc1_pre_inst_next_state              false
% 1.29/1.00  --bmc1_pre_inst_state                   false
% 1.29/1.00  --bmc1_pre_inst_reach_state             false
% 1.29/1.00  --bmc1_out_unsat_core                   false
% 1.29/1.00  --bmc1_aig_witness_out                  false
% 1.29/1.00  --bmc1_verbose                          false
% 1.29/1.00  --bmc1_dump_clauses_tptp                false
% 1.29/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.29/1.00  --bmc1_dump_file                        -
% 1.29/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.29/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.29/1.00  --bmc1_ucm_extend_mode                  1
% 1.29/1.00  --bmc1_ucm_init_mode                    2
% 1.29/1.00  --bmc1_ucm_cone_mode                    none
% 1.29/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.29/1.00  --bmc1_ucm_relax_model                  4
% 1.29/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.29/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.29/1.00  --bmc1_ucm_layered_model                none
% 1.29/1.00  --bmc1_ucm_max_lemma_size               10
% 1.29/1.00  
% 1.29/1.00  ------ AIG Options
% 1.29/1.00  
% 1.29/1.00  --aig_mode                              false
% 1.29/1.00  
% 1.29/1.00  ------ Instantiation Options
% 1.29/1.00  
% 1.29/1.00  --instantiation_flag                    true
% 1.29/1.00  --inst_sos_flag                         false
% 1.29/1.00  --inst_sos_phase                        true
% 1.29/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.29/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.29/1.00  --inst_lit_sel_side                     num_symb
% 1.29/1.00  --inst_solver_per_active                1400
% 1.29/1.00  --inst_solver_calls_frac                1.
% 1.29/1.00  --inst_passive_queue_type               priority_queues
% 1.29/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.29/1.00  --inst_passive_queues_freq              [25;2]
% 1.29/1.00  --inst_dismatching                      true
% 1.29/1.00  --inst_eager_unprocessed_to_passive     true
% 1.29/1.00  --inst_prop_sim_given                   true
% 1.29/1.00  --inst_prop_sim_new                     false
% 1.29/1.00  --inst_subs_new                         false
% 1.29/1.00  --inst_eq_res_simp                      false
% 1.29/1.00  --inst_subs_given                       false
% 1.29/1.00  --inst_orphan_elimination               true
% 1.29/1.00  --inst_learning_loop_flag               true
% 1.29/1.00  --inst_learning_start                   3000
% 1.29/1.00  --inst_learning_factor                  2
% 1.29/1.00  --inst_start_prop_sim_after_learn       3
% 1.29/1.00  --inst_sel_renew                        solver
% 1.29/1.00  --inst_lit_activity_flag                true
% 1.29/1.00  --inst_restr_to_given                   false
% 1.29/1.00  --inst_activity_threshold               500
% 1.29/1.00  --inst_out_proof                        true
% 1.29/1.00  
% 1.29/1.00  ------ Resolution Options
% 1.29/1.00  
% 1.29/1.00  --resolution_flag                       true
% 1.29/1.00  --res_lit_sel                           adaptive
% 1.29/1.00  --res_lit_sel_side                      none
% 1.29/1.00  --res_ordering                          kbo
% 1.29/1.00  --res_to_prop_solver                    active
% 1.29/1.00  --res_prop_simpl_new                    false
% 1.29/1.00  --res_prop_simpl_given                  true
% 1.29/1.00  --res_passive_queue_type                priority_queues
% 1.29/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.29/1.00  --res_passive_queues_freq               [15;5]
% 1.29/1.00  --res_forward_subs                      full
% 1.29/1.00  --res_backward_subs                     full
% 1.29/1.00  --res_forward_subs_resolution           true
% 1.29/1.00  --res_backward_subs_resolution          true
% 1.29/1.00  --res_orphan_elimination                true
% 1.29/1.00  --res_time_limit                        2.
% 1.29/1.00  --res_out_proof                         true
% 1.29/1.00  
% 1.29/1.00  ------ Superposition Options
% 1.29/1.00  
% 1.29/1.00  --superposition_flag                    true
% 1.29/1.00  --sup_passive_queue_type                priority_queues
% 1.29/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.29/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.29/1.00  --demod_completeness_check              fast
% 1.29/1.00  --demod_use_ground                      true
% 1.29/1.00  --sup_to_prop_solver                    passive
% 1.29/1.00  --sup_prop_simpl_new                    true
% 1.29/1.00  --sup_prop_simpl_given                  true
% 1.29/1.00  --sup_fun_splitting                     false
% 1.29/1.00  --sup_smt_interval                      50000
% 1.29/1.00  
% 1.29/1.00  ------ Superposition Simplification Setup
% 1.29/1.00  
% 1.29/1.00  --sup_indices_passive                   []
% 1.29/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.29/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.29/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.29/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.29/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.29/1.00  --sup_full_bw                           [BwDemod]
% 1.29/1.00  --sup_immed_triv                        [TrivRules]
% 1.29/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.29/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.29/1.00  --sup_immed_bw_main                     []
% 1.29/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.29/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.29/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.29/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.29/1.00  
% 1.29/1.00  ------ Combination Options
% 1.29/1.00  
% 1.29/1.00  --comb_res_mult                         3
% 1.29/1.00  --comb_sup_mult                         2
% 1.29/1.00  --comb_inst_mult                        10
% 1.29/1.00  
% 1.29/1.00  ------ Debug Options
% 1.29/1.00  
% 1.29/1.00  --dbg_backtrace                         false
% 1.29/1.00  --dbg_dump_prop_clauses                 false
% 1.29/1.00  --dbg_dump_prop_clauses_file            -
% 1.29/1.00  --dbg_out_stat                          false
% 1.29/1.00  ------ Parsing...
% 1.29/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.29/1.00  
% 1.29/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 1.29/1.00  
% 1.29/1.00  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.29/1.00  
% 1.29/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.29/1.00  ------ Proving...
% 1.29/1.00  ------ Problem Properties 
% 1.29/1.00  
% 1.29/1.00  
% 1.29/1.00  clauses                                 11
% 1.29/1.00  conjectures                             0
% 1.29/1.00  EPR                                     0
% 1.29/1.00  Horn                                    8
% 1.29/1.00  unary                                   2
% 1.29/1.00  binary                                  7
% 1.29/1.00  lits                                    22
% 1.29/1.00  lits eq                                 17
% 1.29/1.00  fd_pure                                 0
% 1.29/1.00  fd_pseudo                               0
% 1.29/1.00  fd_cond                                 0
% 1.29/1.00  fd_pseudo_cond                          0
% 1.29/1.00  AC symbols                              0
% 1.29/1.00  
% 1.29/1.00  ------ Schedule dynamic 5 is on 
% 1.29/1.00  
% 1.29/1.00  ------ no conjectures: strip conj schedule 
% 1.29/1.00  
% 1.29/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 1.29/1.00  
% 1.29/1.00  
% 1.29/1.00  ------ 
% 1.29/1.00  Current options:
% 1.29/1.00  ------ 
% 1.29/1.00  
% 1.29/1.00  ------ Input Options
% 1.29/1.00  
% 1.29/1.00  --out_options                           all
% 1.29/1.00  --tptp_safe_out                         true
% 1.29/1.00  --problem_path                          ""
% 1.29/1.00  --include_path                          ""
% 1.29/1.00  --clausifier                            res/vclausify_rel
% 1.29/1.00  --clausifier_options                    --mode clausify
% 1.29/1.00  --stdin                                 false
% 1.29/1.00  --stats_out                             all
% 1.29/1.00  
% 1.29/1.00  ------ General Options
% 1.29/1.00  
% 1.29/1.00  --fof                                   false
% 1.29/1.00  --time_out_real                         305.
% 1.29/1.00  --time_out_virtual                      -1.
% 1.29/1.00  --symbol_type_check                     false
% 1.29/1.00  --clausify_out                          false
% 1.29/1.00  --sig_cnt_out                           false
% 1.29/1.00  --trig_cnt_out                          false
% 1.29/1.00  --trig_cnt_out_tolerance                1.
% 1.29/1.00  --trig_cnt_out_sk_spl                   false
% 1.29/1.00  --abstr_cl_out                          false
% 1.29/1.00  
% 1.29/1.00  ------ Global Options
% 1.29/1.00  
% 1.29/1.00  --schedule                              default
% 1.29/1.00  --add_important_lit                     false
% 1.29/1.00  --prop_solver_per_cl                    1000
% 1.29/1.00  --min_unsat_core                        false
% 1.29/1.00  --soft_assumptions                      false
% 1.29/1.00  --soft_lemma_size                       3
% 1.29/1.00  --prop_impl_unit_size                   0
% 1.29/1.00  --prop_impl_unit                        []
% 1.29/1.00  --share_sel_clauses                     true
% 1.29/1.00  --reset_solvers                         false
% 1.29/1.00  --bc_imp_inh                            [conj_cone]
% 1.29/1.00  --conj_cone_tolerance                   3.
% 1.29/1.00  --extra_neg_conj                        none
% 1.29/1.00  --large_theory_mode                     true
% 1.29/1.00  --prolific_symb_bound                   200
% 1.29/1.00  --lt_threshold                          2000
% 1.29/1.00  --clause_weak_htbl                      true
% 1.29/1.00  --gc_record_bc_elim                     false
% 1.29/1.00  
% 1.29/1.00  ------ Preprocessing Options
% 1.29/1.00  
% 1.29/1.00  --preprocessing_flag                    true
% 1.29/1.00  --time_out_prep_mult                    0.1
% 1.29/1.00  --splitting_mode                        input
% 1.29/1.00  --splitting_grd                         true
% 1.29/1.00  --splitting_cvd                         false
% 1.29/1.00  --splitting_cvd_svl                     false
% 1.29/1.00  --splitting_nvd                         32
% 1.29/1.00  --sub_typing                            true
% 1.29/1.00  --prep_gs_sim                           true
% 1.29/1.00  --prep_unflatten                        true
% 1.29/1.00  --prep_res_sim                          true
% 1.29/1.00  --prep_upred                            true
% 1.29/1.00  --prep_sem_filter                       exhaustive
% 1.29/1.00  --prep_sem_filter_out                   false
% 1.29/1.00  --pred_elim                             true
% 1.29/1.00  --res_sim_input                         true
% 1.29/1.00  --eq_ax_congr_red                       true
% 1.29/1.00  --pure_diseq_elim                       true
% 1.29/1.00  --brand_transform                       false
% 1.29/1.00  --non_eq_to_eq                          false
% 1.29/1.00  --prep_def_merge                        true
% 1.29/1.00  --prep_def_merge_prop_impl              false
% 1.29/1.00  --prep_def_merge_mbd                    true
% 1.29/1.00  --prep_def_merge_tr_red                 false
% 1.29/1.00  --prep_def_merge_tr_cl                  false
% 1.29/1.00  --smt_preprocessing                     true
% 1.29/1.00  --smt_ac_axioms                         fast
% 1.29/1.00  --preprocessed_out                      false
% 1.29/1.00  --preprocessed_stats                    false
% 1.29/1.00  
% 1.29/1.00  ------ Abstraction refinement Options
% 1.29/1.00  
% 1.29/1.00  --abstr_ref                             []
% 1.29/1.00  --abstr_ref_prep                        false
% 1.29/1.00  --abstr_ref_until_sat                   false
% 1.29/1.00  --abstr_ref_sig_restrict                funpre
% 1.29/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.29/1.00  --abstr_ref_under                       []
% 1.29/1.00  
% 1.29/1.00  ------ SAT Options
% 1.29/1.00  
% 1.29/1.00  --sat_mode                              false
% 1.29/1.00  --sat_fm_restart_options                ""
% 1.29/1.00  --sat_gr_def                            false
% 1.29/1.00  --sat_epr_types                         true
% 1.29/1.00  --sat_non_cyclic_types                  false
% 1.29/1.00  --sat_finite_models                     false
% 1.29/1.00  --sat_fm_lemmas                         false
% 1.29/1.00  --sat_fm_prep                           false
% 1.29/1.00  --sat_fm_uc_incr                        true
% 1.29/1.00  --sat_out_model                         small
% 1.29/1.00  --sat_out_clauses                       false
% 1.29/1.00  
% 1.29/1.00  ------ QBF Options
% 1.29/1.00  
% 1.29/1.00  --qbf_mode                              false
% 1.29/1.00  --qbf_elim_univ                         false
% 1.29/1.00  --qbf_dom_inst                          none
% 1.29/1.00  --qbf_dom_pre_inst                      false
% 1.29/1.00  --qbf_sk_in                             false
% 1.29/1.00  --qbf_pred_elim                         true
% 1.29/1.00  --qbf_split                             512
% 1.29/1.00  
% 1.29/1.00  ------ BMC1 Options
% 1.29/1.00  
% 1.29/1.00  --bmc1_incremental                      false
% 1.29/1.00  --bmc1_axioms                           reachable_all
% 1.29/1.00  --bmc1_min_bound                        0
% 1.29/1.00  --bmc1_max_bound                        -1
% 1.29/1.00  --bmc1_max_bound_default                -1
% 1.29/1.00  --bmc1_symbol_reachability              true
% 1.29/1.00  --bmc1_property_lemmas                  false
% 1.29/1.00  --bmc1_k_induction                      false
% 1.29/1.00  --bmc1_non_equiv_states                 false
% 1.29/1.00  --bmc1_deadlock                         false
% 1.29/1.00  --bmc1_ucm                              false
% 1.29/1.00  --bmc1_add_unsat_core                   none
% 1.29/1.00  --bmc1_unsat_core_children              false
% 1.29/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.29/1.00  --bmc1_out_stat                         full
% 1.29/1.00  --bmc1_ground_init                      false
% 1.29/1.00  --bmc1_pre_inst_next_state              false
% 1.29/1.00  --bmc1_pre_inst_state                   false
% 1.29/1.00  --bmc1_pre_inst_reach_state             false
% 1.29/1.00  --bmc1_out_unsat_core                   false
% 1.29/1.00  --bmc1_aig_witness_out                  false
% 1.29/1.00  --bmc1_verbose                          false
% 1.29/1.00  --bmc1_dump_clauses_tptp                false
% 1.29/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.29/1.00  --bmc1_dump_file                        -
% 1.29/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.29/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.29/1.00  --bmc1_ucm_extend_mode                  1
% 1.29/1.00  --bmc1_ucm_init_mode                    2
% 1.29/1.00  --bmc1_ucm_cone_mode                    none
% 1.29/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.29/1.00  --bmc1_ucm_relax_model                  4
% 1.29/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.29/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.29/1.00  --bmc1_ucm_layered_model                none
% 1.29/1.00  --bmc1_ucm_max_lemma_size               10
% 1.29/1.00  
% 1.29/1.00  ------ AIG Options
% 1.29/1.00  
% 1.29/1.00  --aig_mode                              false
% 1.29/1.00  
% 1.29/1.00  ------ Instantiation Options
% 1.29/1.00  
% 1.29/1.00  --instantiation_flag                    true
% 1.29/1.00  --inst_sos_flag                         false
% 1.29/1.00  --inst_sos_phase                        true
% 1.29/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.29/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.29/1.00  --inst_lit_sel_side                     none
% 1.29/1.00  --inst_solver_per_active                1400
% 1.29/1.00  --inst_solver_calls_frac                1.
% 1.29/1.00  --inst_passive_queue_type               priority_queues
% 1.29/1.00  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 1.29/1.00  --inst_passive_queues_freq              [25;2]
% 1.29/1.00  --inst_dismatching                      true
% 1.29/1.00  --inst_eager_unprocessed_to_passive     true
% 1.29/1.00  --inst_prop_sim_given                   true
% 1.29/1.00  --inst_prop_sim_new                     false
% 1.29/1.00  --inst_subs_new                         false
% 1.29/1.00  --inst_eq_res_simp                      false
% 1.29/1.00  --inst_subs_given                       false
% 1.29/1.00  --inst_orphan_elimination               true
% 1.29/1.00  --inst_learning_loop_flag               true
% 1.29/1.00  --inst_learning_start                   3000
% 1.29/1.00  --inst_learning_factor                  2
% 1.29/1.00  --inst_start_prop_sim_after_learn       3
% 1.29/1.00  --inst_sel_renew                        solver
% 1.29/1.00  --inst_lit_activity_flag                true
% 1.29/1.00  --inst_restr_to_given                   false
% 1.29/1.00  --inst_activity_threshold               500
% 1.29/1.00  --inst_out_proof                        true
% 1.29/1.00  
% 1.29/1.00  ------ Resolution Options
% 1.29/1.00  
% 1.29/1.00  --resolution_flag                       false
% 1.29/1.00  --res_lit_sel                           adaptive
% 1.29/1.00  --res_lit_sel_side                      none
% 1.29/1.00  --res_ordering                          kbo
% 1.29/1.00  --res_to_prop_solver                    active
% 1.29/1.00  --res_prop_simpl_new                    false
% 1.29/1.00  --res_prop_simpl_given                  true
% 1.29/1.00  --res_passive_queue_type                priority_queues
% 1.29/1.00  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 1.29/1.00  --res_passive_queues_freq               [15;5]
% 1.29/1.00  --res_forward_subs                      full
% 1.29/1.00  --res_backward_subs                     full
% 1.29/1.00  --res_forward_subs_resolution           true
% 1.29/1.00  --res_backward_subs_resolution          true
% 1.29/1.00  --res_orphan_elimination                true
% 1.29/1.00  --res_time_limit                        2.
% 1.29/1.00  --res_out_proof                         true
% 1.29/1.00  
% 1.29/1.00  ------ Superposition Options
% 1.29/1.00  
% 1.29/1.00  --superposition_flag                    true
% 1.29/1.00  --sup_passive_queue_type                priority_queues
% 1.29/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.29/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.29/1.00  --demod_completeness_check              fast
% 1.29/1.00  --demod_use_ground                      true
% 1.29/1.00  --sup_to_prop_solver                    passive
% 1.29/1.00  --sup_prop_simpl_new                    true
% 1.29/1.00  --sup_prop_simpl_given                  true
% 1.29/1.00  --sup_fun_splitting                     false
% 1.29/1.00  --sup_smt_interval                      50000
% 1.29/1.00  
% 1.29/1.00  ------ Superposition Simplification Setup
% 1.29/1.00  
% 1.29/1.00  --sup_indices_passive                   []
% 1.29/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.29/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.29/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.29/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.29/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.29/1.00  --sup_full_bw                           [BwDemod]
% 1.29/1.00  --sup_immed_triv                        [TrivRules]
% 1.29/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.29/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.29/1.00  --sup_immed_bw_main                     []
% 1.29/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.29/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.29/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.29/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.29/1.00  
% 1.29/1.00  ------ Combination Options
% 1.29/1.00  
% 1.29/1.00  --comb_res_mult                         3
% 1.29/1.00  --comb_sup_mult                         2
% 1.29/1.00  --comb_inst_mult                        10
% 1.29/1.00  
% 1.29/1.00  ------ Debug Options
% 1.29/1.00  
% 1.29/1.00  --dbg_backtrace                         false
% 1.29/1.00  --dbg_dump_prop_clauses                 false
% 1.29/1.00  --dbg_dump_prop_clauses_file            -
% 1.29/1.00  --dbg_out_stat                          false
% 1.29/1.00  
% 1.29/1.00  
% 1.29/1.00  
% 1.29/1.00  
% 1.29/1.00  ------ Proving...
% 1.29/1.00  
% 1.29/1.00  
% 1.29/1.00  % SZS status Theorem for theBenchmark.p
% 1.29/1.00  
% 1.29/1.00   Resolution empty clause
% 1.29/1.00  
% 1.29/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.29/1.00  
% 1.29/1.00  fof(f10,conjecture,(
% 1.29/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (! [X2] : (m1_subset_1(X2,X0) => k3_funct_2(X0,X0,X1,X2) = X2) => r2_funct_2(X0,X0,X1,k6_partfun1(X0)))))),
% 1.29/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.29/1.00  
% 1.29/1.00  fof(f11,negated_conjecture,(
% 1.29/1.00    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (! [X2] : (m1_subset_1(X2,X0) => k3_funct_2(X0,X0,X1,X2) = X2) => r2_funct_2(X0,X0,X1,k6_partfun1(X0)))))),
% 1.29/1.00    inference(negated_conjecture,[],[f10])).
% 1.29/1.00  
% 1.29/1.00  fof(f26,plain,(
% 1.29/1.00    ? [X0] : (? [X1] : ((~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))) & ~v1_xboole_0(X0))),
% 1.29/1.00    inference(ennf_transformation,[],[f11])).
% 1.29/1.00  
% 1.29/1.00  fof(f27,plain,(
% 1.29/1.00    ? [X0] : (? [X1] : (~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0))),
% 1.29/1.00    inference(flattening,[],[f26])).
% 1.29/1.00  
% 1.29/1.00  fof(f36,plain,(
% 1.29/1.00    ( ! [X0] : (? [X1] : (~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (~r2_funct_2(X0,X0,sK2,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,sK2,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 1.29/1.00    introduced(choice_axiom,[])).
% 1.29/1.00  
% 1.29/1.00  fof(f35,plain,(
% 1.29/1.00    ? [X0] : (? [X1] : (~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (~r2_funct_2(sK1,sK1,X1,k6_partfun1(sK1)) & ! [X2] : (k3_funct_2(sK1,sK1,X1,X2) = X2 | ~m1_subset_1(X2,sK1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_2(X1,sK1,sK1) & v1_funct_1(X1)) & ~v1_xboole_0(sK1))),
% 1.29/1.00    introduced(choice_axiom,[])).
% 1.29/1.00  
% 1.29/1.00  fof(f37,plain,(
% 1.29/1.00    (~r2_funct_2(sK1,sK1,sK2,k6_partfun1(sK1)) & ! [X2] : (k3_funct_2(sK1,sK1,sK2,X2) = X2 | ~m1_subset_1(X2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)) & ~v1_xboole_0(sK1)),
% 1.29/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f36,f35])).
% 1.29/1.00  
% 1.29/1.00  fof(f55,plain,(
% 1.29/1.00    v1_funct_2(sK2,sK1,sK1)),
% 1.29/1.00    inference(cnf_transformation,[],[f37])).
% 1.29/1.00  
% 1.29/1.00  fof(f7,axiom,(
% 1.29/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3))),
% 1.29/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.29/1.00  
% 1.29/1.00  fof(f22,plain,(
% 1.29/1.00    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 1.29/1.00    inference(ennf_transformation,[],[f7])).
% 1.29/1.00  
% 1.29/1.00  fof(f23,plain,(
% 1.29/1.00    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 1.29/1.00    inference(flattening,[],[f22])).
% 1.29/1.00  
% 1.29/1.00  fof(f49,plain,(
% 1.29/1.00    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 1.29/1.00    inference(cnf_transformation,[],[f23])).
% 1.29/1.00  
% 1.29/1.00  fof(f53,plain,(
% 1.29/1.00    ~v1_xboole_0(sK1)),
% 1.29/1.00    inference(cnf_transformation,[],[f37])).
% 1.29/1.00  
% 1.29/1.00  fof(f54,plain,(
% 1.29/1.00    v1_funct_1(sK2)),
% 1.29/1.00    inference(cnf_transformation,[],[f37])).
% 1.29/1.00  
% 1.29/1.00  fof(f56,plain,(
% 1.29/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 1.29/1.00    inference(cnf_transformation,[],[f37])).
% 1.29/1.00  
% 1.29/1.00  fof(f3,axiom,(
% 1.29/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.29/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.29/1.00  
% 1.29/1.00  fof(f16,plain,(
% 1.29/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.29/1.00    inference(ennf_transformation,[],[f3])).
% 1.29/1.00  
% 1.29/1.00  fof(f43,plain,(
% 1.29/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.29/1.00    inference(cnf_transformation,[],[f16])).
% 1.29/1.00  
% 1.29/1.00  fof(f1,axiom,(
% 1.29/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.29/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.29/1.00  
% 1.29/1.00  fof(f13,plain,(
% 1.29/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.29/1.00    inference(ennf_transformation,[],[f1])).
% 1.29/1.00  
% 1.29/1.00  fof(f38,plain,(
% 1.29/1.00    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.29/1.00    inference(cnf_transformation,[],[f13])).
% 1.29/1.00  
% 1.29/1.00  fof(f2,axiom,(
% 1.29/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 1.29/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.29/1.00  
% 1.29/1.00  fof(f14,plain,(
% 1.29/1.00    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.29/1.00    inference(ennf_transformation,[],[f2])).
% 1.29/1.00  
% 1.29/1.00  fof(f15,plain,(
% 1.29/1.00    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.29/1.00    inference(flattening,[],[f14])).
% 1.29/1.00  
% 1.29/1.00  fof(f28,plain,(
% 1.29/1.00    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.29/1.00    inference(nnf_transformation,[],[f15])).
% 1.29/1.00  
% 1.29/1.00  fof(f29,plain,(
% 1.29/1.00    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.29/1.00    inference(flattening,[],[f28])).
% 1.29/1.00  
% 1.29/1.00  fof(f30,plain,(
% 1.29/1.00    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.29/1.00    inference(rectify,[],[f29])).
% 1.29/1.00  
% 1.29/1.00  fof(f31,plain,(
% 1.29/1.00    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.29/1.00    introduced(choice_axiom,[])).
% 1.29/1.00  
% 1.29/1.00  fof(f32,plain,(
% 1.29/1.00    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1) & r2_hidden(sK0(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.29/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 1.29/1.00  
% 1.29/1.00  fof(f41,plain,(
% 1.29/1.00    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | r2_hidden(sK0(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.29/1.00    inference(cnf_transformation,[],[f32])).
% 1.29/1.00  
% 1.29/1.00  fof(f8,axiom,(
% 1.29/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.29/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.29/1.00  
% 1.29/1.00  fof(f50,plain,(
% 1.29/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.29/1.00    inference(cnf_transformation,[],[f8])).
% 1.29/1.00  
% 1.29/1.00  fof(f60,plain,(
% 1.29/1.00    ( ! [X0,X1] : (k6_partfun1(X0) = X1 | r2_hidden(sK0(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.29/1.00    inference(definition_unfolding,[],[f41,f50])).
% 1.29/1.00  
% 1.29/1.00  fof(f64,plain,(
% 1.29/1.00    ( ! [X1] : (k6_partfun1(k1_relat_1(X1)) = X1 | r2_hidden(sK0(k1_relat_1(X1),X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.29/1.00    inference(equality_resolution,[],[f60])).
% 1.29/1.00  
% 1.29/1.00  fof(f5,axiom,(
% 1.29/1.00    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.29/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.29/1.00  
% 1.29/1.00  fof(f18,plain,(
% 1.29/1.00    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.29/1.00    inference(ennf_transformation,[],[f5])).
% 1.29/1.00  
% 1.29/1.00  fof(f19,plain,(
% 1.29/1.00    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.29/1.00    inference(flattening,[],[f18])).
% 1.29/1.00  
% 1.29/1.00  fof(f46,plain,(
% 1.29/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 1.29/1.00    inference(cnf_transformation,[],[f19])).
% 1.29/1.00  
% 1.29/1.00  fof(f4,axiom,(
% 1.29/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.29/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.29/1.00  
% 1.29/1.00  fof(f12,plain,(
% 1.29/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.29/1.00    inference(pure_predicate_removal,[],[f4])).
% 1.29/1.00  
% 1.29/1.00  fof(f17,plain,(
% 1.29/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.29/1.00    inference(ennf_transformation,[],[f12])).
% 1.29/1.00  
% 1.29/1.00  fof(f44,plain,(
% 1.29/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.29/1.00    inference(cnf_transformation,[],[f17])).
% 1.29/1.00  
% 1.29/1.00  fof(f6,axiom,(
% 1.29/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.29/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.29/1.00  
% 1.29/1.00  fof(f20,plain,(
% 1.29/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.29/1.00    inference(ennf_transformation,[],[f6])).
% 1.29/1.00  
% 1.29/1.00  fof(f21,plain,(
% 1.29/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.29/1.00    inference(flattening,[],[f20])).
% 1.29/1.00  
% 1.29/1.00  fof(f33,plain,(
% 1.29/1.00    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.29/1.00    inference(nnf_transformation,[],[f21])).
% 1.29/1.00  
% 1.29/1.00  fof(f47,plain,(
% 1.29/1.00    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.29/1.00    inference(cnf_transformation,[],[f33])).
% 1.29/1.00  
% 1.29/1.00  fof(f57,plain,(
% 1.29/1.00    ( ! [X2] : (k3_funct_2(sK1,sK1,sK2,X2) = X2 | ~m1_subset_1(X2,sK1)) )),
% 1.29/1.00    inference(cnf_transformation,[],[f37])).
% 1.29/1.00  
% 1.29/1.00  fof(f9,axiom,(
% 1.29/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.29/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.29/1.00  
% 1.29/1.00  fof(f24,plain,(
% 1.29/1.00    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.29/1.00    inference(ennf_transformation,[],[f9])).
% 1.29/1.00  
% 1.29/1.00  fof(f25,plain,(
% 1.29/1.00    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.29/1.00    inference(flattening,[],[f24])).
% 1.29/1.00  
% 1.29/1.00  fof(f34,plain,(
% 1.29/1.00    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.29/1.00    inference(nnf_transformation,[],[f25])).
% 1.29/1.00  
% 1.29/1.00  fof(f52,plain,(
% 1.29/1.00    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.29/1.00    inference(cnf_transformation,[],[f34])).
% 1.29/1.00  
% 1.29/1.00  fof(f68,plain,(
% 1.29/1.00    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.29/1.00    inference(equality_resolution,[],[f52])).
% 1.29/1.00  
% 1.29/1.00  fof(f58,plain,(
% 1.29/1.00    ~r2_funct_2(sK1,sK1,sK2,k6_partfun1(sK1))),
% 1.29/1.00    inference(cnf_transformation,[],[f37])).
% 1.29/1.00  
% 1.29/1.00  fof(f42,plain,(
% 1.29/1.00    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.29/1.00    inference(cnf_transformation,[],[f32])).
% 1.29/1.00  
% 1.29/1.00  fof(f59,plain,(
% 1.29/1.00    ( ! [X0,X1] : (k6_partfun1(X0) = X1 | k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.29/1.00    inference(definition_unfolding,[],[f42,f50])).
% 1.29/1.00  
% 1.29/1.00  fof(f63,plain,(
% 1.29/1.00    ( ! [X1] : (k6_partfun1(k1_relat_1(X1)) = X1 | k1_funct_1(X1,sK0(k1_relat_1(X1),X1)) != sK0(k1_relat_1(X1),X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.29/1.00    inference(equality_resolution,[],[f59])).
% 1.29/1.00  
% 1.29/1.00  cnf(c_17,negated_conjecture,
% 1.29/1.00      ( v1_funct_2(sK2,sK1,sK1) ),
% 1.29/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_11,plain,
% 1.29/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 1.29/1.00      | ~ m1_subset_1(X3,X1)
% 1.29/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.29/1.00      | v1_xboole_0(X1)
% 1.29/1.00      | ~ v1_funct_1(X0)
% 1.29/1.00      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 1.29/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_19,negated_conjecture,
% 1.29/1.00      ( ~ v1_xboole_0(sK1) ),
% 1.29/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_302,plain,
% 1.29/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 1.29/1.00      | ~ m1_subset_1(X3,X1)
% 1.29/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.29/1.00      | ~ v1_funct_1(X0)
% 1.29/1.00      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
% 1.29/1.00      | sK1 != X1 ),
% 1.29/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_19]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_303,plain,
% 1.29/1.00      ( ~ v1_funct_2(X0,sK1,X1)
% 1.29/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 1.29/1.00      | ~ m1_subset_1(X2,sK1)
% 1.29/1.00      | ~ v1_funct_1(X0)
% 1.29/1.00      | k3_funct_2(sK1,X1,X0,X2) = k1_funct_1(X0,X2) ),
% 1.29/1.00      inference(unflattening,[status(thm)],[c_302]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_427,plain,
% 1.29/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 1.29/1.00      | ~ m1_subset_1(X2,sK1)
% 1.29/1.00      | ~ v1_funct_1(X0)
% 1.29/1.00      | k3_funct_2(sK1,X1,X0,X2) = k1_funct_1(X0,X2)
% 1.29/1.00      | sK2 != X0
% 1.29/1.00      | sK1 != X1
% 1.29/1.00      | sK1 != sK1 ),
% 1.29/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_303]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_428,plain,
% 1.29/1.00      ( ~ m1_subset_1(X0,sK1)
% 1.29/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.29/1.00      | ~ v1_funct_1(sK2)
% 1.29/1.00      | k3_funct_2(sK1,sK1,sK2,X0) = k1_funct_1(sK2,X0) ),
% 1.29/1.00      inference(unflattening,[status(thm)],[c_427]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_18,negated_conjecture,
% 1.29/1.00      ( v1_funct_1(sK2) ),
% 1.29/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_16,negated_conjecture,
% 1.29/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 1.29/1.00      inference(cnf_transformation,[],[f56]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_432,plain,
% 1.29/1.00      ( ~ m1_subset_1(X0,sK1)
% 1.29/1.00      | k3_funct_2(sK1,sK1,sK2,X0) = k1_funct_1(sK2,X0) ),
% 1.29/1.00      inference(global_propositional_subsumption,
% 1.29/1.00                [status(thm)],
% 1.29/1.00                [c_428,c_18,c_16]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_5,plain,
% 1.29/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 1.29/1.00      inference(cnf_transformation,[],[f43]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_0,plain,
% 1.29/1.00      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 1.29/1.00      inference(cnf_transformation,[],[f38]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_2,plain,
% 1.29/1.00      ( r2_hidden(sK0(k1_relat_1(X0),X0),k1_relat_1(X0))
% 1.29/1.00      | ~ v1_relat_1(X0)
% 1.29/1.00      | ~ v1_funct_1(X0)
% 1.29/1.00      | k6_partfun1(k1_relat_1(X0)) = X0 ),
% 1.29/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_477,plain,
% 1.29/1.00      ( r2_hidden(sK0(k1_relat_1(X0),X0),k1_relat_1(X0))
% 1.29/1.00      | ~ v1_relat_1(X0)
% 1.29/1.00      | k6_partfun1(k1_relat_1(X0)) = X0
% 1.29/1.00      | sK2 != X0 ),
% 1.29/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_18]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_478,plain,
% 1.29/1.00      ( r2_hidden(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
% 1.29/1.00      | ~ v1_relat_1(sK2)
% 1.29/1.00      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.29/1.00      inference(unflattening,[status(thm)],[c_477]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_569,plain,
% 1.29/1.00      ( m1_subset_1(X0,X1)
% 1.29/1.00      | ~ v1_relat_1(sK2)
% 1.29/1.00      | sK0(k1_relat_1(sK2),sK2) != X0
% 1.29/1.00      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.29/1.00      | k1_relat_1(sK2) != X1 ),
% 1.29/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_478]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_570,plain,
% 1.29/1.00      ( m1_subset_1(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
% 1.29/1.00      | ~ v1_relat_1(sK2)
% 1.29/1.00      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.29/1.00      inference(unflattening,[status(thm)],[c_569]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_601,plain,
% 1.29/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.29/1.00      | m1_subset_1(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
% 1.29/1.00      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.29/1.00      | sK2 != X0 ),
% 1.29/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_570]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_602,plain,
% 1.29/1.00      ( m1_subset_1(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
% 1.29/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.29/1.00      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.29/1.00      inference(unflattening,[status(thm)],[c_601]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_604,plain,
% 1.29/1.00      ( m1_subset_1(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
% 1.29/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.29/1.00      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.29/1.00      inference(instantiation,[status(thm)],[c_602]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_606,plain,
% 1.29/1.00      ( m1_subset_1(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
% 1.29/1.00      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.29/1.00      inference(global_propositional_subsumption,
% 1.29/1.00                [status(thm)],
% 1.29/1.00                [c_602,c_16,c_604]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_697,plain,
% 1.29/1.00      ( k3_funct_2(sK1,sK1,sK2,X0) = k1_funct_1(sK2,X0)
% 1.29/1.00      | sK0(k1_relat_1(sK2),sK2) != X0
% 1.29/1.00      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.29/1.00      | k1_relat_1(sK2) != sK1 ),
% 1.29/1.00      inference(resolution_lifted,[status(thm)],[c_432,c_606]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_698,plain,
% 1.29/1.00      ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2))
% 1.29/1.00      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.29/1.00      | k1_relat_1(sK2) != sK1 ),
% 1.29/1.00      inference(unflattening,[status(thm)],[c_697]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_7,plain,
% 1.29/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 1.29/1.00      | v1_partfun1(X0,X1)
% 1.29/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.29/1.00      | v1_xboole_0(X2)
% 1.29/1.00      | ~ v1_funct_1(X0) ),
% 1.29/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_6,plain,
% 1.29/1.00      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.29/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_10,plain,
% 1.29/1.00      ( ~ v1_partfun1(X0,X1)
% 1.29/1.00      | ~ v4_relat_1(X0,X1)
% 1.29/1.00      | ~ v1_relat_1(X0)
% 1.29/1.00      | k1_relat_1(X0) = X1 ),
% 1.29/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_226,plain,
% 1.29/1.00      ( ~ v1_partfun1(X0,X1)
% 1.29/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.29/1.00      | ~ v1_relat_1(X0)
% 1.29/1.00      | k1_relat_1(X0) = X1 ),
% 1.29/1.00      inference(resolution,[status(thm)],[c_6,c_10]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_230,plain,
% 1.29/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.29/1.00      | ~ v1_partfun1(X0,X1)
% 1.29/1.00      | k1_relat_1(X0) = X1 ),
% 1.29/1.00      inference(global_propositional_subsumption,
% 1.29/1.00                [status(thm)],
% 1.29/1.00                [c_226,c_10,c_6,c_5]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_231,plain,
% 1.29/1.00      ( ~ v1_partfun1(X0,X1)
% 1.29/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.29/1.00      | k1_relat_1(X0) = X1 ),
% 1.29/1.00      inference(renaming,[status(thm)],[c_230]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_270,plain,
% 1.29/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 1.29/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.29/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 1.29/1.00      | v1_xboole_0(X2)
% 1.29/1.00      | ~ v1_funct_1(X0)
% 1.29/1.00      | k1_relat_1(X0) = X1 ),
% 1.29/1.00      inference(resolution,[status(thm)],[c_7,c_231]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_274,plain,
% 1.29/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.29/1.00      | ~ v1_funct_2(X0,X1,X2)
% 1.29/1.00      | v1_xboole_0(X2)
% 1.29/1.00      | ~ v1_funct_1(X0)
% 1.29/1.00      | k1_relat_1(X0) = X1 ),
% 1.29/1.00      inference(global_propositional_subsumption,
% 1.29/1.00                [status(thm)],
% 1.29/1.00                [c_270,c_10,c_7,c_6,c_5]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_275,plain,
% 1.29/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 1.29/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.29/1.00      | v1_xboole_0(X2)
% 1.29/1.00      | ~ v1_funct_1(X0)
% 1.29/1.00      | k1_relat_1(X0) = X1 ),
% 1.29/1.00      inference(renaming,[status(thm)],[c_274]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_323,plain,
% 1.29/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 1.29/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.29/1.00      | ~ v1_funct_1(X0)
% 1.29/1.00      | k1_relat_1(X0) = X1
% 1.29/1.00      | sK1 != X2 ),
% 1.29/1.00      inference(resolution_lifted,[status(thm)],[c_275,c_19]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_324,plain,
% 1.29/1.00      ( ~ v1_funct_2(X0,X1,sK1)
% 1.29/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 1.29/1.00      | ~ v1_funct_1(X0)
% 1.29/1.00      | k1_relat_1(X0) = X1 ),
% 1.29/1.00      inference(unflattening,[status(thm)],[c_323]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_445,plain,
% 1.29/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 1.29/1.00      | ~ v1_funct_1(X0)
% 1.29/1.00      | k1_relat_1(X0) = X1
% 1.29/1.00      | sK2 != X0
% 1.29/1.00      | sK1 != X1
% 1.29/1.00      | sK1 != sK1 ),
% 1.29/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_324]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_446,plain,
% 1.29/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.29/1.00      | ~ v1_funct_1(sK2)
% 1.29/1.00      | k1_relat_1(sK2) = sK1 ),
% 1.29/1.00      inference(unflattening,[status(thm)],[c_445]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_699,plain,
% 1.29/1.00      ( k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.29/1.00      | k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) ),
% 1.29/1.00      inference(global_propositional_subsumption,
% 1.29/1.00                [status(thm)],
% 1.29/1.00                [c_698,c_18,c_16,c_446]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_700,plain,
% 1.29/1.00      ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2))
% 1.29/1.00      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.29/1.00      inference(renaming,[status(thm)],[c_699]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_448,plain,
% 1.29/1.00      ( k1_relat_1(sK2) = sK1 ),
% 1.29/1.00      inference(global_propositional_subsumption,
% 1.29/1.00                [status(thm)],
% 1.29/1.00                [c_446,c_18,c_16]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_15,negated_conjecture,
% 1.29/1.00      ( ~ m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK1,sK2,X0) = X0 ),
% 1.29/1.00      inference(cnf_transformation,[],[f57]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_707,plain,
% 1.29/1.00      ( k3_funct_2(sK1,sK1,sK2,X0) = X0
% 1.29/1.00      | sK0(k1_relat_1(sK2),sK2) != X0
% 1.29/1.00      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.29/1.00      | k1_relat_1(sK2) != sK1 ),
% 1.29/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_606]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_708,plain,
% 1.29/1.00      ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
% 1.29/1.00      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.29/1.00      | k1_relat_1(sK2) != sK1 ),
% 1.29/1.00      inference(unflattening,[status(thm)],[c_707]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_709,plain,
% 1.29/1.00      ( k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.29/1.00      | k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2) ),
% 1.29/1.00      inference(global_propositional_subsumption,
% 1.29/1.00                [status(thm)],
% 1.29/1.00                [c_708,c_18,c_16,c_446]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_710,plain,
% 1.29/1.00      ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
% 1.29/1.00      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.29/1.00      inference(renaming,[status(thm)],[c_709]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_1073,plain,
% 1.29/1.00      ( k3_funct_2(sK1,sK1,sK2,sK0(sK1,sK2)) = sK0(sK1,sK2)
% 1.29/1.00      | k6_partfun1(sK1) = sK2 ),
% 1.29/1.00      inference(light_normalisation,[status(thm)],[c_710,c_448]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_12,plain,
% 1.29/1.00      ( r2_funct_2(X0,X1,X2,X2)
% 1.29/1.00      | ~ v1_funct_2(X2,X0,X1)
% 1.29/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.29/1.00      | ~ v1_funct_1(X2) ),
% 1.29/1.00      inference(cnf_transformation,[],[f68]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_14,negated_conjecture,
% 1.29/1.00      ( ~ r2_funct_2(sK1,sK1,sK2,k6_partfun1(sK1)) ),
% 1.29/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_406,plain,
% 1.29/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 1.29/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.29/1.00      | ~ v1_funct_1(X0)
% 1.29/1.00      | k6_partfun1(sK1) != X0
% 1.29/1.00      | sK2 != X0
% 1.29/1.00      | sK1 != X2
% 1.29/1.00      | sK1 != X1 ),
% 1.29/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_14]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_407,plain,
% 1.29/1.00      ( ~ v1_funct_2(k6_partfun1(sK1),sK1,sK1)
% 1.29/1.00      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.29/1.00      | ~ v1_funct_1(k6_partfun1(sK1))
% 1.29/1.00      | sK2 != k6_partfun1(sK1) ),
% 1.29/1.00      inference(unflattening,[status(thm)],[c_406]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_453,plain,
% 1.29/1.00      ( ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.29/1.00      | ~ v1_funct_1(k6_partfun1(sK1))
% 1.29/1.00      | k6_partfun1(sK1) != sK2
% 1.29/1.00      | sK1 != sK1 ),
% 1.29/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_407]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_534,plain,
% 1.29/1.00      ( ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.29/1.00      | k6_partfun1(sK1) != sK2
% 1.29/1.00      | sK1 != sK1 ),
% 1.29/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_453]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_717,plain,
% 1.29/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.29/1.00      | k6_partfun1(sK1) != sK2
% 1.29/1.00      | sK1 != sK1 ),
% 1.29/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_534]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_806,plain,
% 1.29/1.00      ( k6_partfun1(sK1) != sK2 ),
% 1.29/1.00      inference(equality_resolution_simp,[status(thm)],[c_717]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_1076,plain,
% 1.29/1.00      ( k3_funct_2(sK1,sK1,sK2,sK0(sK1,sK2)) = sK0(sK1,sK2) ),
% 1.29/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_1073,c_806]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_1078,plain,
% 1.29/1.00      ( k1_funct_1(sK2,sK0(sK1,sK2)) = sK0(sK1,sK2) | k6_partfun1(sK1) = sK2 ),
% 1.29/1.00      inference(light_normalisation,[status(thm)],[c_700,c_448,c_1076]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_1,plain,
% 1.29/1.00      ( ~ v1_relat_1(X0)
% 1.29/1.00      | ~ v1_funct_1(X0)
% 1.29/1.00      | k1_funct_1(X0,sK0(k1_relat_1(X0),X0)) != sK0(k1_relat_1(X0),X0)
% 1.29/1.00      | k6_partfun1(k1_relat_1(X0)) = X0 ),
% 1.29/1.00      inference(cnf_transformation,[],[f63]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_490,plain,
% 1.29/1.00      ( ~ v1_relat_1(X0)
% 1.29/1.00      | k1_funct_1(X0,sK0(k1_relat_1(X0),X0)) != sK0(k1_relat_1(X0),X0)
% 1.29/1.00      | k6_partfun1(k1_relat_1(X0)) = X0
% 1.29/1.00      | sK2 != X0 ),
% 1.29/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_18]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_491,plain,
% 1.29/1.00      ( ~ v1_relat_1(sK2)
% 1.29/1.00      | k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
% 1.29/1.00      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.29/1.00      inference(unflattening,[status(thm)],[c_490]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_617,plain,
% 1.29/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.29/1.00      | k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
% 1.29/1.00      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.29/1.00      | sK2 != X0 ),
% 1.29/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_491]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_618,plain,
% 1.29/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.29/1.00      | k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
% 1.29/1.00      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.29/1.00      inference(unflattening,[status(thm)],[c_617]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_620,plain,
% 1.29/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.29/1.00      | k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
% 1.29/1.00      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.29/1.00      inference(instantiation,[status(thm)],[c_618]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_622,plain,
% 1.29/1.00      ( k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
% 1.29/1.00      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.29/1.00      inference(global_propositional_subsumption,
% 1.29/1.00                [status(thm)],
% 1.29/1.00                [c_618,c_16,c_620]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_1062,plain,
% 1.29/1.00      ( k1_funct_1(sK2,sK0(sK1,sK2)) != sK0(sK1,sK2) | k6_partfun1(sK1) = sK2 ),
% 1.29/1.00      inference(light_normalisation,[status(thm)],[c_622,c_448]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_1065,plain,
% 1.29/1.00      ( k1_funct_1(sK2,sK0(sK1,sK2)) != sK0(sK1,sK2) ),
% 1.29/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_1062,c_806]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_1081,plain,
% 1.29/1.00      ( $false ),
% 1.29/1.00      inference(forward_subsumption_resolution,
% 1.29/1.00                [status(thm)],
% 1.29/1.00                [c_1078,c_806,c_1065]) ).
% 1.29/1.00  
% 1.29/1.00  
% 1.29/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.29/1.00  
% 1.29/1.00  ------                               Statistics
% 1.29/1.00  
% 1.29/1.00  ------ General
% 1.29/1.00  
% 1.29/1.00  abstr_ref_over_cycles:                  0
% 1.29/1.00  abstr_ref_under_cycles:                 0
% 1.29/1.00  gc_basic_clause_elim:                   0
% 1.29/1.00  forced_gc_time:                         0
% 1.29/1.00  parsing_time:                           0.011
% 1.29/1.00  unif_index_cands_time:                  0.
% 1.29/1.00  unif_index_add_time:                    0.
% 1.29/1.00  orderings_time:                         0.
% 1.29/1.00  out_proof_time:                         0.013
% 1.29/1.00  total_time:                             0.068
% 1.29/1.00  num_of_symbols:                         50
% 1.29/1.00  num_of_terms:                           891
% 1.29/1.00  
% 1.29/1.00  ------ Preprocessing
% 1.29/1.00  
% 1.29/1.00  num_of_splits:                          1
% 1.29/1.00  num_of_split_atoms:                     1
% 1.29/1.00  num_of_reused_defs:                     0
% 1.29/1.00  num_eq_ax_congr_red:                    4
% 1.29/1.00  num_of_sem_filtered_clauses:            1
% 1.29/1.00  num_of_subtypes:                        0
% 1.29/1.00  monotx_restored_types:                  0
% 1.29/1.00  sat_num_of_epr_types:                   0
% 1.29/1.00  sat_num_of_non_cyclic_types:            0
% 1.29/1.00  sat_guarded_non_collapsed_types:        0
% 1.29/1.00  num_pure_diseq_elim:                    0
% 1.29/1.00  simp_replaced_by:                       0
% 1.29/1.00  res_preprocessed:                       82
% 1.29/1.00  prep_upred:                             0
% 1.29/1.00  prep_unflattend:                        37
% 1.29/1.00  smt_new_axioms:                         0
% 1.29/1.00  pred_elim_cands:                        1
% 1.29/1.00  pred_elim:                              8
% 1.29/1.00  pred_elim_cl:                           8
% 1.29/1.00  pred_elim_cycles:                       14
% 1.29/1.00  merged_defs:                            0
% 1.29/1.00  merged_defs_ncl:                        0
% 1.29/1.00  bin_hyper_res:                          0
% 1.29/1.00  prep_cycles:                            5
% 1.29/1.00  pred_elim_time:                         0.011
% 1.29/1.00  splitting_time:                         0.
% 1.29/1.00  sem_filter_time:                        0.
% 1.29/1.00  monotx_time:                            0.
% 1.29/1.00  subtype_inf_time:                       0.
% 1.29/1.00  
% 1.29/1.00  ------ Problem properties
% 1.29/1.00  
% 1.29/1.00  clauses:                                11
% 1.29/1.00  conjectures:                            0
% 1.29/1.00  epr:                                    0
% 1.29/1.00  horn:                                   8
% 1.29/1.00  ground:                                 8
% 1.29/1.00  unary:                                  2
% 1.29/1.00  binary:                                 7
% 1.29/1.00  lits:                                   22
% 1.29/1.00  lits_eq:                                17
% 1.29/1.00  fd_pure:                                0
% 1.29/1.00  fd_pseudo:                              0
% 1.29/1.00  fd_cond:                                0
% 1.29/1.00  fd_pseudo_cond:                         0
% 1.29/1.00  ac_symbols:                             0
% 1.29/1.00  
% 1.29/1.00  ------ Propositional Solver
% 1.29/1.00  
% 1.29/1.00  prop_solver_calls:                      25
% 1.29/1.00  prop_fast_solver_calls:                 542
% 1.29/1.00  smt_solver_calls:                       0
% 1.29/1.00  smt_fast_solver_calls:                  0
% 1.29/1.00  prop_num_of_clauses:                    199
% 1.29/1.00  prop_preprocess_simplified:             1542
% 1.29/1.00  prop_fo_subsumed:                       10
% 1.29/1.00  prop_solver_time:                       0.
% 1.29/1.00  smt_solver_time:                        0.
% 1.29/1.00  smt_fast_solver_time:                   0.
% 1.29/1.00  prop_fast_solver_time:                  0.
% 1.29/1.00  prop_unsat_core_time:                   0.
% 1.29/1.00  
% 1.29/1.00  ------ QBF
% 1.29/1.00  
% 1.29/1.00  qbf_q_res:                              0
% 1.29/1.00  qbf_num_tautologies:                    0
% 1.29/1.00  qbf_prep_cycles:                        0
% 1.29/1.00  
% 1.29/1.00  ------ BMC1
% 1.29/1.00  
% 1.29/1.00  bmc1_current_bound:                     -1
% 1.29/1.00  bmc1_last_solved_bound:                 -1
% 1.29/1.00  bmc1_unsat_core_size:                   -1
% 1.29/1.00  bmc1_unsat_core_parents_size:           -1
% 1.29/1.00  bmc1_merge_next_fun:                    0
% 1.29/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.29/1.00  
% 1.29/1.00  ------ Instantiation
% 1.29/1.00  
% 1.29/1.00  inst_num_of_clauses:                    21
% 1.29/1.00  inst_num_in_passive:                    0
% 1.29/1.00  inst_num_in_active:                     0
% 1.29/1.00  inst_num_in_unprocessed:                21
% 1.29/1.00  inst_num_of_loops:                      0
% 1.29/1.00  inst_num_of_learning_restarts:          0
% 1.29/1.00  inst_num_moves_active_passive:          0
% 1.29/1.00  inst_lit_activity:                      0
% 1.29/1.00  inst_lit_activity_moves:                0
% 1.29/1.00  inst_num_tautologies:                   0
% 1.29/1.00  inst_num_prop_implied:                  0
% 1.29/1.00  inst_num_existing_simplified:           0
% 1.29/1.00  inst_num_eq_res_simplified:             0
% 1.29/1.00  inst_num_child_elim:                    0
% 1.29/1.00  inst_num_of_dismatching_blockings:      0
% 1.29/1.00  inst_num_of_non_proper_insts:           0
% 1.29/1.00  inst_num_of_duplicates:                 0
% 1.29/1.00  inst_inst_num_from_inst_to_res:         0
% 1.29/1.00  inst_dismatching_checking_time:         0.
% 1.29/1.00  
% 1.29/1.00  ------ Resolution
% 1.29/1.00  
% 1.29/1.00  res_num_of_clauses:                     0
% 1.29/1.00  res_num_in_passive:                     0
% 1.29/1.00  res_num_in_active:                      0
% 1.29/1.00  res_num_of_loops:                       87
% 1.29/1.00  res_forward_subset_subsumed:            1
% 1.29/1.00  res_backward_subset_subsumed:           0
% 1.29/1.00  res_forward_subsumed:                   0
% 1.29/1.00  res_backward_subsumed:                  2
% 1.29/1.00  res_forward_subsumption_resolution:     1
% 1.29/1.00  res_backward_subsumption_resolution:    0
% 1.29/1.00  res_clause_to_clause_subsumption:       20
% 1.29/1.00  res_orphan_elimination:                 0
% 1.29/1.00  res_tautology_del:                      4
% 1.29/1.00  res_num_eq_res_simplified:              2
% 1.29/1.00  res_num_sel_changes:                    0
% 1.29/1.00  res_moves_from_active_to_pass:          0
% 1.29/1.00  
% 1.29/1.00  ------ Superposition
% 1.29/1.00  
% 1.29/1.00  sup_time_total:                         0.
% 1.29/1.00  sup_time_generating:                    0.
% 1.29/1.00  sup_time_sim_full:                      0.
% 1.29/1.00  sup_time_sim_immed:                     0.
% 1.29/1.00  
% 1.29/1.00  sup_num_of_clauses:                     0
% 1.29/1.00  sup_num_in_active:                      0
% 1.29/1.00  sup_num_in_passive:                     0
% 1.29/1.00  sup_num_of_loops:                       0
% 1.29/1.00  sup_fw_superposition:                   0
% 1.29/1.00  sup_bw_superposition:                   0
% 1.29/1.00  sup_immediate_simplified:               0
% 1.29/1.00  sup_given_eliminated:                   0
% 1.29/1.00  comparisons_done:                       0
% 1.29/1.00  comparisons_avoided:                    0
% 1.29/1.00  
% 1.29/1.00  ------ Simplifications
% 1.29/1.00  
% 1.29/1.00  
% 1.29/1.00  sim_fw_subset_subsumed:                 0
% 1.29/1.00  sim_bw_subset_subsumed:                 0
% 1.29/1.00  sim_fw_subsumed:                        0
% 1.29/1.00  sim_bw_subsumed:                        0
% 1.29/1.00  sim_fw_subsumption_res:                 5
% 1.29/1.00  sim_bw_subsumption_res:                 0
% 1.29/1.00  sim_tautology_del:                      0
% 1.29/1.00  sim_eq_tautology_del:                   0
% 1.29/1.00  sim_eq_res_simp:                        0
% 1.29/1.00  sim_fw_demodulated:                     0
% 1.29/1.00  sim_bw_demodulated:                     0
% 1.29/1.00  sim_light_normalised:                   5
% 1.29/1.00  sim_joinable_taut:                      0
% 1.29/1.00  sim_joinable_simp:                      0
% 1.29/1.00  sim_ac_normalised:                      0
% 1.29/1.00  sim_smt_subsumption:                    0
% 1.29/1.00  
%------------------------------------------------------------------------------
