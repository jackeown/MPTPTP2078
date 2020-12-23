%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:32 EST 2020

% Result     : Theorem 1.33s
% Output     : CNFRefutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 992 expanded)
%              Number of clauses        :   71 ( 279 expanded)
%              Number of leaves         :   16 ( 235 expanded)
%              Depth                    :   26
%              Number of atoms          :  525 (5201 expanded)
%              Number of equality atoms :  199 (1194 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f37,plain,(
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

fof(f36,plain,
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

fof(f38,plain,
    ( ~ r2_funct_2(sK1,sK1,sK2,k6_partfun1(sK1))
    & ! [X2] :
        ( k3_funct_2(sK1,sK1,sK2,X2) = X2
        | ~ m1_subset_1(X2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v1_funct_2(sK2,sK1,sK1)
    & v1_funct_1(sK2)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f37,f36])).

fof(f57,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f56,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

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
    inference(nnf_transformation,[],[f16])).

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
    inference(flattening,[],[f29])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK0(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k6_partfun1(X0) = X1
      | r2_hidden(sK0(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f43,f50])).

fof(f66,plain,(
    ! [X1] :
      ( k6_partfun1(k1_relat_1(X1)) = X1
      | r2_hidden(sK0(k1_relat_1(X1),X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f62])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    ! [X2] :
      ( k3_funct_2(sK1,sK1,sK2,X2) = X2
      | ~ m1_subset_1(X2,sK1) ) ),
    inference(cnf_transformation,[],[f38])).

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

fof(f23,plain,(
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
    inference(flattening,[],[f23])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f24])).

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
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f52])).

fof(f60,plain,(
    ~ r2_funct_2(sK1,sK1,sK2,k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k6_partfun1(X0) = X1
      | k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f44,f50])).

fof(f65,plain,(
    ! [X1] :
      ( k6_partfun1(k1_relat_1(X1)) = X1
      | k1_funct_1(X1,sK0(k1_relat_1(X1),X1)) != sK0(k1_relat_1(X1),X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f61])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_20,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_246,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_247,plain,
    ( ~ v1_funct_2(X0,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ m1_subset_1(X2,sK1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(sK1,X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(unflattening,[status(thm)],[c_246])).

cnf(c_547,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ m1_subset_1(X2,sK1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(sK1,X1,X0,X2) = k1_funct_1(X0,X2)
    | sK2 != X0
    | sK1 != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_247])).

cnf(c_548,plain,
    ( ~ m1_subset_1(X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k3_funct_2(sK1,sK1,sK2,X0) = k1_funct_1(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_547])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_552,plain,
    ( ~ m1_subset_1(X0,sK1)
    | k3_funct_2(sK1,sK1,sK2,X0) = k1_funct_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_548,c_19,c_17])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_3,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k6_partfun1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_590,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | k6_partfun1(k1_relat_1(X0)) = X0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_19])).

cnf(c_591,plain,
    ( r2_hidden(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(unflattening,[status(thm)],[c_590])).

cnf(c_682,plain,
    ( m1_subset_1(X0,X1)
    | ~ v1_relat_1(sK2)
    | sK0(k1_relat_1(sK2),sK2) != X0
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | k1_relat_1(sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_591])).

cnf(c_683,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(unflattening,[status(thm)],[c_682])).

cnf(c_714,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_683])).

cnf(c_715,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(unflattening,[status(thm)],[c_714])).

cnf(c_717,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_715])).

cnf(c_719,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_715,c_17,c_717])).

cnf(c_810,plain,
    ( k3_funct_2(sK1,sK1,sK2,X0) = k1_funct_1(sK2,X0)
    | sK0(k1_relat_1(sK2),sK2) != X0
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | k1_relat_1(sK2) != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_552,c_719])).

cnf(c_811,plain,
    ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2))
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | k1_relat_1(sK2) != sK1 ),
    inference(unflattening,[status(thm)],[c_810])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_242,plain,
    ( sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_20])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_7,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_9,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_274,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_7,c_9])).

cnf(c_278,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_274,c_9,c_7,c_6])).

cnf(c_279,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_278])).

cnf(c_393,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_14,c_279])).

cnf(c_397,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_393,c_14,c_6,c_274])).

cnf(c_398,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_397])).

cnf(c_534,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | sK2 != X0
    | sK1 != X1
    | sK1 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_398,c_18])).

cnf(c_535,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k1_relat_1(sK2) = sK1
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_537,plain,
    ( k1_relat_1(sK2) = sK1
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_535,c_19,c_17])).

cnf(c_1052,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1071,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1052])).

cnf(c_1053,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1220,plain,
    ( sK1 != X0
    | sK1 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1053])).

cnf(c_1221,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1220])).

cnf(c_1330,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = sK2
    | k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_811,c_242,c_537,c_1071,c_1221])).

cnf(c_1331,plain,
    ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2))
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(renaming,[status(thm)],[c_1330])).

cnf(c_1228,plain,
    ( k1_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_537,c_242,c_1071,c_1221])).

cnf(c_16,negated_conjecture,
    ( ~ m1_subset_1(X0,sK1)
    | k3_funct_2(sK1,sK1,sK2,X0) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_821,plain,
    ( k3_funct_2(sK1,sK1,sK2,X0) = X0
    | sK0(k1_relat_1(sK2),sK2) != X0
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | k1_relat_1(sK2) != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_719])).

cnf(c_822,plain,
    ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | k1_relat_1(sK2) != sK1 ),
    inference(unflattening,[status(thm)],[c_821])).

cnf(c_1249,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = sK2
    | k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_822,c_242,c_537,c_1071,c_1221])).

cnf(c_1250,plain,
    ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(renaming,[status(thm)],[c_1249])).

cnf(c_1251,plain,
    ( k3_funct_2(sK1,sK1,sK2,sK0(sK1,sK2)) = sK0(sK1,sK2)
    | k6_partfun1(sK1) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_1250,c_1228])).

cnf(c_11,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_15,negated_conjecture,
    ( ~ r2_funct_2(sK1,sK1,sK2,k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_372,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k6_partfun1(sK1) != X0
    | sK2 != X0
    | sK1 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_15])).

cnf(c_373,plain,
    ( ~ v1_funct_2(k6_partfun1(sK1),sK1,sK1)
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(k6_partfun1(sK1))
    | sK2 != k6_partfun1(sK1) ),
    inference(unflattening,[status(thm)],[c_372])).

cnf(c_565,plain,
    ( ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(k6_partfun1(sK1))
    | k6_partfun1(sK1) != sK2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_373])).

cnf(c_647,plain,
    ( ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) != sK2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_565])).

cnf(c_832,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | k6_partfun1(sK1) != sK2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_647])).

cnf(c_923,plain,
    ( k6_partfun1(sK1) != sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_832])).

cnf(c_1254,plain,
    ( k3_funct_2(sK1,sK1,sK2,sK0(sK1,sK2)) = sK0(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1251,c_923])).

cnf(c_1332,plain,
    ( k1_funct_1(sK2,sK0(sK1,sK2)) = sK0(sK1,sK2)
    | k6_partfun1(sK1) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_1331,c_1228,c_1254])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK0(k1_relat_1(X0),X0)) != sK0(k1_relat_1(X0),X0)
    | k6_partfun1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_603,plain,
    ( ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK0(k1_relat_1(X0),X0)) != sK0(k1_relat_1(X0),X0)
    | k6_partfun1(k1_relat_1(X0)) = X0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_19])).

cnf(c_604,plain,
    ( ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(unflattening,[status(thm)],[c_603])).

cnf(c_730,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_604])).

cnf(c_731,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(unflattening,[status(thm)],[c_730])).

cnf(c_733,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_731])).

cnf(c_735,plain,
    ( k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_731,c_17,c_733])).

cnf(c_1296,plain,
    ( k1_funct_1(sK2,sK0(sK1,sK2)) != sK0(sK1,sK2)
    | k6_partfun1(sK1) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_735,c_1228])).

cnf(c_1299,plain,
    ( k1_funct_1(sK2,sK0(sK1,sK2)) != sK0(sK1,sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1296,c_923])).

cnf(c_1335,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1332,c_923,c_1299])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:55:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.33/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.33/0.98  
% 1.33/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.33/0.98  
% 1.33/0.98  ------  iProver source info
% 1.33/0.98  
% 1.33/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.33/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.33/0.98  git: non_committed_changes: false
% 1.33/0.98  git: last_make_outside_of_git: false
% 1.33/0.98  
% 1.33/0.98  ------ 
% 1.33/0.98  
% 1.33/0.98  ------ Input Options
% 1.33/0.98  
% 1.33/0.98  --out_options                           all
% 1.33/0.98  --tptp_safe_out                         true
% 1.33/0.98  --problem_path                          ""
% 1.33/0.98  --include_path                          ""
% 1.33/0.98  --clausifier                            res/vclausify_rel
% 1.33/0.98  --clausifier_options                    --mode clausify
% 1.33/0.98  --stdin                                 false
% 1.33/0.98  --stats_out                             all
% 1.33/0.98  
% 1.33/0.98  ------ General Options
% 1.33/0.98  
% 1.33/0.98  --fof                                   false
% 1.33/0.98  --time_out_real                         305.
% 1.33/0.98  --time_out_virtual                      -1.
% 1.33/0.98  --symbol_type_check                     false
% 1.33/0.98  --clausify_out                          false
% 1.33/0.98  --sig_cnt_out                           false
% 1.33/0.98  --trig_cnt_out                          false
% 1.33/0.98  --trig_cnt_out_tolerance                1.
% 1.33/0.98  --trig_cnt_out_sk_spl                   false
% 1.33/0.98  --abstr_cl_out                          false
% 1.33/0.98  
% 1.33/0.98  ------ Global Options
% 1.33/0.98  
% 1.33/0.98  --schedule                              default
% 1.33/0.98  --add_important_lit                     false
% 1.33/0.98  --prop_solver_per_cl                    1000
% 1.33/0.98  --min_unsat_core                        false
% 1.33/0.98  --soft_assumptions                      false
% 1.33/0.98  --soft_lemma_size                       3
% 1.33/0.98  --prop_impl_unit_size                   0
% 1.33/0.98  --prop_impl_unit                        []
% 1.33/0.98  --share_sel_clauses                     true
% 1.33/0.98  --reset_solvers                         false
% 1.33/0.98  --bc_imp_inh                            [conj_cone]
% 1.33/0.98  --conj_cone_tolerance                   3.
% 1.33/0.98  --extra_neg_conj                        none
% 1.33/0.98  --large_theory_mode                     true
% 1.33/0.98  --prolific_symb_bound                   200
% 1.33/0.98  --lt_threshold                          2000
% 1.33/0.98  --clause_weak_htbl                      true
% 1.33/0.98  --gc_record_bc_elim                     false
% 1.33/0.98  
% 1.33/0.98  ------ Preprocessing Options
% 1.33/0.98  
% 1.33/0.98  --preprocessing_flag                    true
% 1.33/0.98  --time_out_prep_mult                    0.1
% 1.33/0.98  --splitting_mode                        input
% 1.33/0.98  --splitting_grd                         true
% 1.33/0.98  --splitting_cvd                         false
% 1.33/0.98  --splitting_cvd_svl                     false
% 1.33/0.98  --splitting_nvd                         32
% 1.33/0.98  --sub_typing                            true
% 1.33/0.98  --prep_gs_sim                           true
% 1.33/0.98  --prep_unflatten                        true
% 1.33/0.98  --prep_res_sim                          true
% 1.33/0.98  --prep_upred                            true
% 1.33/0.98  --prep_sem_filter                       exhaustive
% 1.33/0.98  --prep_sem_filter_out                   false
% 1.33/0.98  --pred_elim                             true
% 1.33/0.98  --res_sim_input                         true
% 1.33/0.98  --eq_ax_congr_red                       true
% 1.33/0.98  --pure_diseq_elim                       true
% 1.33/0.98  --brand_transform                       false
% 1.33/0.98  --non_eq_to_eq                          false
% 1.33/0.98  --prep_def_merge                        true
% 1.33/0.98  --prep_def_merge_prop_impl              false
% 1.33/0.98  --prep_def_merge_mbd                    true
% 1.33/0.98  --prep_def_merge_tr_red                 false
% 1.33/0.98  --prep_def_merge_tr_cl                  false
% 1.33/0.98  --smt_preprocessing                     true
% 1.33/0.98  --smt_ac_axioms                         fast
% 1.33/0.98  --preprocessed_out                      false
% 1.33/0.98  --preprocessed_stats                    false
% 1.33/0.98  
% 1.33/0.98  ------ Abstraction refinement Options
% 1.33/0.98  
% 1.33/0.98  --abstr_ref                             []
% 1.33/0.98  --abstr_ref_prep                        false
% 1.33/0.98  --abstr_ref_until_sat                   false
% 1.33/0.98  --abstr_ref_sig_restrict                funpre
% 1.33/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.33/0.98  --abstr_ref_under                       []
% 1.33/0.98  
% 1.33/0.98  ------ SAT Options
% 1.33/0.98  
% 1.33/0.98  --sat_mode                              false
% 1.33/0.98  --sat_fm_restart_options                ""
% 1.33/0.98  --sat_gr_def                            false
% 1.33/0.98  --sat_epr_types                         true
% 1.33/0.98  --sat_non_cyclic_types                  false
% 1.33/0.98  --sat_finite_models                     false
% 1.33/0.98  --sat_fm_lemmas                         false
% 1.33/0.98  --sat_fm_prep                           false
% 1.33/0.98  --sat_fm_uc_incr                        true
% 1.33/0.98  --sat_out_model                         small
% 1.33/0.98  --sat_out_clauses                       false
% 1.33/0.98  
% 1.33/0.98  ------ QBF Options
% 1.33/0.98  
% 1.33/0.98  --qbf_mode                              false
% 1.33/0.98  --qbf_elim_univ                         false
% 1.33/0.98  --qbf_dom_inst                          none
% 1.33/0.98  --qbf_dom_pre_inst                      false
% 1.33/0.98  --qbf_sk_in                             false
% 1.33/0.98  --qbf_pred_elim                         true
% 1.33/0.98  --qbf_split                             512
% 1.33/0.98  
% 1.33/0.98  ------ BMC1 Options
% 1.33/0.98  
% 1.33/0.98  --bmc1_incremental                      false
% 1.33/0.98  --bmc1_axioms                           reachable_all
% 1.33/0.98  --bmc1_min_bound                        0
% 1.33/0.98  --bmc1_max_bound                        -1
% 1.33/0.98  --bmc1_max_bound_default                -1
% 1.33/0.98  --bmc1_symbol_reachability              true
% 1.33/0.98  --bmc1_property_lemmas                  false
% 1.33/0.98  --bmc1_k_induction                      false
% 1.33/0.98  --bmc1_non_equiv_states                 false
% 1.33/0.98  --bmc1_deadlock                         false
% 1.33/0.98  --bmc1_ucm                              false
% 1.33/0.98  --bmc1_add_unsat_core                   none
% 1.33/0.98  --bmc1_unsat_core_children              false
% 1.33/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.33/0.98  --bmc1_out_stat                         full
% 1.33/0.98  --bmc1_ground_init                      false
% 1.33/0.98  --bmc1_pre_inst_next_state              false
% 1.33/0.98  --bmc1_pre_inst_state                   false
% 1.33/0.98  --bmc1_pre_inst_reach_state             false
% 1.33/0.98  --bmc1_out_unsat_core                   false
% 1.33/0.98  --bmc1_aig_witness_out                  false
% 1.33/0.98  --bmc1_verbose                          false
% 1.33/0.98  --bmc1_dump_clauses_tptp                false
% 1.33/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.33/0.98  --bmc1_dump_file                        -
% 1.33/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.33/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.33/0.98  --bmc1_ucm_extend_mode                  1
% 1.33/0.98  --bmc1_ucm_init_mode                    2
% 1.33/0.98  --bmc1_ucm_cone_mode                    none
% 1.33/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.33/0.98  --bmc1_ucm_relax_model                  4
% 1.33/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.33/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.33/0.98  --bmc1_ucm_layered_model                none
% 1.33/0.98  --bmc1_ucm_max_lemma_size               10
% 1.33/0.98  
% 1.33/0.98  ------ AIG Options
% 1.33/0.98  
% 1.33/0.98  --aig_mode                              false
% 1.33/0.98  
% 1.33/0.98  ------ Instantiation Options
% 1.33/0.98  
% 1.33/0.98  --instantiation_flag                    true
% 1.33/0.98  --inst_sos_flag                         false
% 1.33/0.98  --inst_sos_phase                        true
% 1.33/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.33/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.33/0.98  --inst_lit_sel_side                     num_symb
% 1.33/0.98  --inst_solver_per_active                1400
% 1.33/0.98  --inst_solver_calls_frac                1.
% 1.33/0.98  --inst_passive_queue_type               priority_queues
% 1.33/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.33/0.98  --inst_passive_queues_freq              [25;2]
% 1.33/0.98  --inst_dismatching                      true
% 1.33/0.98  --inst_eager_unprocessed_to_passive     true
% 1.33/0.98  --inst_prop_sim_given                   true
% 1.33/0.98  --inst_prop_sim_new                     false
% 1.33/0.98  --inst_subs_new                         false
% 1.33/0.98  --inst_eq_res_simp                      false
% 1.33/0.98  --inst_subs_given                       false
% 1.33/0.98  --inst_orphan_elimination               true
% 1.33/0.98  --inst_learning_loop_flag               true
% 1.33/0.98  --inst_learning_start                   3000
% 1.33/0.98  --inst_learning_factor                  2
% 1.33/0.98  --inst_start_prop_sim_after_learn       3
% 1.33/0.98  --inst_sel_renew                        solver
% 1.33/0.98  --inst_lit_activity_flag                true
% 1.33/0.98  --inst_restr_to_given                   false
% 1.33/0.98  --inst_activity_threshold               500
% 1.33/0.98  --inst_out_proof                        true
% 1.33/0.98  
% 1.33/0.98  ------ Resolution Options
% 1.33/0.98  
% 1.33/0.98  --resolution_flag                       true
% 1.33/0.98  --res_lit_sel                           adaptive
% 1.33/0.98  --res_lit_sel_side                      none
% 1.33/0.98  --res_ordering                          kbo
% 1.33/0.98  --res_to_prop_solver                    active
% 1.33/0.98  --res_prop_simpl_new                    false
% 1.33/0.98  --res_prop_simpl_given                  true
% 1.33/0.98  --res_passive_queue_type                priority_queues
% 1.33/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.33/0.98  --res_passive_queues_freq               [15;5]
% 1.33/0.98  --res_forward_subs                      full
% 1.33/0.98  --res_backward_subs                     full
% 1.33/0.98  --res_forward_subs_resolution           true
% 1.33/0.98  --res_backward_subs_resolution          true
% 1.33/0.98  --res_orphan_elimination                true
% 1.33/0.98  --res_time_limit                        2.
% 1.33/0.98  --res_out_proof                         true
% 1.33/0.98  
% 1.33/0.98  ------ Superposition Options
% 1.33/0.98  
% 1.33/0.98  --superposition_flag                    true
% 1.33/0.98  --sup_passive_queue_type                priority_queues
% 1.33/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.33/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.33/0.98  --demod_completeness_check              fast
% 1.33/0.98  --demod_use_ground                      true
% 1.33/0.98  --sup_to_prop_solver                    passive
% 1.33/0.98  --sup_prop_simpl_new                    true
% 1.33/0.98  --sup_prop_simpl_given                  true
% 1.33/0.98  --sup_fun_splitting                     false
% 1.33/0.98  --sup_smt_interval                      50000
% 1.33/0.98  
% 1.33/0.98  ------ Superposition Simplification Setup
% 1.33/0.98  
% 1.33/0.98  --sup_indices_passive                   []
% 1.33/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.33/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.33/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.33/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.33/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.33/0.98  --sup_full_bw                           [BwDemod]
% 1.33/0.98  --sup_immed_triv                        [TrivRules]
% 1.33/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.33/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.33/0.98  --sup_immed_bw_main                     []
% 1.33/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.33/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.33/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.33/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.33/0.98  
% 1.33/0.98  ------ Combination Options
% 1.33/0.98  
% 1.33/0.98  --comb_res_mult                         3
% 1.33/0.98  --comb_sup_mult                         2
% 1.33/0.98  --comb_inst_mult                        10
% 1.33/0.98  
% 1.33/0.98  ------ Debug Options
% 1.33/0.98  
% 1.33/0.98  --dbg_backtrace                         false
% 1.33/0.98  --dbg_dump_prop_clauses                 false
% 1.33/0.98  --dbg_dump_prop_clauses_file            -
% 1.33/0.98  --dbg_out_stat                          false
% 1.33/0.98  ------ Parsing...
% 1.33/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.33/0.98  
% 1.33/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 1.33/0.98  
% 1.33/0.98  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.33/0.98  
% 1.33/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.33/0.98  ------ Proving...
% 1.33/0.98  ------ Problem Properties 
% 1.33/0.98  
% 1.33/0.98  
% 1.33/0.98  clauses                                 12
% 1.33/0.98  conjectures                             0
% 1.33/0.98  EPR                                     1
% 1.33/0.98  Horn                                    8
% 1.33/0.98  unary                                   2
% 1.33/0.98  binary                                  6
% 1.33/0.98  lits                                    26
% 1.33/0.98  lits eq                                 21
% 1.33/0.98  fd_pure                                 0
% 1.33/0.98  fd_pseudo                               0
% 1.33/0.98  fd_cond                                 0
% 1.33/0.98  fd_pseudo_cond                          0
% 1.33/0.98  AC symbols                              0
% 1.33/0.98  
% 1.33/0.98  ------ Schedule dynamic 5 is on 
% 1.33/0.98  
% 1.33/0.98  ------ no conjectures: strip conj schedule 
% 1.33/0.98  
% 1.33/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 1.33/0.98  
% 1.33/0.98  
% 1.33/0.98  ------ 
% 1.33/0.98  Current options:
% 1.33/0.98  ------ 
% 1.33/0.98  
% 1.33/0.98  ------ Input Options
% 1.33/0.98  
% 1.33/0.98  --out_options                           all
% 1.33/0.98  --tptp_safe_out                         true
% 1.33/0.98  --problem_path                          ""
% 1.33/0.98  --include_path                          ""
% 1.33/0.98  --clausifier                            res/vclausify_rel
% 1.33/0.98  --clausifier_options                    --mode clausify
% 1.33/0.98  --stdin                                 false
% 1.33/0.98  --stats_out                             all
% 1.33/0.98  
% 1.33/0.98  ------ General Options
% 1.33/0.98  
% 1.33/0.98  --fof                                   false
% 1.33/0.98  --time_out_real                         305.
% 1.33/0.98  --time_out_virtual                      -1.
% 1.33/0.98  --symbol_type_check                     false
% 1.33/0.98  --clausify_out                          false
% 1.33/0.98  --sig_cnt_out                           false
% 1.33/0.98  --trig_cnt_out                          false
% 1.33/0.98  --trig_cnt_out_tolerance                1.
% 1.33/0.98  --trig_cnt_out_sk_spl                   false
% 1.33/0.98  --abstr_cl_out                          false
% 1.33/0.98  
% 1.33/0.98  ------ Global Options
% 1.33/0.98  
% 1.33/0.98  --schedule                              default
% 1.33/0.98  --add_important_lit                     false
% 1.33/0.98  --prop_solver_per_cl                    1000
% 1.33/0.98  --min_unsat_core                        false
% 1.33/0.98  --soft_assumptions                      false
% 1.33/0.98  --soft_lemma_size                       3
% 1.33/0.98  --prop_impl_unit_size                   0
% 1.33/0.98  --prop_impl_unit                        []
% 1.33/0.98  --share_sel_clauses                     true
% 1.33/0.98  --reset_solvers                         false
% 1.33/0.98  --bc_imp_inh                            [conj_cone]
% 1.33/0.98  --conj_cone_tolerance                   3.
% 1.33/0.98  --extra_neg_conj                        none
% 1.33/0.98  --large_theory_mode                     true
% 1.33/0.98  --prolific_symb_bound                   200
% 1.33/0.98  --lt_threshold                          2000
% 1.33/0.98  --clause_weak_htbl                      true
% 1.33/0.98  --gc_record_bc_elim                     false
% 1.33/0.98  
% 1.33/0.98  ------ Preprocessing Options
% 1.33/0.98  
% 1.33/0.98  --preprocessing_flag                    true
% 1.33/0.98  --time_out_prep_mult                    0.1
% 1.33/0.98  --splitting_mode                        input
% 1.33/0.98  --splitting_grd                         true
% 1.33/0.98  --splitting_cvd                         false
% 1.33/0.98  --splitting_cvd_svl                     false
% 1.33/0.98  --splitting_nvd                         32
% 1.33/0.98  --sub_typing                            true
% 1.33/0.98  --prep_gs_sim                           true
% 1.33/0.98  --prep_unflatten                        true
% 1.33/0.98  --prep_res_sim                          true
% 1.33/0.98  --prep_upred                            true
% 1.33/0.98  --prep_sem_filter                       exhaustive
% 1.33/0.98  --prep_sem_filter_out                   false
% 1.33/0.98  --pred_elim                             true
% 1.33/0.98  --res_sim_input                         true
% 1.33/0.98  --eq_ax_congr_red                       true
% 1.33/0.98  --pure_diseq_elim                       true
% 1.33/0.98  --brand_transform                       false
% 1.33/0.98  --non_eq_to_eq                          false
% 1.33/0.98  --prep_def_merge                        true
% 1.33/0.98  --prep_def_merge_prop_impl              false
% 1.33/0.98  --prep_def_merge_mbd                    true
% 1.33/0.98  --prep_def_merge_tr_red                 false
% 1.33/0.98  --prep_def_merge_tr_cl                  false
% 1.33/0.98  --smt_preprocessing                     true
% 1.33/0.98  --smt_ac_axioms                         fast
% 1.33/0.98  --preprocessed_out                      false
% 1.33/0.98  --preprocessed_stats                    false
% 1.33/0.98  
% 1.33/0.98  ------ Abstraction refinement Options
% 1.33/0.98  
% 1.33/0.98  --abstr_ref                             []
% 1.33/0.98  --abstr_ref_prep                        false
% 1.33/0.98  --abstr_ref_until_sat                   false
% 1.33/0.98  --abstr_ref_sig_restrict                funpre
% 1.33/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.33/0.98  --abstr_ref_under                       []
% 1.33/0.98  
% 1.33/0.98  ------ SAT Options
% 1.33/0.98  
% 1.33/0.98  --sat_mode                              false
% 1.33/0.98  --sat_fm_restart_options                ""
% 1.33/0.98  --sat_gr_def                            false
% 1.33/0.98  --sat_epr_types                         true
% 1.33/0.98  --sat_non_cyclic_types                  false
% 1.33/0.98  --sat_finite_models                     false
% 1.33/0.98  --sat_fm_lemmas                         false
% 1.33/0.98  --sat_fm_prep                           false
% 1.33/0.98  --sat_fm_uc_incr                        true
% 1.33/0.98  --sat_out_model                         small
% 1.33/0.98  --sat_out_clauses                       false
% 1.33/0.98  
% 1.33/0.98  ------ QBF Options
% 1.33/0.98  
% 1.33/0.98  --qbf_mode                              false
% 1.33/0.98  --qbf_elim_univ                         false
% 1.33/0.98  --qbf_dom_inst                          none
% 1.33/0.98  --qbf_dom_pre_inst                      false
% 1.33/0.98  --qbf_sk_in                             false
% 1.33/0.98  --qbf_pred_elim                         true
% 1.33/0.98  --qbf_split                             512
% 1.33/0.98  
% 1.33/0.98  ------ BMC1 Options
% 1.33/0.98  
% 1.33/0.98  --bmc1_incremental                      false
% 1.33/0.98  --bmc1_axioms                           reachable_all
% 1.33/0.98  --bmc1_min_bound                        0
% 1.33/0.98  --bmc1_max_bound                        -1
% 1.33/0.98  --bmc1_max_bound_default                -1
% 1.33/0.98  --bmc1_symbol_reachability              true
% 1.33/0.98  --bmc1_property_lemmas                  false
% 1.33/0.98  --bmc1_k_induction                      false
% 1.33/0.98  --bmc1_non_equiv_states                 false
% 1.33/0.98  --bmc1_deadlock                         false
% 1.33/0.98  --bmc1_ucm                              false
% 1.33/0.98  --bmc1_add_unsat_core                   none
% 1.33/0.98  --bmc1_unsat_core_children              false
% 1.33/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.33/0.98  --bmc1_out_stat                         full
% 1.33/0.98  --bmc1_ground_init                      false
% 1.33/0.98  --bmc1_pre_inst_next_state              false
% 1.33/0.98  --bmc1_pre_inst_state                   false
% 1.33/0.98  --bmc1_pre_inst_reach_state             false
% 1.33/0.98  --bmc1_out_unsat_core                   false
% 1.33/0.98  --bmc1_aig_witness_out                  false
% 1.33/0.98  --bmc1_verbose                          false
% 1.33/0.98  --bmc1_dump_clauses_tptp                false
% 1.33/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.33/0.98  --bmc1_dump_file                        -
% 1.33/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.33/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.33/0.98  --bmc1_ucm_extend_mode                  1
% 1.33/0.98  --bmc1_ucm_init_mode                    2
% 1.33/0.98  --bmc1_ucm_cone_mode                    none
% 1.33/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.33/0.98  --bmc1_ucm_relax_model                  4
% 1.33/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.33/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.33/0.98  --bmc1_ucm_layered_model                none
% 1.33/0.98  --bmc1_ucm_max_lemma_size               10
% 1.33/0.98  
% 1.33/0.98  ------ AIG Options
% 1.33/0.98  
% 1.33/0.98  --aig_mode                              false
% 1.33/0.98  
% 1.33/0.98  ------ Instantiation Options
% 1.33/0.98  
% 1.33/0.98  --instantiation_flag                    true
% 1.33/0.98  --inst_sos_flag                         false
% 1.33/0.98  --inst_sos_phase                        true
% 1.33/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.33/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.33/0.98  --inst_lit_sel_side                     none
% 1.33/0.98  --inst_solver_per_active                1400
% 1.33/0.98  --inst_solver_calls_frac                1.
% 1.33/0.98  --inst_passive_queue_type               priority_queues
% 1.33/0.98  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 1.33/0.98  --inst_passive_queues_freq              [25;2]
% 1.33/0.98  --inst_dismatching                      true
% 1.33/0.98  --inst_eager_unprocessed_to_passive     true
% 1.33/0.98  --inst_prop_sim_given                   true
% 1.33/0.98  --inst_prop_sim_new                     false
% 1.33/0.98  --inst_subs_new                         false
% 1.33/0.98  --inst_eq_res_simp                      false
% 1.33/0.98  --inst_subs_given                       false
% 1.33/0.98  --inst_orphan_elimination               true
% 1.33/0.98  --inst_learning_loop_flag               true
% 1.33/0.98  --inst_learning_start                   3000
% 1.33/0.98  --inst_learning_factor                  2
% 1.33/0.98  --inst_start_prop_sim_after_learn       3
% 1.33/0.98  --inst_sel_renew                        solver
% 1.33/0.98  --inst_lit_activity_flag                true
% 1.33/0.98  --inst_restr_to_given                   false
% 1.33/0.98  --inst_activity_threshold               500
% 1.33/0.98  --inst_out_proof                        true
% 1.33/0.98  
% 1.33/0.98  ------ Resolution Options
% 1.33/0.98  
% 1.33/0.98  --resolution_flag                       false
% 1.33/0.98  --res_lit_sel                           adaptive
% 1.33/0.98  --res_lit_sel_side                      none
% 1.33/0.98  --res_ordering                          kbo
% 1.33/0.98  --res_to_prop_solver                    active
% 1.33/0.98  --res_prop_simpl_new                    false
% 1.33/0.98  --res_prop_simpl_given                  true
% 1.33/0.98  --res_passive_queue_type                priority_queues
% 1.33/0.98  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 1.33/0.98  --res_passive_queues_freq               [15;5]
% 1.33/0.98  --res_forward_subs                      full
% 1.33/0.98  --res_backward_subs                     full
% 1.33/0.98  --res_forward_subs_resolution           true
% 1.33/0.98  --res_backward_subs_resolution          true
% 1.33/0.98  --res_orphan_elimination                true
% 1.33/0.98  --res_time_limit                        2.
% 1.33/0.98  --res_out_proof                         true
% 1.33/0.98  
% 1.33/0.98  ------ Superposition Options
% 1.33/0.98  
% 1.33/0.98  --superposition_flag                    true
% 1.33/0.98  --sup_passive_queue_type                priority_queues
% 1.33/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.33/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.33/0.98  --demod_completeness_check              fast
% 1.33/0.98  --demod_use_ground                      true
% 1.33/0.98  --sup_to_prop_solver                    passive
% 1.33/0.98  --sup_prop_simpl_new                    true
% 1.33/0.98  --sup_prop_simpl_given                  true
% 1.33/0.98  --sup_fun_splitting                     false
% 1.33/0.98  --sup_smt_interval                      50000
% 1.33/0.98  
% 1.33/0.98  ------ Superposition Simplification Setup
% 1.33/0.98  
% 1.33/0.98  --sup_indices_passive                   []
% 1.33/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.33/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.33/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.33/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.33/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.33/0.98  --sup_full_bw                           [BwDemod]
% 1.33/0.98  --sup_immed_triv                        [TrivRules]
% 1.33/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.33/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.33/0.98  --sup_immed_bw_main                     []
% 1.33/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.33/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.33/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.33/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.33/0.98  
% 1.33/0.98  ------ Combination Options
% 1.33/0.98  
% 1.33/0.98  --comb_res_mult                         3
% 1.33/0.98  --comb_sup_mult                         2
% 1.33/0.98  --comb_inst_mult                        10
% 1.33/0.98  
% 1.33/0.98  ------ Debug Options
% 1.33/0.98  
% 1.33/0.98  --dbg_backtrace                         false
% 1.33/0.98  --dbg_dump_prop_clauses                 false
% 1.33/0.98  --dbg_dump_prop_clauses_file            -
% 1.33/0.98  --dbg_out_stat                          false
% 1.33/0.98  
% 1.33/0.98  
% 1.33/0.98  
% 1.33/0.98  
% 1.33/0.98  ------ Proving...
% 1.33/0.98  
% 1.33/0.98  
% 1.33/0.98  % SZS status Theorem for theBenchmark.p
% 1.33/0.98  
% 1.33/0.98   Resolution empty clause
% 1.33/0.98  
% 1.33/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.33/0.98  
% 1.33/0.98  fof(f11,conjecture,(
% 1.33/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (! [X2] : (m1_subset_1(X2,X0) => k3_funct_2(X0,X0,X1,X2) = X2) => r2_funct_2(X0,X0,X1,k6_partfun1(X0)))))),
% 1.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.33/0.98  
% 1.33/0.98  fof(f12,negated_conjecture,(
% 1.33/0.98    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (! [X2] : (m1_subset_1(X2,X0) => k3_funct_2(X0,X0,X1,X2) = X2) => r2_funct_2(X0,X0,X1,k6_partfun1(X0)))))),
% 1.33/0.98    inference(negated_conjecture,[],[f11])).
% 1.33/0.98  
% 1.33/0.98  fof(f27,plain,(
% 1.33/0.98    ? [X0] : (? [X1] : ((~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))) & ~v1_xboole_0(X0))),
% 1.33/0.98    inference(ennf_transformation,[],[f12])).
% 1.33/0.98  
% 1.33/0.98  fof(f28,plain,(
% 1.33/0.98    ? [X0] : (? [X1] : (~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0))),
% 1.33/0.98    inference(flattening,[],[f27])).
% 1.33/0.98  
% 1.33/0.98  fof(f37,plain,(
% 1.33/0.98    ( ! [X0] : (? [X1] : (~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (~r2_funct_2(X0,X0,sK2,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,sK2,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 1.33/0.98    introduced(choice_axiom,[])).
% 1.33/0.98  
% 1.33/0.98  fof(f36,plain,(
% 1.33/0.98    ? [X0] : (? [X1] : (~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (~r2_funct_2(sK1,sK1,X1,k6_partfun1(sK1)) & ! [X2] : (k3_funct_2(sK1,sK1,X1,X2) = X2 | ~m1_subset_1(X2,sK1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_2(X1,sK1,sK1) & v1_funct_1(X1)) & ~v1_xboole_0(sK1))),
% 1.33/0.98    introduced(choice_axiom,[])).
% 1.33/0.98  
% 1.33/0.98  fof(f38,plain,(
% 1.33/0.98    (~r2_funct_2(sK1,sK1,sK2,k6_partfun1(sK1)) & ! [X2] : (k3_funct_2(sK1,sK1,sK2,X2) = X2 | ~m1_subset_1(X2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)) & ~v1_xboole_0(sK1)),
% 1.33/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f37,f36])).
% 1.33/0.98  
% 1.33/0.98  fof(f57,plain,(
% 1.33/0.98    v1_funct_2(sK2,sK1,sK1)),
% 1.33/0.98    inference(cnf_transformation,[],[f38])).
% 1.33/0.98  
% 1.33/0.98  fof(f7,axiom,(
% 1.33/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3))),
% 1.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.33/0.98  
% 1.33/0.98  fof(f21,plain,(
% 1.33/0.98    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 1.33/0.98    inference(ennf_transformation,[],[f7])).
% 1.33/0.98  
% 1.33/0.98  fof(f22,plain,(
% 1.33/0.98    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 1.33/0.98    inference(flattening,[],[f21])).
% 1.33/0.98  
% 1.33/0.98  fof(f49,plain,(
% 1.33/0.98    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 1.33/0.98    inference(cnf_transformation,[],[f22])).
% 1.33/0.98  
% 1.33/0.98  fof(f55,plain,(
% 1.33/0.98    ~v1_xboole_0(sK1)),
% 1.33/0.98    inference(cnf_transformation,[],[f38])).
% 1.33/0.98  
% 1.33/0.98  fof(f56,plain,(
% 1.33/0.98    v1_funct_1(sK2)),
% 1.33/0.98    inference(cnf_transformation,[],[f38])).
% 1.33/0.98  
% 1.33/0.98  fof(f58,plain,(
% 1.33/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 1.33/0.98    inference(cnf_transformation,[],[f38])).
% 1.33/0.98  
% 1.33/0.98  fof(f4,axiom,(
% 1.33/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.33/0.98  
% 1.33/0.98  fof(f17,plain,(
% 1.33/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.98    inference(ennf_transformation,[],[f4])).
% 1.33/0.98  
% 1.33/0.98  fof(f45,plain,(
% 1.33/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.33/0.98    inference(cnf_transformation,[],[f17])).
% 1.33/0.98  
% 1.33/0.98  fof(f2,axiom,(
% 1.33/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.33/0.98  
% 1.33/0.98  fof(f14,plain,(
% 1.33/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.33/0.98    inference(ennf_transformation,[],[f2])).
% 1.33/0.98  
% 1.33/0.98  fof(f40,plain,(
% 1.33/0.98    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.33/0.98    inference(cnf_transformation,[],[f14])).
% 1.33/0.98  
% 1.33/0.98  fof(f3,axiom,(
% 1.33/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 1.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.33/0.98  
% 1.33/0.98  fof(f15,plain,(
% 1.33/0.98    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.33/0.98    inference(ennf_transformation,[],[f3])).
% 1.33/0.98  
% 1.33/0.98  fof(f16,plain,(
% 1.33/0.98    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.33/0.98    inference(flattening,[],[f15])).
% 1.33/0.98  
% 1.33/0.98  fof(f29,plain,(
% 1.33/0.98    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.33/0.98    inference(nnf_transformation,[],[f16])).
% 1.33/0.98  
% 1.33/0.98  fof(f30,plain,(
% 1.33/0.98    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.33/0.98    inference(flattening,[],[f29])).
% 1.33/0.98  
% 1.33/0.98  fof(f31,plain,(
% 1.33/0.98    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.33/0.98    inference(rectify,[],[f30])).
% 1.33/0.98  
% 1.33/0.98  fof(f32,plain,(
% 1.33/0.98    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.33/0.98    introduced(choice_axiom,[])).
% 1.33/0.98  
% 1.33/0.98  fof(f33,plain,(
% 1.33/0.98    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1) & r2_hidden(sK0(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.33/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 1.33/0.98  
% 1.33/0.98  fof(f43,plain,(
% 1.33/0.98    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | r2_hidden(sK0(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.33/0.98    inference(cnf_transformation,[],[f33])).
% 1.33/0.98  
% 1.33/0.98  fof(f8,axiom,(
% 1.33/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.33/0.98  
% 1.33/0.98  fof(f50,plain,(
% 1.33/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.33/0.98    inference(cnf_transformation,[],[f8])).
% 1.33/0.98  
% 1.33/0.98  fof(f62,plain,(
% 1.33/0.98    ( ! [X0,X1] : (k6_partfun1(X0) = X1 | r2_hidden(sK0(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.33/0.98    inference(definition_unfolding,[],[f43,f50])).
% 1.33/0.98  
% 1.33/0.98  fof(f66,plain,(
% 1.33/0.98    ( ! [X1] : (k6_partfun1(k1_relat_1(X1)) = X1 | r2_hidden(sK0(k1_relat_1(X1),X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.33/0.98    inference(equality_resolution,[],[f62])).
% 1.33/0.98  
% 1.33/0.98  fof(f1,axiom,(
% 1.33/0.98    v1_xboole_0(k1_xboole_0)),
% 1.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.33/0.98  
% 1.33/0.98  fof(f39,plain,(
% 1.33/0.98    v1_xboole_0(k1_xboole_0)),
% 1.33/0.98    inference(cnf_transformation,[],[f1])).
% 1.33/0.98  
% 1.33/0.98  fof(f10,axiom,(
% 1.33/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.33/0.98  
% 1.33/0.98  fof(f25,plain,(
% 1.33/0.98    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.33/0.98    inference(ennf_transformation,[],[f10])).
% 1.33/0.98  
% 1.33/0.98  fof(f26,plain,(
% 1.33/0.98    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.33/0.98    inference(flattening,[],[f25])).
% 1.33/0.98  
% 1.33/0.98  fof(f53,plain,(
% 1.33/0.98    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.33/0.98    inference(cnf_transformation,[],[f26])).
% 1.33/0.98  
% 1.33/0.98  fof(f5,axiom,(
% 1.33/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.33/0.98  
% 1.33/0.98  fof(f13,plain,(
% 1.33/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.33/0.98    inference(pure_predicate_removal,[],[f5])).
% 1.33/0.98  
% 1.33/0.98  fof(f18,plain,(
% 1.33/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.98    inference(ennf_transformation,[],[f13])).
% 1.33/0.98  
% 1.33/0.98  fof(f46,plain,(
% 1.33/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.33/0.98    inference(cnf_transformation,[],[f18])).
% 1.33/0.98  
% 1.33/0.98  fof(f6,axiom,(
% 1.33/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.33/0.98  
% 1.33/0.98  fof(f19,plain,(
% 1.33/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.33/0.98    inference(ennf_transformation,[],[f6])).
% 1.33/0.98  
% 1.33/0.98  fof(f20,plain,(
% 1.33/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.33/0.98    inference(flattening,[],[f19])).
% 1.33/0.98  
% 1.33/0.98  fof(f34,plain,(
% 1.33/0.98    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.33/0.98    inference(nnf_transformation,[],[f20])).
% 1.33/0.98  
% 1.33/0.98  fof(f47,plain,(
% 1.33/0.98    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.33/0.98    inference(cnf_transformation,[],[f34])).
% 1.33/0.98  
% 1.33/0.98  fof(f59,plain,(
% 1.33/0.98    ( ! [X2] : (k3_funct_2(sK1,sK1,sK2,X2) = X2 | ~m1_subset_1(X2,sK1)) )),
% 1.33/0.98    inference(cnf_transformation,[],[f38])).
% 1.33/0.98  
% 1.33/0.98  fof(f9,axiom,(
% 1.33/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.33/0.98  
% 1.33/0.98  fof(f23,plain,(
% 1.33/0.98    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.33/0.98    inference(ennf_transformation,[],[f9])).
% 1.33/0.98  
% 1.33/0.98  fof(f24,plain,(
% 1.33/0.98    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.33/0.98    inference(flattening,[],[f23])).
% 1.33/0.98  
% 1.33/0.98  fof(f35,plain,(
% 1.33/0.98    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.33/0.98    inference(nnf_transformation,[],[f24])).
% 1.33/0.98  
% 1.33/0.98  fof(f52,plain,(
% 1.33/0.98    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.33/0.98    inference(cnf_transformation,[],[f35])).
% 1.33/0.98  
% 1.33/0.98  fof(f70,plain,(
% 1.33/0.98    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.33/0.98    inference(equality_resolution,[],[f52])).
% 1.33/0.98  
% 1.33/0.98  fof(f60,plain,(
% 1.33/0.98    ~r2_funct_2(sK1,sK1,sK2,k6_partfun1(sK1))),
% 1.33/0.98    inference(cnf_transformation,[],[f38])).
% 1.33/0.98  
% 1.33/0.98  fof(f44,plain,(
% 1.33/0.98    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.33/0.98    inference(cnf_transformation,[],[f33])).
% 1.33/0.98  
% 1.33/0.98  fof(f61,plain,(
% 1.33/0.98    ( ! [X0,X1] : (k6_partfun1(X0) = X1 | k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.33/0.98    inference(definition_unfolding,[],[f44,f50])).
% 1.33/0.98  
% 1.33/0.98  fof(f65,plain,(
% 1.33/0.98    ( ! [X1] : (k6_partfun1(k1_relat_1(X1)) = X1 | k1_funct_1(X1,sK0(k1_relat_1(X1),X1)) != sK0(k1_relat_1(X1),X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.33/0.98    inference(equality_resolution,[],[f61])).
% 1.33/0.98  
% 1.33/0.98  cnf(c_18,negated_conjecture,
% 1.33/0.98      ( v1_funct_2(sK2,sK1,sK1) ),
% 1.33/0.98      inference(cnf_transformation,[],[f57]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_10,plain,
% 1.33/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.33/0.98      | ~ m1_subset_1(X3,X1)
% 1.33/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.33/0.98      | ~ v1_funct_1(X0)
% 1.33/0.98      | v1_xboole_0(X1)
% 1.33/0.98      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 1.33/0.98      inference(cnf_transformation,[],[f49]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_20,negated_conjecture,
% 1.33/0.98      ( ~ v1_xboole_0(sK1) ),
% 1.33/0.98      inference(cnf_transformation,[],[f55]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_246,plain,
% 1.33/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.33/0.98      | ~ m1_subset_1(X3,X1)
% 1.33/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.33/0.98      | ~ v1_funct_1(X0)
% 1.33/0.98      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
% 1.33/0.98      | sK1 != X1 ),
% 1.33/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_247,plain,
% 1.33/0.98      ( ~ v1_funct_2(X0,sK1,X1)
% 1.33/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 1.33/0.98      | ~ m1_subset_1(X2,sK1)
% 1.33/0.98      | ~ v1_funct_1(X0)
% 1.33/0.98      | k3_funct_2(sK1,X1,X0,X2) = k1_funct_1(X0,X2) ),
% 1.33/0.98      inference(unflattening,[status(thm)],[c_246]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_547,plain,
% 1.33/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 1.33/0.98      | ~ m1_subset_1(X2,sK1)
% 1.33/0.98      | ~ v1_funct_1(X0)
% 1.33/0.98      | k3_funct_2(sK1,X1,X0,X2) = k1_funct_1(X0,X2)
% 1.33/0.98      | sK2 != X0
% 1.33/0.98      | sK1 != X1
% 1.33/0.98      | sK1 != sK1 ),
% 1.33/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_247]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_548,plain,
% 1.33/0.98      ( ~ m1_subset_1(X0,sK1)
% 1.33/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.33/0.98      | ~ v1_funct_1(sK2)
% 1.33/0.98      | k3_funct_2(sK1,sK1,sK2,X0) = k1_funct_1(sK2,X0) ),
% 1.33/0.98      inference(unflattening,[status(thm)],[c_547]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_19,negated_conjecture,
% 1.33/0.98      ( v1_funct_1(sK2) ),
% 1.33/0.98      inference(cnf_transformation,[],[f56]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_17,negated_conjecture,
% 1.33/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 1.33/0.98      inference(cnf_transformation,[],[f58]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_552,plain,
% 1.33/0.98      ( ~ m1_subset_1(X0,sK1)
% 1.33/0.98      | k3_funct_2(sK1,sK1,sK2,X0) = k1_funct_1(sK2,X0) ),
% 1.33/0.98      inference(global_propositional_subsumption,
% 1.33/0.98                [status(thm)],
% 1.33/0.98                [c_548,c_19,c_17]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_6,plain,
% 1.33/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 1.33/0.98      inference(cnf_transformation,[],[f45]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1,plain,
% 1.33/0.98      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 1.33/0.98      inference(cnf_transformation,[],[f40]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_3,plain,
% 1.33/0.98      ( r2_hidden(sK0(k1_relat_1(X0),X0),k1_relat_1(X0))
% 1.33/0.98      | ~ v1_relat_1(X0)
% 1.33/0.98      | ~ v1_funct_1(X0)
% 1.33/0.98      | k6_partfun1(k1_relat_1(X0)) = X0 ),
% 1.33/0.98      inference(cnf_transformation,[],[f66]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_590,plain,
% 1.33/0.98      ( r2_hidden(sK0(k1_relat_1(X0),X0),k1_relat_1(X0))
% 1.33/0.98      | ~ v1_relat_1(X0)
% 1.33/0.98      | k6_partfun1(k1_relat_1(X0)) = X0
% 1.33/0.98      | sK2 != X0 ),
% 1.33/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_19]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_591,plain,
% 1.33/0.98      ( r2_hidden(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
% 1.33/0.98      | ~ v1_relat_1(sK2)
% 1.33/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.33/0.98      inference(unflattening,[status(thm)],[c_590]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_682,plain,
% 1.33/0.98      ( m1_subset_1(X0,X1)
% 1.33/0.98      | ~ v1_relat_1(sK2)
% 1.33/0.98      | sK0(k1_relat_1(sK2),sK2) != X0
% 1.33/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.33/0.98      | k1_relat_1(sK2) != X1 ),
% 1.33/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_591]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_683,plain,
% 1.33/0.98      ( m1_subset_1(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
% 1.33/0.98      | ~ v1_relat_1(sK2)
% 1.33/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.33/0.98      inference(unflattening,[status(thm)],[c_682]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_714,plain,
% 1.33/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.33/0.98      | m1_subset_1(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
% 1.33/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.33/0.98      | sK2 != X0 ),
% 1.33/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_683]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_715,plain,
% 1.33/0.98      ( m1_subset_1(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
% 1.33/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.33/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.33/0.98      inference(unflattening,[status(thm)],[c_714]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_717,plain,
% 1.33/0.98      ( m1_subset_1(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
% 1.33/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.33/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.33/0.98      inference(instantiation,[status(thm)],[c_715]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_719,plain,
% 1.33/0.98      ( m1_subset_1(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
% 1.33/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.33/0.98      inference(global_propositional_subsumption,
% 1.33/0.98                [status(thm)],
% 1.33/0.98                [c_715,c_17,c_717]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_810,plain,
% 1.33/0.98      ( k3_funct_2(sK1,sK1,sK2,X0) = k1_funct_1(sK2,X0)
% 1.33/0.98      | sK0(k1_relat_1(sK2),sK2) != X0
% 1.33/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.33/0.98      | k1_relat_1(sK2) != sK1 ),
% 1.33/0.98      inference(resolution_lifted,[status(thm)],[c_552,c_719]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_811,plain,
% 1.33/0.98      ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2))
% 1.33/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.33/0.98      | k1_relat_1(sK2) != sK1 ),
% 1.33/0.98      inference(unflattening,[status(thm)],[c_810]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_0,plain,
% 1.33/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 1.33/0.98      inference(cnf_transformation,[],[f39]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_242,plain,
% 1.33/0.98      ( sK1 != k1_xboole_0 ),
% 1.33/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_20]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_14,plain,
% 1.33/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.33/0.98      | v1_partfun1(X0,X1)
% 1.33/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.33/0.98      | ~ v1_funct_1(X0)
% 1.33/0.98      | k1_xboole_0 = X2 ),
% 1.33/0.98      inference(cnf_transformation,[],[f53]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_7,plain,
% 1.33/0.98      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.33/0.98      inference(cnf_transformation,[],[f46]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_9,plain,
% 1.33/0.98      ( ~ v1_partfun1(X0,X1)
% 1.33/0.98      | ~ v4_relat_1(X0,X1)
% 1.33/0.98      | ~ v1_relat_1(X0)
% 1.33/0.98      | k1_relat_1(X0) = X1 ),
% 1.33/0.98      inference(cnf_transformation,[],[f47]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_274,plain,
% 1.33/0.98      ( ~ v1_partfun1(X0,X1)
% 1.33/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.33/0.98      | ~ v1_relat_1(X0)
% 1.33/0.98      | k1_relat_1(X0) = X1 ),
% 1.33/0.98      inference(resolution,[status(thm)],[c_7,c_9]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_278,plain,
% 1.33/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.33/0.98      | ~ v1_partfun1(X0,X1)
% 1.33/0.98      | k1_relat_1(X0) = X1 ),
% 1.33/0.98      inference(global_propositional_subsumption,
% 1.33/0.98                [status(thm)],
% 1.33/0.98                [c_274,c_9,c_7,c_6]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_279,plain,
% 1.33/0.98      ( ~ v1_partfun1(X0,X1)
% 1.33/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.33/0.98      | k1_relat_1(X0) = X1 ),
% 1.33/0.98      inference(renaming,[status(thm)],[c_278]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_393,plain,
% 1.33/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.33/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.33/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 1.33/0.98      | ~ v1_funct_1(X0)
% 1.33/0.98      | k1_relat_1(X0) = X1
% 1.33/0.98      | k1_xboole_0 = X2 ),
% 1.33/0.98      inference(resolution,[status(thm)],[c_14,c_279]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_397,plain,
% 1.33/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.33/0.98      | ~ v1_funct_2(X0,X1,X2)
% 1.33/0.98      | ~ v1_funct_1(X0)
% 1.33/0.98      | k1_relat_1(X0) = X1
% 1.33/0.98      | k1_xboole_0 = X2 ),
% 1.33/0.98      inference(global_propositional_subsumption,
% 1.33/0.98                [status(thm)],
% 1.33/0.98                [c_393,c_14,c_6,c_274]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_398,plain,
% 1.33/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.33/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.33/0.98      | ~ v1_funct_1(X0)
% 1.33/0.98      | k1_relat_1(X0) = X1
% 1.33/0.98      | k1_xboole_0 = X2 ),
% 1.33/0.98      inference(renaming,[status(thm)],[c_397]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_534,plain,
% 1.33/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.33/0.98      | ~ v1_funct_1(X0)
% 1.33/0.98      | k1_relat_1(X0) = X1
% 1.33/0.98      | sK2 != X0
% 1.33/0.98      | sK1 != X1
% 1.33/0.98      | sK1 != X2
% 1.33/0.98      | k1_xboole_0 = X2 ),
% 1.33/0.98      inference(resolution_lifted,[status(thm)],[c_398,c_18]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_535,plain,
% 1.33/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.33/0.98      | ~ v1_funct_1(sK2)
% 1.33/0.98      | k1_relat_1(sK2) = sK1
% 1.33/0.98      | k1_xboole_0 = sK1 ),
% 1.33/0.98      inference(unflattening,[status(thm)],[c_534]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_537,plain,
% 1.33/0.98      ( k1_relat_1(sK2) = sK1 | k1_xboole_0 = sK1 ),
% 1.33/0.98      inference(global_propositional_subsumption,
% 1.33/0.98                [status(thm)],
% 1.33/0.98                [c_535,c_19,c_17]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1052,plain,( X0 = X0 ),theory(equality) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1071,plain,
% 1.33/0.98      ( sK1 = sK1 ),
% 1.33/0.98      inference(instantiation,[status(thm)],[c_1052]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1053,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1220,plain,
% 1.33/0.98      ( sK1 != X0 | sK1 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 1.33/0.98      inference(instantiation,[status(thm)],[c_1053]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1221,plain,
% 1.33/0.98      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 1.33/0.98      inference(instantiation,[status(thm)],[c_1220]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1330,plain,
% 1.33/0.98      ( k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.33/0.98      | k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) ),
% 1.33/0.98      inference(global_propositional_subsumption,
% 1.33/0.98                [status(thm)],
% 1.33/0.98                [c_811,c_242,c_537,c_1071,c_1221]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1331,plain,
% 1.33/0.98      ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2))
% 1.33/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.33/0.98      inference(renaming,[status(thm)],[c_1330]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1228,plain,
% 1.33/0.98      ( k1_relat_1(sK2) = sK1 ),
% 1.33/0.98      inference(global_propositional_subsumption,
% 1.33/0.98                [status(thm)],
% 1.33/0.98                [c_537,c_242,c_1071,c_1221]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_16,negated_conjecture,
% 1.33/0.98      ( ~ m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK1,sK2,X0) = X0 ),
% 1.33/0.98      inference(cnf_transformation,[],[f59]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_821,plain,
% 1.33/0.98      ( k3_funct_2(sK1,sK1,sK2,X0) = X0
% 1.33/0.98      | sK0(k1_relat_1(sK2),sK2) != X0
% 1.33/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.33/0.98      | k1_relat_1(sK2) != sK1 ),
% 1.33/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_719]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_822,plain,
% 1.33/0.98      ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
% 1.33/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.33/0.98      | k1_relat_1(sK2) != sK1 ),
% 1.33/0.98      inference(unflattening,[status(thm)],[c_821]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1249,plain,
% 1.33/0.98      ( k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.33/0.98      | k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2) ),
% 1.33/0.98      inference(global_propositional_subsumption,
% 1.33/0.98                [status(thm)],
% 1.33/0.98                [c_822,c_242,c_537,c_1071,c_1221]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1250,plain,
% 1.33/0.98      ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
% 1.33/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.33/0.98      inference(renaming,[status(thm)],[c_1249]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1251,plain,
% 1.33/0.98      ( k3_funct_2(sK1,sK1,sK2,sK0(sK1,sK2)) = sK0(sK1,sK2)
% 1.33/0.98      | k6_partfun1(sK1) = sK2 ),
% 1.33/0.98      inference(light_normalisation,[status(thm)],[c_1250,c_1228]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_11,plain,
% 1.33/0.98      ( r2_funct_2(X0,X1,X2,X2)
% 1.33/0.98      | ~ v1_funct_2(X2,X0,X1)
% 1.33/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.33/0.98      | ~ v1_funct_1(X2) ),
% 1.33/0.98      inference(cnf_transformation,[],[f70]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_15,negated_conjecture,
% 1.33/0.98      ( ~ r2_funct_2(sK1,sK1,sK2,k6_partfun1(sK1)) ),
% 1.33/0.98      inference(cnf_transformation,[],[f60]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_372,plain,
% 1.33/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.33/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.33/0.98      | ~ v1_funct_1(X0)
% 1.33/0.98      | k6_partfun1(sK1) != X0
% 1.33/0.98      | sK2 != X0
% 1.33/0.98      | sK1 != X2
% 1.33/0.98      | sK1 != X1 ),
% 1.33/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_15]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_373,plain,
% 1.33/0.98      ( ~ v1_funct_2(k6_partfun1(sK1),sK1,sK1)
% 1.33/0.98      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.33/0.98      | ~ v1_funct_1(k6_partfun1(sK1))
% 1.33/0.98      | sK2 != k6_partfun1(sK1) ),
% 1.33/0.98      inference(unflattening,[status(thm)],[c_372]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_565,plain,
% 1.33/0.98      ( ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.33/0.98      | ~ v1_funct_1(k6_partfun1(sK1))
% 1.33/0.98      | k6_partfun1(sK1) != sK2
% 1.33/0.98      | sK1 != sK1 ),
% 1.33/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_373]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_647,plain,
% 1.33/0.98      ( ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.33/0.98      | k6_partfun1(sK1) != sK2
% 1.33/0.98      | sK1 != sK1 ),
% 1.33/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_565]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_832,plain,
% 1.33/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.33/0.98      | k6_partfun1(sK1) != sK2
% 1.33/0.98      | sK1 != sK1 ),
% 1.33/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_647]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_923,plain,
% 1.33/0.98      ( k6_partfun1(sK1) != sK2 ),
% 1.33/0.98      inference(equality_resolution_simp,[status(thm)],[c_832]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1254,plain,
% 1.33/0.98      ( k3_funct_2(sK1,sK1,sK2,sK0(sK1,sK2)) = sK0(sK1,sK2) ),
% 1.33/0.98      inference(global_propositional_subsumption,[status(thm)],[c_1251,c_923]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1332,plain,
% 1.33/0.98      ( k1_funct_1(sK2,sK0(sK1,sK2)) = sK0(sK1,sK2) | k6_partfun1(sK1) = sK2 ),
% 1.33/0.98      inference(light_normalisation,[status(thm)],[c_1331,c_1228,c_1254]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_2,plain,
% 1.33/0.98      ( ~ v1_relat_1(X0)
% 1.33/0.98      | ~ v1_funct_1(X0)
% 1.33/0.98      | k1_funct_1(X0,sK0(k1_relat_1(X0),X0)) != sK0(k1_relat_1(X0),X0)
% 1.33/0.98      | k6_partfun1(k1_relat_1(X0)) = X0 ),
% 1.33/0.98      inference(cnf_transformation,[],[f65]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_603,plain,
% 1.33/0.98      ( ~ v1_relat_1(X0)
% 1.33/0.98      | k1_funct_1(X0,sK0(k1_relat_1(X0),X0)) != sK0(k1_relat_1(X0),X0)
% 1.33/0.98      | k6_partfun1(k1_relat_1(X0)) = X0
% 1.33/0.98      | sK2 != X0 ),
% 1.33/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_19]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_604,plain,
% 1.33/0.98      ( ~ v1_relat_1(sK2)
% 1.33/0.98      | k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
% 1.33/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.33/0.98      inference(unflattening,[status(thm)],[c_603]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_730,plain,
% 1.33/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.33/0.98      | k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
% 1.33/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.33/0.98      | sK2 != X0 ),
% 1.33/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_604]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_731,plain,
% 1.33/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.33/0.98      | k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
% 1.33/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.33/0.98      inference(unflattening,[status(thm)],[c_730]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_733,plain,
% 1.33/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.33/0.98      | k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
% 1.33/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.33/0.98      inference(instantiation,[status(thm)],[c_731]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_735,plain,
% 1.33/0.98      ( k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
% 1.33/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.33/0.98      inference(global_propositional_subsumption,
% 1.33/0.98                [status(thm)],
% 1.33/0.98                [c_731,c_17,c_733]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1296,plain,
% 1.33/0.98      ( k1_funct_1(sK2,sK0(sK1,sK2)) != sK0(sK1,sK2) | k6_partfun1(sK1) = sK2 ),
% 1.33/0.98      inference(light_normalisation,[status(thm)],[c_735,c_1228]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1299,plain,
% 1.33/0.98      ( k1_funct_1(sK2,sK0(sK1,sK2)) != sK0(sK1,sK2) ),
% 1.33/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_1296,c_923]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1335,plain,
% 1.33/0.98      ( $false ),
% 1.33/0.98      inference(forward_subsumption_resolution,
% 1.33/0.98                [status(thm)],
% 1.33/0.98                [c_1332,c_923,c_1299]) ).
% 1.33/0.98  
% 1.33/0.98  
% 1.33/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.33/0.98  
% 1.33/0.98  ------                               Statistics
% 1.33/0.98  
% 1.33/0.98  ------ General
% 1.33/0.98  
% 1.33/0.98  abstr_ref_over_cycles:                  0
% 1.33/0.98  abstr_ref_under_cycles:                 0
% 1.33/0.98  gc_basic_clause_elim:                   0
% 1.33/0.98  forced_gc_time:                         0
% 1.33/0.98  parsing_time:                           0.008
% 1.33/0.98  unif_index_cands_time:                  0.
% 1.33/0.98  unif_index_add_time:                    0.
% 1.33/0.98  orderings_time:                         0.
% 1.33/0.98  out_proof_time:                         0.01
% 1.33/0.98  total_time:                             0.071
% 1.33/0.98  num_of_symbols:                         51
% 1.33/0.98  num_of_terms:                           1075
% 1.33/0.98  
% 1.33/0.98  ------ Preprocessing
% 1.33/0.98  
% 1.33/0.98  num_of_splits:                          1
% 1.33/0.98  num_of_split_atoms:                     1
% 1.33/0.98  num_of_reused_defs:                     0
% 1.33/0.98  num_eq_ax_congr_red:                    4
% 1.33/0.98  num_of_sem_filtered_clauses:            1
% 1.33/0.98  num_of_subtypes:                        0
% 1.33/0.98  monotx_restored_types:                  0
% 1.33/0.98  sat_num_of_epr_types:                   0
% 1.33/0.98  sat_num_of_non_cyclic_types:            0
% 1.33/0.98  sat_guarded_non_collapsed_types:        0
% 1.33/0.98  num_pure_diseq_elim:                    0
% 1.33/0.98  simp_replaced_by:                       0
% 1.33/0.98  res_preprocessed:                       88
% 1.33/0.98  prep_upred:                             0
% 1.33/0.98  prep_unflattend:                        43
% 1.33/0.98  smt_new_axioms:                         0
% 1.33/0.98  pred_elim_cands:                        1
% 1.33/0.98  pred_elim:                              8
% 1.33/0.98  pred_elim_cl:                           9
% 1.33/0.98  pred_elim_cycles:                       15
% 1.33/0.98  merged_defs:                            0
% 1.33/0.98  merged_defs_ncl:                        0
% 1.33/0.98  bin_hyper_res:                          0
% 1.33/0.98  prep_cycles:                            5
% 1.33/0.98  pred_elim_time:                         0.014
% 1.33/0.98  splitting_time:                         0.
% 1.33/0.98  sem_filter_time:                        0.
% 1.33/0.98  monotx_time:                            0.
% 1.33/0.98  subtype_inf_time:                       0.
% 1.33/0.98  
% 1.33/0.98  ------ Problem properties
% 1.33/0.98  
% 1.33/0.98  clauses:                                12
% 1.33/0.98  conjectures:                            0
% 1.33/0.98  epr:                                    1
% 1.33/0.98  horn:                                   8
% 1.33/0.98  ground:                                 9
% 1.33/0.98  unary:                                  2
% 1.33/0.98  binary:                                 6
% 1.33/0.98  lits:                                   26
% 1.33/0.98  lits_eq:                                21
% 1.33/0.98  fd_pure:                                0
% 1.33/0.98  fd_pseudo:                              0
% 1.33/0.98  fd_cond:                                0
% 1.33/0.98  fd_pseudo_cond:                         0
% 1.33/0.98  ac_symbols:                             0
% 1.33/0.98  
% 1.33/0.98  ------ Propositional Solver
% 1.33/0.98  
% 1.33/0.98  prop_solver_calls:                      29
% 1.33/0.98  prop_fast_solver_calls:                 627
% 1.33/0.98  smt_solver_calls:                       0
% 1.33/0.98  smt_fast_solver_calls:                  0
% 1.33/0.98  prop_num_of_clauses:                    276
% 1.33/0.98  prop_preprocess_simplified:             1788
% 1.33/0.98  prop_fo_subsumed:                       13
% 1.33/0.98  prop_solver_time:                       0.
% 1.33/0.98  smt_solver_time:                        0.
% 1.33/0.98  smt_fast_solver_time:                   0.
% 1.33/0.98  prop_fast_solver_time:                  0.
% 1.33/0.98  prop_unsat_core_time:                   0.
% 1.33/0.98  
% 1.33/0.98  ------ QBF
% 1.33/0.98  
% 1.33/0.98  qbf_q_res:                              0
% 1.33/0.98  qbf_num_tautologies:                    0
% 1.33/0.98  qbf_prep_cycles:                        0
% 1.33/0.98  
% 1.33/0.98  ------ BMC1
% 1.33/0.98  
% 1.33/0.98  bmc1_current_bound:                     -1
% 1.33/0.98  bmc1_last_solved_bound:                 -1
% 1.33/0.98  bmc1_unsat_core_size:                   -1
% 1.33/0.98  bmc1_unsat_core_parents_size:           -1
% 1.33/0.98  bmc1_merge_next_fun:                    0
% 1.33/0.98  bmc1_unsat_core_clauses_time:           0.
% 1.33/0.98  
% 1.33/0.98  ------ Instantiation
% 1.33/0.98  
% 1.33/0.98  inst_num_of_clauses:                    52
% 1.33/0.98  inst_num_in_passive:                    4
% 1.33/0.98  inst_num_in_active:                     42
% 1.33/0.98  inst_num_in_unprocessed:                6
% 1.33/0.98  inst_num_of_loops:                      50
% 1.33/0.98  inst_num_of_learning_restarts:          0
% 1.33/0.98  inst_num_moves_active_passive:          6
% 1.33/0.98  inst_lit_activity:                      0
% 1.33/0.98  inst_lit_activity_moves:                0
% 1.33/0.98  inst_num_tautologies:                   0
% 1.33/0.98  inst_num_prop_implied:                  0
% 1.33/0.98  inst_num_existing_simplified:           0
% 1.33/0.98  inst_num_eq_res_simplified:             0
% 1.33/0.98  inst_num_child_elim:                    0
% 1.33/0.98  inst_num_of_dismatching_blockings:      3
% 1.33/0.98  inst_num_of_non_proper_insts:           30
% 1.33/0.98  inst_num_of_duplicates:                 0
% 1.33/0.98  inst_inst_num_from_inst_to_res:         0
% 1.33/0.98  inst_dismatching_checking_time:         0.
% 1.33/0.98  
% 1.33/0.98  ------ Resolution
% 1.33/0.98  
% 1.33/0.98  res_num_of_clauses:                     0
% 1.33/0.98  res_num_in_passive:                     0
% 1.33/0.98  res_num_in_active:                      0
% 1.33/0.98  res_num_of_loops:                       93
% 1.33/0.98  res_forward_subset_subsumed:            17
% 1.33/0.98  res_backward_subset_subsumed:           0
% 1.33/0.98  res_forward_subsumed:                   0
% 1.33/0.98  res_backward_subsumed:                  2
% 1.33/0.98  res_forward_subsumption_resolution:     1
% 1.33/0.98  res_backward_subsumption_resolution:    0
% 1.33/0.98  res_clause_to_clause_subsumption:       23
% 1.33/0.98  res_orphan_elimination:                 0
% 1.33/0.98  res_tautology_del:                      7
% 1.33/0.98  res_num_eq_res_simplified:              2
% 1.33/0.98  res_num_sel_changes:                    0
% 1.33/0.98  res_moves_from_active_to_pass:          0
% 1.33/0.98  
% 1.33/0.98  ------ Superposition
% 1.33/0.98  
% 1.33/0.98  sup_time_total:                         0.
% 1.33/0.98  sup_time_generating:                    0.
% 1.33/0.98  sup_time_sim_full:                      0.
% 1.33/0.98  sup_time_sim_immed:                     0.
% 1.33/0.98  
% 1.33/0.98  sup_num_of_clauses:                     11
% 1.33/0.98  sup_num_in_active:                      8
% 1.33/0.98  sup_num_in_passive:                     3
% 1.33/0.98  sup_num_of_loops:                       8
% 1.33/0.98  sup_fw_superposition:                   0
% 1.33/0.98  sup_bw_superposition:                   0
% 1.33/0.98  sup_immediate_simplified:               0
% 1.33/0.98  sup_given_eliminated:                   0
% 1.33/0.98  comparisons_done:                       0
% 1.33/0.98  comparisons_avoided:                    0
% 1.33/0.98  
% 1.33/0.98  ------ Simplifications
% 1.33/0.98  
% 1.33/0.98  
% 1.33/0.98  sim_fw_subset_subsumed:                 0
% 1.33/0.98  sim_bw_subset_subsumed:                 0
% 1.33/0.98  sim_fw_subsumed:                        0
% 1.33/0.98  sim_bw_subsumed:                        0
% 1.33/0.98  sim_fw_subsumption_res:                 3
% 1.33/0.98  sim_bw_subsumption_res:                 0
% 1.33/0.98  sim_tautology_del:                      0
% 1.33/0.98  sim_eq_tautology_del:                   0
% 1.33/0.98  sim_eq_res_simp:                        0
% 1.33/0.98  sim_fw_demodulated:                     0
% 1.33/0.98  sim_bw_demodulated:                     0
% 1.33/0.98  sim_light_normalised:                   3
% 1.33/0.98  sim_joinable_taut:                      0
% 1.33/0.98  sim_joinable_simp:                      0
% 1.33/0.98  sim_ac_normalised:                      0
% 1.33/0.98  sim_smt_subsumption:                    0
% 1.33/0.98  
%------------------------------------------------------------------------------
