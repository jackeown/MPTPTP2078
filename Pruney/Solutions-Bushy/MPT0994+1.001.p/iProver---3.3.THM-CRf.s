%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0994+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:36 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 218 expanded)
%              Number of clauses        :   60 (  83 expanded)
%              Number of leaves         :    9 (  39 expanded)
%              Depth                    :   19
%              Number of atoms          :  311 (1067 expanded)
%              Number of equality atoms :  150 ( 351 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4) )
     => ( ( r2_hidden(k1_funct_1(X4,X2),X3)
          & r2_hidden(X2,X0) )
       => ( k1_funct_1(X4,X2) = k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X4,X0,X1)
          & v1_funct_1(X4) )
       => ( ( r2_hidden(k1_funct_1(X4,X2),X3)
            & r2_hidden(X2,X0) )
         => ( k1_funct_1(X4,X2) = k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f18,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k1_funct_1(X4,X2) != k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
      & k1_xboole_0 != X1
      & r2_hidden(k1_funct_1(X4,X2),X3)
      & r2_hidden(X2,X0)
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X4,X0,X1)
      & v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k1_funct_1(X4,X2) != k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
      & k1_xboole_0 != X1
      & r2_hidden(k1_funct_1(X4,X2),X3)
      & r2_hidden(X2,X0)
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X4,X0,X1)
      & v1_funct_1(X4) ) ),
    inference(flattening,[],[f18])).

fof(f23,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k1_funct_1(X4,X2) != k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
        & k1_xboole_0 != X1
        & r2_hidden(k1_funct_1(X4,X2),X3)
        & r2_hidden(X2,X0)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4) )
   => ( k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2)
      & k1_xboole_0 != sK1
      & r2_hidden(k1_funct_1(sK4,sK2),sK3)
      & r2_hidden(sK2,sK0)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK4,sK0,sK1)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2)
    & k1_xboole_0 != sK1
    & r2_hidden(k1_funct_1(sK4,sK2),sK3)
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK4,sK0,sK1)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f23])).

fof(f42,plain,(
    r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | ~ r2_hidden(k1_funct_1(X2,X0),X1)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f38,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f40,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f39,plain,(
    v1_funct_2(sK4,sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f43,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
       => k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,(
    k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_791,negated_conjecture,
    ( r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_963,plain,
    ( r2_hidden(k1_funct_1(sK4,sK2),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_791])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(X0,k1_relat_1(k8_relat_1(X2,X1)))
    | ~ r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_221,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(X0,k1_relat_1(k8_relat_1(X2,X1)))
    | ~ r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_222,plain,
    ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK4)))
    | ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ r2_hidden(k1_funct_1(sK4,X0),X1)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_221])).

cnf(c_788,plain,
    ( r2_hidden(X0_49,k1_relat_1(k8_relat_1(X0_46,sK4)))
    | ~ r2_hidden(X0_49,k1_relat_1(sK4))
    | ~ r2_hidden(k1_funct_1(sK4,X0_49),X0_46)
    | ~ v1_relat_1(sK4) ),
    inference(subtyping,[status(esa)],[c_222])).

cnf(c_966,plain,
    ( r2_hidden(X0_49,k1_relat_1(k8_relat_1(X0_46,sK4))) = iProver_top
    | r2_hidden(X0_49,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0_49),X0_46) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_788])).

cnf(c_830,plain,
    ( r2_hidden(X0_49,k1_relat_1(k8_relat_1(X0_46,sK4))) = iProver_top
    | r2_hidden(X0_49,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0_49),X0_46) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_788])).

cnf(c_796,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_1050,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_796])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_416,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_17])).

cnf(c_417,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_783,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(subtyping,[status(esa)],[c_417])).

cnf(c_1053,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_783])).

cnf(c_1054,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1053])).

cnf(c_1368,plain,
    ( r2_hidden(k1_funct_1(sK4,X0_49),X0_46) != iProver_top
    | r2_hidden(X0_49,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(X0_49,k1_relat_1(k8_relat_1(X0_46,sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_966,c_830,c_1050,c_1054])).

cnf(c_1369,plain,
    ( r2_hidden(X0_49,k1_relat_1(k8_relat_1(X0_46,sK4))) = iProver_top
    | r2_hidden(X0_49,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0_49),X0_46) != iProver_top ),
    inference(renaming,[status(thm)],[c_1368])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_371,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_372,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_784,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_relset_1(X0_46,X1_46,sK4) = k1_relat_1(sK4) ),
    inference(subtyping,[status(esa)],[c_372])).

cnf(c_1084,plain,
    ( k1_relset_1(sK0,sK1,sK4) = k1_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_784])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK4,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_380,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_17])).

cnf(c_381,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_608,plain,
    ( k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK1 != X1
    | sK0 != X0
    | sK4 != sK4
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_381])).

cnf(c_609,plain,
    ( k1_relset_1(sK0,sK1,sK4) = sK0
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_608])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_610,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_relset_1(sK0,sK1,sK4) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_609,c_14])).

cnf(c_611,plain,
    ( k1_relset_1(sK0,sK1,sK4) = sK0
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(renaming,[status(thm)],[c_610])).

cnf(c_667,plain,
    ( k1_relset_1(sK0,sK1,sK4) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_611])).

cnf(c_780,plain,
    ( k1_relset_1(sK0,sK1,sK4) = sK0 ),
    inference(subtyping,[status(esa)],[c_667])).

cnf(c_1156,plain,
    ( k1_relat_1(sK4) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_1084,c_780])).

cnf(c_1374,plain,
    ( r2_hidden(X0_49,k1_relat_1(k8_relat_1(X0_46,sK4))) = iProver_top
    | r2_hidden(X0_49,sK0) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0_49),X0_46) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1369,c_1156])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(k8_relat_1(X1,X2),X0) = k1_funct_1(X2,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_239,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
    | ~ v1_relat_1(X2)
    | k1_funct_1(k8_relat_1(X1,X2),X0) = k1_funct_1(X2,X0)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_240,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK4)))
    | ~ v1_relat_1(sK4)
    | k1_funct_1(k8_relat_1(X1,sK4),X0) = k1_funct_1(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_239])).

cnf(c_787,plain,
    ( ~ r2_hidden(X0_49,k1_relat_1(k8_relat_1(X0_46,sK4)))
    | ~ v1_relat_1(sK4)
    | k1_funct_1(k8_relat_1(X0_46,sK4),X0_49) = k1_funct_1(sK4,X0_49) ),
    inference(subtyping,[status(esa)],[c_240])).

cnf(c_967,plain,
    ( k1_funct_1(k8_relat_1(X0_46,sK4),X0_49) = k1_funct_1(sK4,X0_49)
    | r2_hidden(X0_49,k1_relat_1(k8_relat_1(X0_46,sK4))) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_787])).

cnf(c_833,plain,
    ( k1_funct_1(k8_relat_1(X0_46,sK4),X0_49) = k1_funct_1(sK4,X0_49)
    | r2_hidden(X0_49,k1_relat_1(k8_relat_1(X0_46,sK4))) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_787])).

cnf(c_1359,plain,
    ( r2_hidden(X0_49,k1_relat_1(k8_relat_1(X0_46,sK4))) != iProver_top
    | k1_funct_1(k8_relat_1(X0_46,sK4),X0_49) = k1_funct_1(sK4,X0_49) ),
    inference(global_propositional_subsumption,[status(thm)],[c_967,c_833,c_1050,c_1054])).

cnf(c_1360,plain,
    ( k1_funct_1(k8_relat_1(X0_46,sK4),X0_49) = k1_funct_1(sK4,X0_49)
    | r2_hidden(X0_49,k1_relat_1(k8_relat_1(X0_46,sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1359])).

cnf(c_1381,plain,
    ( k1_funct_1(k8_relat_1(X0_46,sK4),X0_49) = k1_funct_1(sK4,X0_49)
    | r2_hidden(X0_49,sK0) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0_49),X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_1374,c_1360])).

cnf(c_1429,plain,
    ( k1_funct_1(k8_relat_1(sK3,sK4),sK2) = k1_funct_1(sK4,sK2)
    | r2_hidden(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_963,c_1381])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_relset_1(X1,X2,X3,X0) = k8_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_362,plain,
    ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_17])).

cnf(c_363,plain,
    ( k6_relset_1(X0,X1,X2,sK4) = k8_relat_1(X2,sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_785,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k6_relset_1(X0_46,X1_46,X2_46,sK4) = k8_relat_1(X2_46,sK4) ),
    inference(subtyping,[status(esa)],[c_363])).

cnf(c_1087,plain,
    ( k6_relset_1(sK0,sK1,X0_46,sK4) = k8_relat_1(X0_46,sK4) ),
    inference(equality_resolution,[status(thm)],[c_785])).

cnf(c_13,negated_conjecture,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_793,negated_conjecture,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1203,plain,
    ( k1_funct_1(k8_relat_1(sK3,sK4),sK2) != k1_funct_1(sK4,sK2) ),
    inference(demodulation,[status(thm)],[c_1087,c_793])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_23,plain,
    ( r2_hidden(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1429,c_1203,c_23])).


%------------------------------------------------------------------------------
