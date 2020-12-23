%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:26 EST 2020

% Result     : Theorem 1.31s
% Output     : CNFRefutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 227 expanded)
%              Number of clauses        :   60 (  89 expanded)
%              Number of leaves         :   11 (  40 expanded)
%              Depth                    :   18
%              Number of atoms          :  317 ( 934 expanded)
%              Number of equality atoms :  126 ( 225 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => ( r2_hidden(k1_funct_1(X3,X2),X1)
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f28,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
        & k1_xboole_0 != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ~ r2_hidden(k1_funct_1(sK3,sK2),sK1)
      & k1_xboole_0 != sK1
      & r2_hidden(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),sK1)
    & k1_xboole_0 != sK1
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f28])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
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
    inference(ennf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X2,X0),X1)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f49,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_8,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_237,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_8,c_2])).

cnf(c_4,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_256,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X2)) = X0 ),
    inference(resolution,[status(thm)],[c_237,c_4])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_350,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_256,c_19])).

cnf(c_351,plain,
    ( ~ v1_relat_1(sK3)
    | k5_relat_1(sK3,k6_relat_1(X0)) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_350])).

cnf(c_637,plain,
    ( ~ v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k5_relat_1(sK3,k6_relat_1(X1_48)) = sK3 ),
    inference(subtyping,[status(esa)],[c_351])).

cnf(c_830,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k5_relat_1(sK3,k6_relat_1(X1_48)) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_637])).

cnf(c_648,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_917,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_648])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_335,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_19])).

cnf(c_336,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_335])).

cnf(c_638,plain,
    ( ~ v1_relat_1(X0_48)
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_336])).

cnf(c_912,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0_48,X1_48))
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)) ),
    inference(instantiation,[status(thm)],[c_638])).

cnf(c_973,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_912])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_645,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_48,X1_48)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1016,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_645])).

cnf(c_1153,plain,
    ( k5_relat_1(sK3,k6_relat_1(X1_48)) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_830,c_637,c_917,c_973,c_1016])).

cnf(c_1154,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k5_relat_1(sK3,k6_relat_1(X1_48)) = sK3 ),
    inference(renaming,[status(thm)],[c_1153])).

cnf(c_1158,plain,
    ( k5_relat_1(sK3,k6_relat_1(sK1)) = sK3 ),
    inference(equality_resolution,[status(thm)],[c_1154])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_289,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_21])).

cnf(c_290,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK3,k6_relat_1(X1))))
    | r2_hidden(k1_funct_1(sK3,X0),X1)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_289])).

cnf(c_640,plain,
    ( ~ r2_hidden(X0_51,k1_relat_1(k5_relat_1(sK3,k6_relat_1(X0_48))))
    | r2_hidden(k1_funct_1(sK3,X0_51),X0_48)
    | ~ v1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_290])).

cnf(c_827,plain,
    ( r2_hidden(X0_51,k1_relat_1(k5_relat_1(sK3,k6_relat_1(X0_48)))) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0_51),X0_48) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_640])).

cnf(c_680,plain,
    ( r2_hidden(X0_51,k1_relat_1(k5_relat_1(sK3,k6_relat_1(X0_48)))) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0_51),X0_48) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_640])).

cnf(c_974,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_973])).

cnf(c_1017,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1016])).

cnf(c_1160,plain,
    ( r2_hidden(k1_funct_1(sK3,X0_51),X0_48) = iProver_top
    | r2_hidden(X0_51,k1_relat_1(k5_relat_1(sK3,k6_relat_1(X0_48)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_827,c_680,c_917,c_974,c_1017])).

cnf(c_1161,plain,
    ( r2_hidden(X0_51,k1_relat_1(k5_relat_1(sK3,k6_relat_1(X0_48)))) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0_51),X0_48) = iProver_top ),
    inference(renaming,[status(thm)],[c_1160])).

cnf(c_1218,plain,
    ( r2_hidden(X0_51,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0_51),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1158,c_1161])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_401,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_402,plain,
    ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_401])).

cnf(c_636,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_relset_1(X0_48,X1_48,sK3) = k1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_402])).

cnf(c_930,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_636])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_365,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_366,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_521,plain,
    ( k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK0 != X0
    | sK1 != X1
    | sK3 != sK3
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_366])).

cnf(c_522,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_521])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_523,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_relset_1(sK0,sK1,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_522,c_17])).

cnf(c_524,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(renaming,[status(thm)],[c_523])).

cnf(c_581,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_524])).

cnf(c_633,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0 ),
    inference(subtyping,[status(esa)],[c_581])).

cnf(c_996,plain,
    ( k1_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_930,c_633])).

cnf(c_1225,plain,
    ( r2_hidden(X0_51,sK0) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0_51),sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1218,c_996])).

cnf(c_1234,plain,
    ( r2_hidden(k1_funct_1(sK3,sK2),sK1) = iProver_top
    | r2_hidden(sK2,sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1225])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_26,plain,
    ( r2_hidden(k1_funct_1(sK3,sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_25,plain,
    ( r2_hidden(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1234,c_26,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 21:00:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.31/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.31/0.98  
% 1.31/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.31/0.98  
% 1.31/0.98  ------  iProver source info
% 1.31/0.98  
% 1.31/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.31/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.31/0.98  git: non_committed_changes: false
% 1.31/0.98  git: last_make_outside_of_git: false
% 1.31/0.98  
% 1.31/0.98  ------ 
% 1.31/0.98  
% 1.31/0.98  ------ Input Options
% 1.31/0.98  
% 1.31/0.98  --out_options                           all
% 1.31/0.98  --tptp_safe_out                         true
% 1.31/0.98  --problem_path                          ""
% 1.31/0.98  --include_path                          ""
% 1.31/0.98  --clausifier                            res/vclausify_rel
% 1.31/0.98  --clausifier_options                    --mode clausify
% 1.31/0.98  --stdin                                 false
% 1.31/0.98  --stats_out                             all
% 1.31/0.98  
% 1.31/0.98  ------ General Options
% 1.31/0.98  
% 1.31/0.98  --fof                                   false
% 1.31/0.98  --time_out_real                         305.
% 1.31/0.98  --time_out_virtual                      -1.
% 1.31/0.98  --symbol_type_check                     false
% 1.31/0.98  --clausify_out                          false
% 1.31/0.98  --sig_cnt_out                           false
% 1.31/0.98  --trig_cnt_out                          false
% 1.31/0.98  --trig_cnt_out_tolerance                1.
% 1.31/0.98  --trig_cnt_out_sk_spl                   false
% 1.31/0.98  --abstr_cl_out                          false
% 1.31/0.98  
% 1.31/0.98  ------ Global Options
% 1.31/0.98  
% 1.31/0.98  --schedule                              default
% 1.31/0.98  --add_important_lit                     false
% 1.31/0.98  --prop_solver_per_cl                    1000
% 1.31/0.98  --min_unsat_core                        false
% 1.31/0.98  --soft_assumptions                      false
% 1.31/0.98  --soft_lemma_size                       3
% 1.31/0.98  --prop_impl_unit_size                   0
% 1.31/0.98  --prop_impl_unit                        []
% 1.31/0.98  --share_sel_clauses                     true
% 1.31/0.98  --reset_solvers                         false
% 1.31/0.98  --bc_imp_inh                            [conj_cone]
% 1.31/0.98  --conj_cone_tolerance                   3.
% 1.31/0.98  --extra_neg_conj                        none
% 1.31/0.98  --large_theory_mode                     true
% 1.31/0.98  --prolific_symb_bound                   200
% 1.31/0.98  --lt_threshold                          2000
% 1.31/0.98  --clause_weak_htbl                      true
% 1.31/0.98  --gc_record_bc_elim                     false
% 1.31/0.98  
% 1.31/0.98  ------ Preprocessing Options
% 1.31/0.98  
% 1.31/0.98  --preprocessing_flag                    true
% 1.31/0.98  --time_out_prep_mult                    0.1
% 1.31/0.98  --splitting_mode                        input
% 1.31/0.98  --splitting_grd                         true
% 1.31/0.98  --splitting_cvd                         false
% 1.31/0.98  --splitting_cvd_svl                     false
% 1.31/0.98  --splitting_nvd                         32
% 1.31/0.98  --sub_typing                            true
% 1.31/0.98  --prep_gs_sim                           true
% 1.31/0.98  --prep_unflatten                        true
% 1.31/0.98  --prep_res_sim                          true
% 1.31/0.98  --prep_upred                            true
% 1.31/0.98  --prep_sem_filter                       exhaustive
% 1.31/0.98  --prep_sem_filter_out                   false
% 1.31/0.98  --pred_elim                             true
% 1.31/0.98  --res_sim_input                         true
% 1.31/0.98  --eq_ax_congr_red                       true
% 1.31/0.98  --pure_diseq_elim                       true
% 1.31/0.98  --brand_transform                       false
% 1.31/0.98  --non_eq_to_eq                          false
% 1.31/0.98  --prep_def_merge                        true
% 1.31/0.98  --prep_def_merge_prop_impl              false
% 1.31/0.98  --prep_def_merge_mbd                    true
% 1.31/0.98  --prep_def_merge_tr_red                 false
% 1.31/0.98  --prep_def_merge_tr_cl                  false
% 1.31/0.98  --smt_preprocessing                     true
% 1.31/0.98  --smt_ac_axioms                         fast
% 1.31/0.98  --preprocessed_out                      false
% 1.31/0.98  --preprocessed_stats                    false
% 1.31/0.98  
% 1.31/0.98  ------ Abstraction refinement Options
% 1.31/0.98  
% 1.31/0.98  --abstr_ref                             []
% 1.31/0.98  --abstr_ref_prep                        false
% 1.31/0.98  --abstr_ref_until_sat                   false
% 1.31/0.98  --abstr_ref_sig_restrict                funpre
% 1.31/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.31/0.98  --abstr_ref_under                       []
% 1.31/0.98  
% 1.31/0.98  ------ SAT Options
% 1.31/0.98  
% 1.31/0.98  --sat_mode                              false
% 1.31/0.98  --sat_fm_restart_options                ""
% 1.31/0.98  --sat_gr_def                            false
% 1.31/0.98  --sat_epr_types                         true
% 1.31/0.98  --sat_non_cyclic_types                  false
% 1.31/0.98  --sat_finite_models                     false
% 1.31/0.98  --sat_fm_lemmas                         false
% 1.31/0.98  --sat_fm_prep                           false
% 1.31/0.98  --sat_fm_uc_incr                        true
% 1.31/0.98  --sat_out_model                         small
% 1.31/0.98  --sat_out_clauses                       false
% 1.31/0.98  
% 1.31/0.98  ------ QBF Options
% 1.31/0.98  
% 1.31/0.98  --qbf_mode                              false
% 1.31/0.98  --qbf_elim_univ                         false
% 1.31/0.98  --qbf_dom_inst                          none
% 1.31/0.98  --qbf_dom_pre_inst                      false
% 1.31/0.98  --qbf_sk_in                             false
% 1.31/0.98  --qbf_pred_elim                         true
% 1.31/0.98  --qbf_split                             512
% 1.31/0.98  
% 1.31/0.98  ------ BMC1 Options
% 1.31/0.98  
% 1.31/0.98  --bmc1_incremental                      false
% 1.31/0.98  --bmc1_axioms                           reachable_all
% 1.31/0.98  --bmc1_min_bound                        0
% 1.31/0.98  --bmc1_max_bound                        -1
% 1.31/0.98  --bmc1_max_bound_default                -1
% 1.31/0.98  --bmc1_symbol_reachability              true
% 1.31/0.98  --bmc1_property_lemmas                  false
% 1.31/0.98  --bmc1_k_induction                      false
% 1.31/0.98  --bmc1_non_equiv_states                 false
% 1.31/0.98  --bmc1_deadlock                         false
% 1.31/0.98  --bmc1_ucm                              false
% 1.31/0.98  --bmc1_add_unsat_core                   none
% 1.31/0.98  --bmc1_unsat_core_children              false
% 1.31/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.31/0.98  --bmc1_out_stat                         full
% 1.31/0.98  --bmc1_ground_init                      false
% 1.31/0.98  --bmc1_pre_inst_next_state              false
% 1.31/0.98  --bmc1_pre_inst_state                   false
% 1.31/0.98  --bmc1_pre_inst_reach_state             false
% 1.31/0.98  --bmc1_out_unsat_core                   false
% 1.31/0.98  --bmc1_aig_witness_out                  false
% 1.31/0.98  --bmc1_verbose                          false
% 1.31/0.98  --bmc1_dump_clauses_tptp                false
% 1.31/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.31/0.98  --bmc1_dump_file                        -
% 1.31/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.31/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.31/0.98  --bmc1_ucm_extend_mode                  1
% 1.31/0.98  --bmc1_ucm_init_mode                    2
% 1.31/0.98  --bmc1_ucm_cone_mode                    none
% 1.31/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.31/0.98  --bmc1_ucm_relax_model                  4
% 1.31/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.31/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.31/0.98  --bmc1_ucm_layered_model                none
% 1.31/0.98  --bmc1_ucm_max_lemma_size               10
% 1.31/0.98  
% 1.31/0.98  ------ AIG Options
% 1.31/0.98  
% 1.31/0.98  --aig_mode                              false
% 1.31/0.98  
% 1.31/0.98  ------ Instantiation Options
% 1.31/0.98  
% 1.31/0.98  --instantiation_flag                    true
% 1.31/0.98  --inst_sos_flag                         false
% 1.31/0.98  --inst_sos_phase                        true
% 1.31/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.31/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.31/0.98  --inst_lit_sel_side                     num_symb
% 1.31/0.98  --inst_solver_per_active                1400
% 1.31/0.98  --inst_solver_calls_frac                1.
% 1.31/0.98  --inst_passive_queue_type               priority_queues
% 1.31/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.31/0.98  --inst_passive_queues_freq              [25;2]
% 1.31/0.98  --inst_dismatching                      true
% 1.31/0.98  --inst_eager_unprocessed_to_passive     true
% 1.31/0.98  --inst_prop_sim_given                   true
% 1.31/0.98  --inst_prop_sim_new                     false
% 1.31/0.98  --inst_subs_new                         false
% 1.31/0.98  --inst_eq_res_simp                      false
% 1.31/0.98  --inst_subs_given                       false
% 1.31/0.98  --inst_orphan_elimination               true
% 1.31/0.98  --inst_learning_loop_flag               true
% 1.31/0.98  --inst_learning_start                   3000
% 1.31/0.98  --inst_learning_factor                  2
% 1.31/0.98  --inst_start_prop_sim_after_learn       3
% 1.31/0.98  --inst_sel_renew                        solver
% 1.31/0.98  --inst_lit_activity_flag                true
% 1.31/0.98  --inst_restr_to_given                   false
% 1.31/0.98  --inst_activity_threshold               500
% 1.31/0.98  --inst_out_proof                        true
% 1.31/0.98  
% 1.31/0.98  ------ Resolution Options
% 1.31/0.98  
% 1.31/0.98  --resolution_flag                       true
% 1.31/0.98  --res_lit_sel                           adaptive
% 1.31/0.98  --res_lit_sel_side                      none
% 1.31/0.98  --res_ordering                          kbo
% 1.31/0.98  --res_to_prop_solver                    active
% 1.31/0.98  --res_prop_simpl_new                    false
% 1.31/0.98  --res_prop_simpl_given                  true
% 1.31/0.98  --res_passive_queue_type                priority_queues
% 1.31/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.31/0.98  --res_passive_queues_freq               [15;5]
% 1.31/0.98  --res_forward_subs                      full
% 1.31/0.98  --res_backward_subs                     full
% 1.31/0.98  --res_forward_subs_resolution           true
% 1.31/0.98  --res_backward_subs_resolution          true
% 1.31/0.98  --res_orphan_elimination                true
% 1.31/0.98  --res_time_limit                        2.
% 1.31/0.98  --res_out_proof                         true
% 1.31/0.98  
% 1.31/0.98  ------ Superposition Options
% 1.31/0.98  
% 1.31/0.98  --superposition_flag                    true
% 1.31/0.98  --sup_passive_queue_type                priority_queues
% 1.31/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.31/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.31/0.98  --demod_completeness_check              fast
% 1.31/0.98  --demod_use_ground                      true
% 1.31/0.98  --sup_to_prop_solver                    passive
% 1.31/0.98  --sup_prop_simpl_new                    true
% 1.31/0.98  --sup_prop_simpl_given                  true
% 1.31/0.98  --sup_fun_splitting                     false
% 1.31/0.98  --sup_smt_interval                      50000
% 1.31/0.98  
% 1.31/0.98  ------ Superposition Simplification Setup
% 1.31/0.98  
% 1.31/0.98  --sup_indices_passive                   []
% 1.31/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.31/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.31/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.31/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.31/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.31/0.98  --sup_full_bw                           [BwDemod]
% 1.31/0.98  --sup_immed_triv                        [TrivRules]
% 1.31/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.31/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.31/0.98  --sup_immed_bw_main                     []
% 1.31/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.31/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.31/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.31/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.31/0.98  
% 1.31/0.98  ------ Combination Options
% 1.31/0.98  
% 1.31/0.98  --comb_res_mult                         3
% 1.31/0.98  --comb_sup_mult                         2
% 1.31/0.98  --comb_inst_mult                        10
% 1.31/0.98  
% 1.31/0.98  ------ Debug Options
% 1.31/0.98  
% 1.31/0.98  --dbg_backtrace                         false
% 1.31/0.98  --dbg_dump_prop_clauses                 false
% 1.31/0.98  --dbg_dump_prop_clauses_file            -
% 1.31/0.98  --dbg_out_stat                          false
% 1.31/0.98  ------ Parsing...
% 1.31/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.31/0.98  
% 1.31/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.31/0.98  
% 1.31/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.31/0.98  
% 1.31/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.31/0.98  ------ Proving...
% 1.31/0.98  ------ Problem Properties 
% 1.31/0.98  
% 1.31/0.98  
% 1.31/0.98  clauses                                 13
% 1.31/0.98  conjectures                             3
% 1.31/0.98  EPR                                     2
% 1.31/0.98  Horn                                    12
% 1.31/0.98  unary                                   5
% 1.31/0.98  binary                                  1
% 1.31/0.98  lits                                    30
% 1.31/0.98  lits eq                                 14
% 1.31/0.98  fd_pure                                 0
% 1.31/0.98  fd_pseudo                               0
% 1.31/0.98  fd_cond                                 0
% 1.31/0.98  fd_pseudo_cond                          0
% 1.31/0.98  AC symbols                              0
% 1.31/0.98  
% 1.31/0.98  ------ Schedule dynamic 5 is on 
% 1.31/0.98  
% 1.31/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.31/0.98  
% 1.31/0.98  
% 1.31/0.98  ------ 
% 1.31/0.98  Current options:
% 1.31/0.98  ------ 
% 1.31/0.98  
% 1.31/0.98  ------ Input Options
% 1.31/0.98  
% 1.31/0.98  --out_options                           all
% 1.31/0.98  --tptp_safe_out                         true
% 1.31/0.98  --problem_path                          ""
% 1.31/0.98  --include_path                          ""
% 1.31/0.98  --clausifier                            res/vclausify_rel
% 1.31/0.98  --clausifier_options                    --mode clausify
% 1.31/0.98  --stdin                                 false
% 1.31/0.98  --stats_out                             all
% 1.31/0.98  
% 1.31/0.98  ------ General Options
% 1.31/0.98  
% 1.31/0.98  --fof                                   false
% 1.31/0.98  --time_out_real                         305.
% 1.31/0.98  --time_out_virtual                      -1.
% 1.31/0.98  --symbol_type_check                     false
% 1.31/0.98  --clausify_out                          false
% 1.31/0.98  --sig_cnt_out                           false
% 1.31/0.98  --trig_cnt_out                          false
% 1.31/0.98  --trig_cnt_out_tolerance                1.
% 1.31/0.98  --trig_cnt_out_sk_spl                   false
% 1.31/0.98  --abstr_cl_out                          false
% 1.31/0.98  
% 1.31/0.98  ------ Global Options
% 1.31/0.98  
% 1.31/0.98  --schedule                              default
% 1.31/0.98  --add_important_lit                     false
% 1.31/0.98  --prop_solver_per_cl                    1000
% 1.31/0.98  --min_unsat_core                        false
% 1.31/0.98  --soft_assumptions                      false
% 1.31/0.98  --soft_lemma_size                       3
% 1.31/0.98  --prop_impl_unit_size                   0
% 1.31/0.98  --prop_impl_unit                        []
% 1.31/0.98  --share_sel_clauses                     true
% 1.31/0.98  --reset_solvers                         false
% 1.31/0.98  --bc_imp_inh                            [conj_cone]
% 1.31/0.98  --conj_cone_tolerance                   3.
% 1.31/0.98  --extra_neg_conj                        none
% 1.31/0.98  --large_theory_mode                     true
% 1.31/0.98  --prolific_symb_bound                   200
% 1.31/0.98  --lt_threshold                          2000
% 1.31/0.98  --clause_weak_htbl                      true
% 1.31/0.98  --gc_record_bc_elim                     false
% 1.31/0.98  
% 1.31/0.98  ------ Preprocessing Options
% 1.31/0.98  
% 1.31/0.98  --preprocessing_flag                    true
% 1.31/0.98  --time_out_prep_mult                    0.1
% 1.31/0.98  --splitting_mode                        input
% 1.31/0.98  --splitting_grd                         true
% 1.31/0.98  --splitting_cvd                         false
% 1.31/0.98  --splitting_cvd_svl                     false
% 1.31/0.98  --splitting_nvd                         32
% 1.31/0.98  --sub_typing                            true
% 1.31/0.98  --prep_gs_sim                           true
% 1.31/0.98  --prep_unflatten                        true
% 1.31/0.98  --prep_res_sim                          true
% 1.31/0.98  --prep_upred                            true
% 1.31/0.98  --prep_sem_filter                       exhaustive
% 1.31/0.98  --prep_sem_filter_out                   false
% 1.31/0.98  --pred_elim                             true
% 1.31/0.98  --res_sim_input                         true
% 1.31/0.98  --eq_ax_congr_red                       true
% 1.31/0.98  --pure_diseq_elim                       true
% 1.31/0.98  --brand_transform                       false
% 1.31/0.98  --non_eq_to_eq                          false
% 1.31/0.98  --prep_def_merge                        true
% 1.31/0.98  --prep_def_merge_prop_impl              false
% 1.31/0.98  --prep_def_merge_mbd                    true
% 1.31/0.98  --prep_def_merge_tr_red                 false
% 1.31/0.98  --prep_def_merge_tr_cl                  false
% 1.31/0.98  --smt_preprocessing                     true
% 1.31/0.98  --smt_ac_axioms                         fast
% 1.31/0.98  --preprocessed_out                      false
% 1.31/0.98  --preprocessed_stats                    false
% 1.31/0.98  
% 1.31/0.98  ------ Abstraction refinement Options
% 1.31/0.98  
% 1.31/0.98  --abstr_ref                             []
% 1.31/0.98  --abstr_ref_prep                        false
% 1.31/0.98  --abstr_ref_until_sat                   false
% 1.31/0.98  --abstr_ref_sig_restrict                funpre
% 1.31/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.31/0.98  --abstr_ref_under                       []
% 1.31/0.98  
% 1.31/0.98  ------ SAT Options
% 1.31/0.98  
% 1.31/0.98  --sat_mode                              false
% 1.31/0.98  --sat_fm_restart_options                ""
% 1.31/0.98  --sat_gr_def                            false
% 1.31/0.98  --sat_epr_types                         true
% 1.31/0.98  --sat_non_cyclic_types                  false
% 1.31/0.98  --sat_finite_models                     false
% 1.31/0.98  --sat_fm_lemmas                         false
% 1.31/0.98  --sat_fm_prep                           false
% 1.31/0.98  --sat_fm_uc_incr                        true
% 1.31/0.98  --sat_out_model                         small
% 1.31/0.98  --sat_out_clauses                       false
% 1.31/0.98  
% 1.31/0.98  ------ QBF Options
% 1.31/0.98  
% 1.31/0.98  --qbf_mode                              false
% 1.31/0.98  --qbf_elim_univ                         false
% 1.31/0.98  --qbf_dom_inst                          none
% 1.31/0.98  --qbf_dom_pre_inst                      false
% 1.31/0.98  --qbf_sk_in                             false
% 1.31/0.98  --qbf_pred_elim                         true
% 1.31/0.98  --qbf_split                             512
% 1.31/0.98  
% 1.31/0.98  ------ BMC1 Options
% 1.31/0.98  
% 1.31/0.98  --bmc1_incremental                      false
% 1.31/0.98  --bmc1_axioms                           reachable_all
% 1.31/0.98  --bmc1_min_bound                        0
% 1.31/0.98  --bmc1_max_bound                        -1
% 1.31/0.98  --bmc1_max_bound_default                -1
% 1.31/0.98  --bmc1_symbol_reachability              true
% 1.31/0.98  --bmc1_property_lemmas                  false
% 1.31/0.98  --bmc1_k_induction                      false
% 1.31/0.98  --bmc1_non_equiv_states                 false
% 1.31/0.98  --bmc1_deadlock                         false
% 1.31/0.98  --bmc1_ucm                              false
% 1.31/0.98  --bmc1_add_unsat_core                   none
% 1.31/0.98  --bmc1_unsat_core_children              false
% 1.31/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.31/0.98  --bmc1_out_stat                         full
% 1.31/0.98  --bmc1_ground_init                      false
% 1.31/0.98  --bmc1_pre_inst_next_state              false
% 1.31/0.98  --bmc1_pre_inst_state                   false
% 1.31/0.98  --bmc1_pre_inst_reach_state             false
% 1.31/0.98  --bmc1_out_unsat_core                   false
% 1.31/0.98  --bmc1_aig_witness_out                  false
% 1.31/0.98  --bmc1_verbose                          false
% 1.31/0.98  --bmc1_dump_clauses_tptp                false
% 1.31/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.31/0.98  --bmc1_dump_file                        -
% 1.31/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.31/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.31/0.98  --bmc1_ucm_extend_mode                  1
% 1.31/0.98  --bmc1_ucm_init_mode                    2
% 1.31/0.98  --bmc1_ucm_cone_mode                    none
% 1.31/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.31/0.98  --bmc1_ucm_relax_model                  4
% 1.31/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.31/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.31/0.98  --bmc1_ucm_layered_model                none
% 1.31/0.98  --bmc1_ucm_max_lemma_size               10
% 1.31/0.98  
% 1.31/0.98  ------ AIG Options
% 1.31/0.98  
% 1.31/0.98  --aig_mode                              false
% 1.31/0.98  
% 1.31/0.98  ------ Instantiation Options
% 1.31/0.98  
% 1.31/0.98  --instantiation_flag                    true
% 1.31/0.98  --inst_sos_flag                         false
% 1.31/0.98  --inst_sos_phase                        true
% 1.31/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.31/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.31/0.98  --inst_lit_sel_side                     none
% 1.31/0.98  --inst_solver_per_active                1400
% 1.31/0.98  --inst_solver_calls_frac                1.
% 1.31/0.98  --inst_passive_queue_type               priority_queues
% 1.31/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.31/0.98  --inst_passive_queues_freq              [25;2]
% 1.31/0.98  --inst_dismatching                      true
% 1.31/0.98  --inst_eager_unprocessed_to_passive     true
% 1.31/0.98  --inst_prop_sim_given                   true
% 1.31/0.98  --inst_prop_sim_new                     false
% 1.31/0.98  --inst_subs_new                         false
% 1.31/0.98  --inst_eq_res_simp                      false
% 1.31/0.98  --inst_subs_given                       false
% 1.31/0.98  --inst_orphan_elimination               true
% 1.31/0.98  --inst_learning_loop_flag               true
% 1.31/0.98  --inst_learning_start                   3000
% 1.31/0.98  --inst_learning_factor                  2
% 1.31/0.98  --inst_start_prop_sim_after_learn       3
% 1.31/0.98  --inst_sel_renew                        solver
% 1.31/0.98  --inst_lit_activity_flag                true
% 1.31/0.98  --inst_restr_to_given                   false
% 1.31/0.98  --inst_activity_threshold               500
% 1.31/0.98  --inst_out_proof                        true
% 1.31/0.98  
% 1.31/0.98  ------ Resolution Options
% 1.31/0.98  
% 1.31/0.98  --resolution_flag                       false
% 1.31/0.98  --res_lit_sel                           adaptive
% 1.31/0.98  --res_lit_sel_side                      none
% 1.31/0.98  --res_ordering                          kbo
% 1.31/0.98  --res_to_prop_solver                    active
% 1.31/0.98  --res_prop_simpl_new                    false
% 1.31/0.98  --res_prop_simpl_given                  true
% 1.31/0.98  --res_passive_queue_type                priority_queues
% 1.31/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.31/0.98  --res_passive_queues_freq               [15;5]
% 1.31/0.98  --res_forward_subs                      full
% 1.31/0.98  --res_backward_subs                     full
% 1.31/0.98  --res_forward_subs_resolution           true
% 1.31/0.98  --res_backward_subs_resolution          true
% 1.31/0.98  --res_orphan_elimination                true
% 1.31/0.98  --res_time_limit                        2.
% 1.31/0.98  --res_out_proof                         true
% 1.31/0.98  
% 1.31/0.98  ------ Superposition Options
% 1.31/0.98  
% 1.31/0.98  --superposition_flag                    true
% 1.31/0.98  --sup_passive_queue_type                priority_queues
% 1.31/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.31/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.31/0.98  --demod_completeness_check              fast
% 1.31/0.98  --demod_use_ground                      true
% 1.31/0.98  --sup_to_prop_solver                    passive
% 1.31/0.98  --sup_prop_simpl_new                    true
% 1.31/0.98  --sup_prop_simpl_given                  true
% 1.31/0.98  --sup_fun_splitting                     false
% 1.31/0.98  --sup_smt_interval                      50000
% 1.31/0.98  
% 1.31/0.98  ------ Superposition Simplification Setup
% 1.31/0.98  
% 1.31/0.98  --sup_indices_passive                   []
% 1.31/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.31/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.31/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.31/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.31/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.31/0.98  --sup_full_bw                           [BwDemod]
% 1.31/0.98  --sup_immed_triv                        [TrivRules]
% 1.31/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.31/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.31/0.98  --sup_immed_bw_main                     []
% 1.31/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.31/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.31/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.31/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.31/0.98  
% 1.31/0.98  ------ Combination Options
% 1.31/0.98  
% 1.31/0.98  --comb_res_mult                         3
% 1.31/0.98  --comb_sup_mult                         2
% 1.31/0.98  --comb_inst_mult                        10
% 1.31/0.98  
% 1.31/0.98  ------ Debug Options
% 1.31/0.98  
% 1.31/0.98  --dbg_backtrace                         false
% 1.31/0.98  --dbg_dump_prop_clauses                 false
% 1.31/0.98  --dbg_dump_prop_clauses_file            -
% 1.31/0.98  --dbg_out_stat                          false
% 1.31/0.98  
% 1.31/0.98  
% 1.31/0.98  
% 1.31/0.98  
% 1.31/0.98  ------ Proving...
% 1.31/0.98  
% 1.31/0.98  
% 1.31/0.98  % SZS status Theorem for theBenchmark.p
% 1.31/0.98  
% 1.31/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.31/0.98  
% 1.31/0.98  fof(f6,axiom,(
% 1.31/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.31/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.31/0.98  
% 1.31/0.98  fof(f11,plain,(
% 1.31/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.31/0.98    inference(pure_predicate_removal,[],[f6])).
% 1.31/0.98  
% 1.31/0.98  fof(f18,plain,(
% 1.31/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.98    inference(ennf_transformation,[],[f11])).
% 1.31/0.98  
% 1.31/0.98  fof(f38,plain,(
% 1.31/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.31/0.98    inference(cnf_transformation,[],[f18])).
% 1.31/0.98  
% 1.31/0.98  fof(f2,axiom,(
% 1.31/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.31/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.31/0.98  
% 1.31/0.98  fof(f13,plain,(
% 1.31/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.31/0.98    inference(ennf_transformation,[],[f2])).
% 1.31/0.98  
% 1.31/0.98  fof(f24,plain,(
% 1.31/0.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.31/0.98    inference(nnf_transformation,[],[f13])).
% 1.31/0.98  
% 1.31/0.98  fof(f31,plain,(
% 1.31/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.31/0.98    inference(cnf_transformation,[],[f24])).
% 1.31/0.98  
% 1.31/0.98  fof(f4,axiom,(
% 1.31/0.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 1.31/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.31/0.98  
% 1.31/0.98  fof(f14,plain,(
% 1.31/0.98    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.31/0.98    inference(ennf_transformation,[],[f4])).
% 1.31/0.98  
% 1.31/0.98  fof(f15,plain,(
% 1.31/0.98    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.31/0.98    inference(flattening,[],[f14])).
% 1.31/0.98  
% 1.31/0.98  fof(f34,plain,(
% 1.31/0.98    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.31/0.98    inference(cnf_transformation,[],[f15])).
% 1.31/0.98  
% 1.31/0.98  fof(f9,conjecture,(
% 1.31/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 1.31/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.31/0.98  
% 1.31/0.98  fof(f10,negated_conjecture,(
% 1.31/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 1.31/0.98    inference(negated_conjecture,[],[f9])).
% 1.31/0.98  
% 1.31/0.98  fof(f22,plain,(
% 1.31/0.98    ? [X0,X1,X2,X3] : (((~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1) & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.31/0.98    inference(ennf_transformation,[],[f10])).
% 1.31/0.98  
% 1.31/0.98  fof(f23,plain,(
% 1.31/0.98    ? [X0,X1,X2,X3] : (~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.31/0.98    inference(flattening,[],[f22])).
% 1.31/0.98  
% 1.31/0.98  fof(f28,plain,(
% 1.31/0.98    ? [X0,X1,X2,X3] : (~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_hidden(k1_funct_1(sK3,sK2),sK1) & k1_xboole_0 != sK1 & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.31/0.98    introduced(choice_axiom,[])).
% 1.31/0.98  
% 1.31/0.98  fof(f29,plain,(
% 1.31/0.98    ~r2_hidden(k1_funct_1(sK3,sK2),sK1) & k1_xboole_0 != sK1 & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.31/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f28])).
% 1.31/0.98  
% 1.31/0.98  fof(f48,plain,(
% 1.31/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.31/0.98    inference(cnf_transformation,[],[f29])).
% 1.31/0.98  
% 1.31/0.98  fof(f1,axiom,(
% 1.31/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.31/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.31/0.98  
% 1.31/0.98  fof(f12,plain,(
% 1.31/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.31/0.98    inference(ennf_transformation,[],[f1])).
% 1.31/0.98  
% 1.31/0.98  fof(f30,plain,(
% 1.31/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.31/0.98    inference(cnf_transformation,[],[f12])).
% 1.31/0.98  
% 1.31/0.98  fof(f3,axiom,(
% 1.31/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.31/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.31/0.98  
% 1.31/0.98  fof(f33,plain,(
% 1.31/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.31/0.98    inference(cnf_transformation,[],[f3])).
% 1.31/0.98  
% 1.31/0.98  fof(f5,axiom,(
% 1.31/0.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.31/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.31/0.98  
% 1.31/0.98  fof(f16,plain,(
% 1.31/0.98    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.31/0.98    inference(ennf_transformation,[],[f5])).
% 1.31/0.98  
% 1.31/0.98  fof(f17,plain,(
% 1.31/0.98    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.31/0.98    inference(flattening,[],[f16])).
% 1.31/0.98  
% 1.31/0.98  fof(f25,plain,(
% 1.31/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) | (~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.31/0.98    inference(nnf_transformation,[],[f17])).
% 1.31/0.98  
% 1.31/0.98  fof(f26,plain,(
% 1.31/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) | ~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.31/0.98    inference(flattening,[],[f25])).
% 1.31/0.98  
% 1.31/0.98  fof(f36,plain,(
% 1.31/0.98    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.31/0.98    inference(cnf_transformation,[],[f26])).
% 1.31/0.98  
% 1.31/0.98  fof(f46,plain,(
% 1.31/0.98    v1_funct_1(sK3)),
% 1.31/0.98    inference(cnf_transformation,[],[f29])).
% 1.31/0.98  
% 1.31/0.98  fof(f7,axiom,(
% 1.31/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.31/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.31/0.98  
% 1.31/0.98  fof(f19,plain,(
% 1.31/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.98    inference(ennf_transformation,[],[f7])).
% 1.31/0.98  
% 1.31/0.98  fof(f39,plain,(
% 1.31/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.31/0.98    inference(cnf_transformation,[],[f19])).
% 1.31/0.98  
% 1.31/0.98  fof(f47,plain,(
% 1.31/0.98    v1_funct_2(sK3,sK0,sK1)),
% 1.31/0.98    inference(cnf_transformation,[],[f29])).
% 1.31/0.98  
% 1.31/0.98  fof(f8,axiom,(
% 1.31/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.31/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.31/0.98  
% 1.31/0.98  fof(f20,plain,(
% 1.31/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.98    inference(ennf_transformation,[],[f8])).
% 1.31/0.98  
% 1.31/0.98  fof(f21,plain,(
% 1.31/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.98    inference(flattening,[],[f20])).
% 1.31/0.98  
% 1.31/0.98  fof(f27,plain,(
% 1.31/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.98    inference(nnf_transformation,[],[f21])).
% 1.31/0.98  
% 1.31/0.98  fof(f40,plain,(
% 1.31/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.31/0.98    inference(cnf_transformation,[],[f27])).
% 1.31/0.98  
% 1.31/0.98  fof(f50,plain,(
% 1.31/0.98    k1_xboole_0 != sK1),
% 1.31/0.98    inference(cnf_transformation,[],[f29])).
% 1.31/0.98  
% 1.31/0.98  fof(f51,plain,(
% 1.31/0.98    ~r2_hidden(k1_funct_1(sK3,sK2),sK1)),
% 1.31/0.98    inference(cnf_transformation,[],[f29])).
% 1.31/0.98  
% 1.31/0.98  fof(f49,plain,(
% 1.31/0.98    r2_hidden(sK2,sK0)),
% 1.31/0.98    inference(cnf_transformation,[],[f29])).
% 1.31/0.98  
% 1.31/0.98  cnf(c_8,plain,
% 1.31/0.98      ( v5_relat_1(X0,X1)
% 1.31/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 1.31/0.98      inference(cnf_transformation,[],[f38]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_2,plain,
% 1.31/0.98      ( r1_tarski(k2_relat_1(X0),X1)
% 1.31/0.98      | ~ v5_relat_1(X0,X1)
% 1.31/0.98      | ~ v1_relat_1(X0) ),
% 1.31/0.98      inference(cnf_transformation,[],[f31]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_237,plain,
% 1.31/0.98      ( r1_tarski(k2_relat_1(X0),X1)
% 1.31/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 1.31/0.98      | ~ v1_relat_1(X0) ),
% 1.31/0.98      inference(resolution,[status(thm)],[c_8,c_2]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_4,plain,
% 1.31/0.98      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 1.31/0.98      | ~ v1_relat_1(X0)
% 1.31/0.98      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 1.31/0.98      inference(cnf_transformation,[],[f34]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_256,plain,
% 1.31/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.31/0.98      | ~ v1_relat_1(X0)
% 1.31/0.98      | k5_relat_1(X0,k6_relat_1(X2)) = X0 ),
% 1.31/0.98      inference(resolution,[status(thm)],[c_237,c_4]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_19,negated_conjecture,
% 1.31/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 1.31/0.98      inference(cnf_transformation,[],[f48]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_350,plain,
% 1.31/0.98      ( ~ v1_relat_1(X0)
% 1.31/0.98      | k5_relat_1(X0,k6_relat_1(X1)) = X0
% 1.31/0.98      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.31/0.98      | sK3 != X0 ),
% 1.31/0.98      inference(resolution_lifted,[status(thm)],[c_256,c_19]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_351,plain,
% 1.31/0.98      ( ~ v1_relat_1(sK3)
% 1.31/0.98      | k5_relat_1(sK3,k6_relat_1(X0)) = sK3
% 1.31/0.98      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.31/0.98      inference(unflattening,[status(thm)],[c_350]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_637,plain,
% 1.31/0.98      ( ~ v1_relat_1(sK3)
% 1.31/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.31/0.98      | k5_relat_1(sK3,k6_relat_1(X1_48)) = sK3 ),
% 1.31/0.98      inference(subtyping,[status(esa)],[c_351]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_830,plain,
% 1.31/0.98      ( k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.31/0.98      | k5_relat_1(sK3,k6_relat_1(X1_48)) = sK3
% 1.31/0.98      | v1_relat_1(sK3) != iProver_top ),
% 1.31/0.98      inference(predicate_to_equality,[status(thm)],[c_637]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_648,plain,( X0_49 = X0_49 ),theory(equality) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_917,plain,
% 1.31/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.31/0.98      inference(instantiation,[status(thm)],[c_648]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_0,plain,
% 1.31/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.31/0.98      | ~ v1_relat_1(X1)
% 1.31/0.98      | v1_relat_1(X0) ),
% 1.31/0.98      inference(cnf_transformation,[],[f30]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_335,plain,
% 1.31/0.98      ( ~ v1_relat_1(X0)
% 1.31/0.98      | v1_relat_1(X1)
% 1.31/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0)
% 1.31/0.98      | sK3 != X1 ),
% 1.31/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_19]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_336,plain,
% 1.31/0.98      ( ~ v1_relat_1(X0)
% 1.31/0.98      | v1_relat_1(sK3)
% 1.31/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0) ),
% 1.31/0.98      inference(unflattening,[status(thm)],[c_335]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_638,plain,
% 1.31/0.98      ( ~ v1_relat_1(X0_48)
% 1.31/0.98      | v1_relat_1(sK3)
% 1.31/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0_48) ),
% 1.31/0.98      inference(subtyping,[status(esa)],[c_336]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_912,plain,
% 1.31/0.98      ( ~ v1_relat_1(k2_zfmisc_1(X0_48,X1_48))
% 1.31/0.98      | v1_relat_1(sK3)
% 1.31/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)) ),
% 1.31/0.98      inference(instantiation,[status(thm)],[c_638]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_973,plain,
% 1.31/0.98      ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 1.31/0.98      | v1_relat_1(sK3)
% 1.31/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.31/0.98      inference(instantiation,[status(thm)],[c_912]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_3,plain,
% 1.31/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.31/0.98      inference(cnf_transformation,[],[f33]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_645,plain,
% 1.31/0.98      ( v1_relat_1(k2_zfmisc_1(X0_48,X1_48)) ),
% 1.31/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_1016,plain,
% 1.31/0.98      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.31/0.98      inference(instantiation,[status(thm)],[c_645]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_1153,plain,
% 1.31/0.98      ( k5_relat_1(sK3,k6_relat_1(X1_48)) = sK3
% 1.31/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.31/0.98      inference(global_propositional_subsumption,
% 1.31/0.98                [status(thm)],
% 1.31/0.98                [c_830,c_637,c_917,c_973,c_1016]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_1154,plain,
% 1.31/0.98      ( k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.31/0.98      | k5_relat_1(sK3,k6_relat_1(X1_48)) = sK3 ),
% 1.31/0.98      inference(renaming,[status(thm)],[c_1153]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_1158,plain,
% 1.31/0.98      ( k5_relat_1(sK3,k6_relat_1(sK1)) = sK3 ),
% 1.31/0.98      inference(equality_resolution,[status(thm)],[c_1154]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_6,plain,
% 1.31/0.98      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))))
% 1.31/0.98      | r2_hidden(k1_funct_1(X1,X0),X2)
% 1.31/0.98      | ~ v1_funct_1(X1)
% 1.31/0.98      | ~ v1_relat_1(X1) ),
% 1.31/0.98      inference(cnf_transformation,[],[f36]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_21,negated_conjecture,
% 1.31/0.98      ( v1_funct_1(sK3) ),
% 1.31/0.98      inference(cnf_transformation,[],[f46]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_289,plain,
% 1.31/0.98      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))))
% 1.31/0.98      | r2_hidden(k1_funct_1(X1,X0),X2)
% 1.31/0.98      | ~ v1_relat_1(X1)
% 1.31/0.98      | sK3 != X1 ),
% 1.31/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_21]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_290,plain,
% 1.31/0.98      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK3,k6_relat_1(X1))))
% 1.31/0.98      | r2_hidden(k1_funct_1(sK3,X0),X1)
% 1.31/0.98      | ~ v1_relat_1(sK3) ),
% 1.31/0.98      inference(unflattening,[status(thm)],[c_289]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_640,plain,
% 1.31/0.98      ( ~ r2_hidden(X0_51,k1_relat_1(k5_relat_1(sK3,k6_relat_1(X0_48))))
% 1.31/0.98      | r2_hidden(k1_funct_1(sK3,X0_51),X0_48)
% 1.31/0.98      | ~ v1_relat_1(sK3) ),
% 1.31/0.98      inference(subtyping,[status(esa)],[c_290]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_827,plain,
% 1.31/0.98      ( r2_hidden(X0_51,k1_relat_1(k5_relat_1(sK3,k6_relat_1(X0_48)))) != iProver_top
% 1.31/0.98      | r2_hidden(k1_funct_1(sK3,X0_51),X0_48) = iProver_top
% 1.31/0.98      | v1_relat_1(sK3) != iProver_top ),
% 1.31/0.98      inference(predicate_to_equality,[status(thm)],[c_640]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_680,plain,
% 1.31/0.98      ( r2_hidden(X0_51,k1_relat_1(k5_relat_1(sK3,k6_relat_1(X0_48)))) != iProver_top
% 1.31/0.98      | r2_hidden(k1_funct_1(sK3,X0_51),X0_48) = iProver_top
% 1.31/0.98      | v1_relat_1(sK3) != iProver_top ),
% 1.31/0.98      inference(predicate_to_equality,[status(thm)],[c_640]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_974,plain,
% 1.31/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.31/0.98      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 1.31/0.98      | v1_relat_1(sK3) = iProver_top ),
% 1.31/0.98      inference(predicate_to_equality,[status(thm)],[c_973]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_1017,plain,
% 1.31/0.98      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 1.31/0.98      inference(predicate_to_equality,[status(thm)],[c_1016]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_1160,plain,
% 1.31/0.98      ( r2_hidden(k1_funct_1(sK3,X0_51),X0_48) = iProver_top
% 1.31/0.98      | r2_hidden(X0_51,k1_relat_1(k5_relat_1(sK3,k6_relat_1(X0_48)))) != iProver_top ),
% 1.31/0.98      inference(global_propositional_subsumption,
% 1.31/0.98                [status(thm)],
% 1.31/0.98                [c_827,c_680,c_917,c_974,c_1017]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_1161,plain,
% 1.31/0.98      ( r2_hidden(X0_51,k1_relat_1(k5_relat_1(sK3,k6_relat_1(X0_48)))) != iProver_top
% 1.31/0.98      | r2_hidden(k1_funct_1(sK3,X0_51),X0_48) = iProver_top ),
% 1.31/0.98      inference(renaming,[status(thm)],[c_1160]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_1218,plain,
% 1.31/0.98      ( r2_hidden(X0_51,k1_relat_1(sK3)) != iProver_top
% 1.31/0.98      | r2_hidden(k1_funct_1(sK3,X0_51),sK1) = iProver_top ),
% 1.31/0.98      inference(superposition,[status(thm)],[c_1158,c_1161]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_9,plain,
% 1.31/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.31/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.31/0.98      inference(cnf_transformation,[],[f39]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_401,plain,
% 1.31/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.31/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.31/0.98      | sK3 != X2 ),
% 1.31/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_19]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_402,plain,
% 1.31/0.98      ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
% 1.31/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.31/0.98      inference(unflattening,[status(thm)],[c_401]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_636,plain,
% 1.31/0.98      ( k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.31/0.98      | k1_relset_1(X0_48,X1_48,sK3) = k1_relat_1(sK3) ),
% 1.31/0.98      inference(subtyping,[status(esa)],[c_402]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_930,plain,
% 1.31/0.98      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 1.31/0.98      inference(equality_resolution,[status(thm)],[c_636]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_20,negated_conjecture,
% 1.31/0.98      ( v1_funct_2(sK3,sK0,sK1) ),
% 1.31/0.98      inference(cnf_transformation,[],[f47]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_15,plain,
% 1.31/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.31/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.31/0.98      | k1_relset_1(X1,X2,X0) = X1
% 1.31/0.98      | k1_xboole_0 = X2 ),
% 1.31/0.98      inference(cnf_transformation,[],[f40]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_365,plain,
% 1.31/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.31/0.98      | k1_relset_1(X1,X2,X0) = X1
% 1.31/0.98      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.31/0.98      | sK3 != X0
% 1.31/0.98      | k1_xboole_0 = X2 ),
% 1.31/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_366,plain,
% 1.31/0.98      ( ~ v1_funct_2(sK3,X0,X1)
% 1.31/0.98      | k1_relset_1(X0,X1,sK3) = X0
% 1.31/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.31/0.98      | k1_xboole_0 = X1 ),
% 1.31/0.98      inference(unflattening,[status(thm)],[c_365]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_521,plain,
% 1.31/0.98      ( k1_relset_1(X0,X1,sK3) = X0
% 1.31/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.31/0.98      | sK0 != X0
% 1.31/0.98      | sK1 != X1
% 1.31/0.98      | sK3 != sK3
% 1.31/0.98      | k1_xboole_0 = X1 ),
% 1.31/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_366]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_522,plain,
% 1.31/0.98      ( k1_relset_1(sK0,sK1,sK3) = sK0
% 1.31/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.31/0.98      | k1_xboole_0 = sK1 ),
% 1.31/0.98      inference(unflattening,[status(thm)],[c_521]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_17,negated_conjecture,
% 1.31/0.98      ( k1_xboole_0 != sK1 ),
% 1.31/0.98      inference(cnf_transformation,[],[f50]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_523,plain,
% 1.31/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.31/0.98      | k1_relset_1(sK0,sK1,sK3) = sK0 ),
% 1.31/0.98      inference(global_propositional_subsumption,
% 1.31/0.98                [status(thm)],
% 1.31/0.98                [c_522,c_17]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_524,plain,
% 1.31/0.98      ( k1_relset_1(sK0,sK1,sK3) = sK0
% 1.31/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.31/0.98      inference(renaming,[status(thm)],[c_523]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_581,plain,
% 1.31/0.98      ( k1_relset_1(sK0,sK1,sK3) = sK0 ),
% 1.31/0.98      inference(equality_resolution_simp,[status(thm)],[c_524]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_633,plain,
% 1.31/0.98      ( k1_relset_1(sK0,sK1,sK3) = sK0 ),
% 1.31/0.98      inference(subtyping,[status(esa)],[c_581]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_996,plain,
% 1.31/0.98      ( k1_relat_1(sK3) = sK0 ),
% 1.31/0.98      inference(light_normalisation,[status(thm)],[c_930,c_633]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_1225,plain,
% 1.31/0.98      ( r2_hidden(X0_51,sK0) != iProver_top
% 1.31/0.98      | r2_hidden(k1_funct_1(sK3,X0_51),sK1) = iProver_top ),
% 1.31/0.98      inference(light_normalisation,[status(thm)],[c_1218,c_996]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_1234,plain,
% 1.31/0.98      ( r2_hidden(k1_funct_1(sK3,sK2),sK1) = iProver_top
% 1.31/0.98      | r2_hidden(sK2,sK0) != iProver_top ),
% 1.31/0.98      inference(instantiation,[status(thm)],[c_1225]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_16,negated_conjecture,
% 1.31/0.98      ( ~ r2_hidden(k1_funct_1(sK3,sK2),sK1) ),
% 1.31/0.98      inference(cnf_transformation,[],[f51]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_26,plain,
% 1.31/0.98      ( r2_hidden(k1_funct_1(sK3,sK2),sK1) != iProver_top ),
% 1.31/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_18,negated_conjecture,
% 1.31/0.98      ( r2_hidden(sK2,sK0) ),
% 1.31/0.98      inference(cnf_transformation,[],[f49]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(c_25,plain,
% 1.31/0.98      ( r2_hidden(sK2,sK0) = iProver_top ),
% 1.31/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.31/0.98  
% 1.31/0.98  cnf(contradiction,plain,
% 1.31/0.98      ( $false ),
% 1.31/0.98      inference(minisat,[status(thm)],[c_1234,c_26,c_25]) ).
% 1.31/0.98  
% 1.31/0.98  
% 1.31/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.31/0.98  
% 1.31/0.98  ------                               Statistics
% 1.31/0.98  
% 1.31/0.98  ------ General
% 1.31/0.98  
% 1.31/0.98  abstr_ref_over_cycles:                  0
% 1.31/0.98  abstr_ref_under_cycles:                 0
% 1.31/0.98  gc_basic_clause_elim:                   0
% 1.31/0.98  forced_gc_time:                         0
% 1.31/0.98  parsing_time:                           0.01
% 1.31/0.98  unif_index_cands_time:                  0.
% 1.31/0.98  unif_index_add_time:                    0.
% 1.31/0.98  orderings_time:                         0.
% 1.31/0.98  out_proof_time:                         0.011
% 1.31/0.98  total_time:                             0.075
% 1.31/0.98  num_of_symbols:                         55
% 1.31/0.98  num_of_terms:                           1163
% 1.31/0.98  
% 1.31/0.98  ------ Preprocessing
% 1.31/0.98  
% 1.31/0.98  num_of_splits:                          0
% 1.31/0.98  num_of_split_atoms:                     0
% 1.31/0.98  num_of_reused_defs:                     0
% 1.31/0.98  num_eq_ax_congr_red:                    10
% 1.31/0.98  num_of_sem_filtered_clauses:            1
% 1.31/0.98  num_of_subtypes:                        4
% 1.31/0.98  monotx_restored_types:                  0
% 1.31/0.98  sat_num_of_epr_types:                   0
% 1.31/0.98  sat_num_of_non_cyclic_types:            0
% 1.31/0.98  sat_guarded_non_collapsed_types:        0
% 1.31/0.98  num_pure_diseq_elim:                    0
% 1.31/0.98  simp_replaced_by:                       0
% 1.31/0.98  res_preprocessed:                       90
% 1.31/0.98  prep_upred:                             0
% 1.31/0.98  prep_unflattend:                        28
% 1.31/0.98  smt_new_axioms:                         0
% 1.31/0.98  pred_elim_cands:                        2
% 1.31/0.98  pred_elim:                              5
% 1.31/0.98  pred_elim_cl:                           9
% 1.31/0.98  pred_elim_cycles:                       7
% 1.31/0.98  merged_defs:                            0
% 1.31/0.98  merged_defs_ncl:                        0
% 1.31/0.98  bin_hyper_res:                          0
% 1.31/0.98  prep_cycles:                            4
% 1.31/0.98  pred_elim_time:                         0.008
% 1.31/0.98  splitting_time:                         0.
% 1.31/0.98  sem_filter_time:                        0.
% 1.31/0.98  monotx_time:                            0.
% 1.31/0.98  subtype_inf_time:                       0.
% 1.31/0.98  
% 1.31/0.98  ------ Problem properties
% 1.31/0.98  
% 1.31/0.98  clauses:                                13
% 1.31/0.98  conjectures:                            3
% 1.31/0.98  epr:                                    2
% 1.31/0.98  horn:                                   12
% 1.31/0.98  ground:                                 6
% 1.31/0.98  unary:                                  5
% 1.31/0.98  binary:                                 1
% 1.31/0.98  lits:                                   30
% 1.31/0.98  lits_eq:                                14
% 1.31/0.98  fd_pure:                                0
% 1.31/0.98  fd_pseudo:                              0
% 1.31/0.98  fd_cond:                                0
% 1.31/0.98  fd_pseudo_cond:                         0
% 1.31/0.98  ac_symbols:                             0
% 1.31/0.98  
% 1.31/0.98  ------ Propositional Solver
% 1.31/0.98  
% 1.31/0.98  prop_solver_calls:                      25
% 1.31/0.98  prop_fast_solver_calls:                 541
% 1.31/0.98  smt_solver_calls:                       0
% 1.31/0.98  smt_fast_solver_calls:                  0
% 1.31/0.98  prop_num_of_clauses:                    331
% 1.31/0.98  prop_preprocess_simplified:             2095
% 1.31/0.98  prop_fo_subsumed:                       10
% 1.31/0.98  prop_solver_time:                       0.
% 1.31/0.98  smt_solver_time:                        0.
% 1.31/0.98  smt_fast_solver_time:                   0.
% 1.31/0.98  prop_fast_solver_time:                  0.
% 1.31/0.98  prop_unsat_core_time:                   0.
% 1.31/0.98  
% 1.31/0.98  ------ QBF
% 1.31/0.98  
% 1.31/0.98  qbf_q_res:                              0
% 1.31/0.98  qbf_num_tautologies:                    0
% 1.31/0.98  qbf_prep_cycles:                        0
% 1.31/0.98  
% 1.31/0.98  ------ BMC1
% 1.31/0.98  
% 1.31/0.98  bmc1_current_bound:                     -1
% 1.31/0.98  bmc1_last_solved_bound:                 -1
% 1.31/0.98  bmc1_unsat_core_size:                   -1
% 1.31/0.98  bmc1_unsat_core_parents_size:           -1
% 1.31/0.98  bmc1_merge_next_fun:                    0
% 1.31/0.98  bmc1_unsat_core_clauses_time:           0.
% 1.31/0.98  
% 1.31/0.98  ------ Instantiation
% 1.31/0.98  
% 1.31/0.98  inst_num_of_clauses:                    92
% 1.31/0.98  inst_num_in_passive:                    4
% 1.31/0.98  inst_num_in_active:                     71
% 1.31/0.98  inst_num_in_unprocessed:                17
% 1.31/0.98  inst_num_of_loops:                      80
% 1.31/0.98  inst_num_of_learning_restarts:          0
% 1.31/0.98  inst_num_moves_active_passive:          6
% 1.31/0.98  inst_lit_activity:                      0
% 1.31/0.98  inst_lit_activity_moves:                0
% 1.31/0.98  inst_num_tautologies:                   0
% 1.31/0.98  inst_num_prop_implied:                  0
% 1.31/0.98  inst_num_existing_simplified:           0
% 1.31/0.98  inst_num_eq_res_simplified:             0
% 1.31/0.98  inst_num_child_elim:                    0
% 1.31/0.98  inst_num_of_dismatching_blockings:      8
% 1.31/0.98  inst_num_of_non_proper_insts:           82
% 1.31/0.98  inst_num_of_duplicates:                 0
% 1.31/0.98  inst_inst_num_from_inst_to_res:         0
% 1.31/0.98  inst_dismatching_checking_time:         0.
% 1.31/0.98  
% 1.31/0.98  ------ Resolution
% 1.31/0.98  
% 1.31/0.98  res_num_of_clauses:                     0
% 1.31/0.98  res_num_in_passive:                     0
% 1.31/0.98  res_num_in_active:                      0
% 1.31/0.98  res_num_of_loops:                       94
% 1.31/0.98  res_forward_subset_subsumed:            21
% 1.31/0.98  res_backward_subset_subsumed:           0
% 1.31/0.98  res_forward_subsumed:                   0
% 1.31/0.98  res_backward_subsumed:                  0
% 1.31/0.98  res_forward_subsumption_resolution:     0
% 1.31/0.98  res_backward_subsumption_resolution:    0
% 1.31/0.98  res_clause_to_clause_subsumption:       25
% 1.31/0.98  res_orphan_elimination:                 0
% 1.31/0.98  res_tautology_del:                      22
% 1.31/0.98  res_num_eq_res_simplified:              1
% 1.31/0.98  res_num_sel_changes:                    0
% 1.31/0.98  res_moves_from_active_to_pass:          0
% 1.31/0.98  
% 1.31/0.98  ------ Superposition
% 1.31/0.98  
% 1.31/0.98  sup_time_total:                         0.
% 1.31/0.98  sup_time_generating:                    0.
% 1.31/0.98  sup_time_sim_full:                      0.
% 1.31/0.98  sup_time_sim_immed:                     0.
% 1.31/0.98  
% 1.31/0.98  sup_num_of_clauses:                     16
% 1.31/0.98  sup_num_in_active:                      15
% 1.31/0.98  sup_num_in_passive:                     1
% 1.31/0.98  sup_num_of_loops:                       15
% 1.31/0.98  sup_fw_superposition:                   0
% 1.31/0.98  sup_bw_superposition:                   5
% 1.31/0.98  sup_immediate_simplified:               3
% 1.31/0.98  sup_given_eliminated:                   0
% 1.31/0.98  comparisons_done:                       0
% 1.31/0.98  comparisons_avoided:                    0
% 1.31/0.98  
% 1.31/0.98  ------ Simplifications
% 1.31/0.98  
% 1.31/0.98  
% 1.31/0.98  sim_fw_subset_subsumed:                 0
% 1.31/0.98  sim_bw_subset_subsumed:                 0
% 1.31/0.98  sim_fw_subsumed:                        0
% 1.31/0.98  sim_bw_subsumed:                        0
% 1.31/0.98  sim_fw_subsumption_res:                 1
% 1.31/0.98  sim_bw_subsumption_res:                 0
% 1.31/0.98  sim_tautology_del:                      4
% 1.31/0.98  sim_eq_tautology_del:                   0
% 1.31/0.98  sim_eq_res_simp:                        0
% 1.31/0.98  sim_fw_demodulated:                     0
% 1.31/0.98  sim_bw_demodulated:                     1
% 1.31/0.98  sim_light_normalised:                   6
% 1.31/0.98  sim_joinable_taut:                      0
% 1.31/0.98  sim_joinable_simp:                      0
% 1.31/0.98  sim_ac_normalised:                      0
% 1.31/0.98  sim_smt_subsumption:                    0
% 1.31/0.98  
%------------------------------------------------------------------------------
