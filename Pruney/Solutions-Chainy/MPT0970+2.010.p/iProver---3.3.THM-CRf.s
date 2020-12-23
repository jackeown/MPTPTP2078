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
% DateTime   : Thu Dec  3 12:00:47 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 557 expanded)
%              Number of clauses        :   84 ( 208 expanded)
%              Number of leaves         :   16 ( 134 expanded)
%              Depth                    :   20
%              Number of atoms          :  425 (2486 expanded)
%              Number of equality atoms :  199 ( 798 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

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
    inference(flattening,[],[f22])).

fof(f31,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK4(X3)) = X3
        & r2_hidden(sK4(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
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
   => ( k2_relset_1(sK1,sK2,sK3) != sK2
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK3,X4) = X3
              & r2_hidden(X4,sK1) )
          | ~ r2_hidden(X3,sK2) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( k2_relset_1(sK1,sK2,sK3) != sK2
    & ! [X3] :
        ( ( k1_funct_1(sK3,sK4(X3)) = X3
          & r2_hidden(sK4(X3),sK1) )
        | ~ r2_hidden(X3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f23,f31,f30])).

fof(f52,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f9])).

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

fof(f29,plain,(
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

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( k1_funct_1(X1,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X1)) )
              & r2_hidden(X2,X0) )
       => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X1,X3) != X2
              | ~ r2_hidden(X3,k1_relat_1(X1)) )
          & r2_hidden(X2,X0) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X1,X3) != X2
              | ~ r2_hidden(X3,k1_relat_1(X1)) )
          & r2_hidden(X2,X0) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X1,X3) != X2
              | ~ r2_hidden(X3,k1_relat_1(X1)) )
          & r2_hidden(X2,X0) )
     => ( ! [X3] :
            ( k1_funct_1(X1,X3) != sK0(X0,X1)
            | ~ r2_hidden(X3,k1_relat_1(X1)) )
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | ( ! [X3] :
            ( k1_funct_1(X1,X3) != sK0(X0,X1)
            | ~ r2_hidden(X3,k1_relat_1(X1)) )
        & r2_hidden(sK0(X0,X1),X0) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f27])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | r2_hidden(sK0(X0,X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f55,plain,(
    ! [X3] :
      ( k1_funct_1(sK3,sK4(X3)) = X3
      | ~ r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    k2_relset_1(sK1,sK2,sK3) != sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | k1_funct_1(X1,X3) != sK0(X0,X1)
      | ~ r2_hidden(X3,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f54,plain,(
    ! [X3] :
      ( r2_hidden(sK4(X3),sK1)
      | ~ r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_754,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1559,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k2_relset_1(sK1,sK2,sK3))
    | k2_relset_1(sK1,sK2,sK3) != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_754])).

cnf(c_2228,plain,
    ( ~ r1_tarski(X0,k2_relset_1(sK1,sK2,sK3))
    | r1_tarski(sK2,k2_relset_1(sK1,sK2,sK3))
    | k2_relset_1(sK1,sK2,sK3) != k2_relset_1(sK1,sK2,sK3)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1559])).

cnf(c_2230,plain,
    ( r1_tarski(sK2,k2_relset_1(sK1,sK2,sK3))
    | ~ r1_tarski(k1_xboole_0,k2_relset_1(sK1,sK2,sK3))
    | k2_relset_1(sK1,sK2,sK3) != k2_relset_1(sK1,sK2,sK3)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2228])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2199,plain,
    ( r1_tarski(k1_xboole_0,k2_relset_1(sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_375,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_21])).

cnf(c_376,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_590,plain,
    ( k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK3 != sK3
    | sK2 != X1
    | sK1 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_376])).

cnf(c_591,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_590])).

cnf(c_653,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_591])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_420,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_421,plain,
    ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_1096,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_421])).

cnf(c_1364,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_653,c_1096])).

cnf(c_7,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_281,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_23])).

cnf(c_282,plain,
    ( r2_hidden(sK0(X0,sK3),X0)
    | r1_tarski(X0,k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_281])).

cnf(c_954,plain,
    ( r2_hidden(sK0(X0,sK3),X0) = iProver_top
    | r1_tarski(X0,k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_282])).

cnf(c_283,plain,
    ( r2_hidden(sK0(X0,sK3),X0) = iProver_top
    | r1_tarski(X0,k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_282])).

cnf(c_752,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1053,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_752])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_429,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_430,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_1108,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_430])).

cnf(c_1109,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1108])).

cnf(c_1524,plain,
    ( r1_tarski(X0,k2_relat_1(sK3)) = iProver_top
    | r2_hidden(sK0(X0,sK3),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_954,c_283,c_1053,c_1109])).

cnf(c_1525,plain,
    ( r2_hidden(sK0(X0,sK3),X0) = iProver_top
    | r1_tarski(X0,k2_relat_1(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1524])).

cnf(c_19,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | k1_funct_1(sK3,sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_956,plain,
    ( k1_funct_1(sK3,sK4(X0)) = X0
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1532,plain,
    ( k1_funct_1(sK3,sK4(sK0(sK2,sK3))) = sK0(sK2,sK3)
    | r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1525,c_956])).

cnf(c_18,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) != sK2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_5,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_260,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_9])).

cnf(c_261,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_265,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_261,c_8])).

cnf(c_266,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_265])).

cnf(c_363,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_266,c_21])).

cnf(c_364,plain,
    ( r1_tarski(k2_relat_1(sK3),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_363])).

cnf(c_1054,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_364])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_411,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_412,plain,
    ( k2_relset_1(X0,X1,sK3) = k2_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_411])).

cnf(c_1088,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_412])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1100,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1208,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(sK2,k2_relat_1(sK3))
    | sK2 = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1100])).

cnf(c_1533,plain,
    ( r1_tarski(sK2,k2_relat_1(sK3))
    | k1_funct_1(sK3,sK4(sK0(sK2,sK3))) = sK0(sK2,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1532])).

cnf(c_753,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1076,plain,
    ( k2_relset_1(sK1,sK2,sK3) != X0
    | k2_relset_1(sK1,sK2,sK3) = sK2
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_753])).

cnf(c_1558,plain,
    ( k2_relset_1(sK1,sK2,sK3) != k2_relat_1(sK3)
    | k2_relset_1(sK1,sK2,sK3) = sK2
    | sK2 != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1076])).

cnf(c_1590,plain,
    ( k1_funct_1(sK3,sK4(sK0(sK2,sK3))) = sK0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1532,c_18,c_1053,c_1054,c_1088,c_1208,c_1533,c_1558])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r1_tarski(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | sK0(X2,X1) != k1_funct_1(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_296,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r1_tarski(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK0(X2,X1) != k1_funct_1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_23])).

cnf(c_297,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r1_tarski(X1,k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | sK0(X1,sK3) != k1_funct_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_296])).

cnf(c_953,plain,
    ( sK0(X0,sK3) != k1_funct_1(sK3,X1)
    | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top
    | r1_tarski(X0,k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_297])).

cnf(c_298,plain,
    ( sK0(X0,sK3) != k1_funct_1(sK3,X1)
    | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top
    | r1_tarski(X0,k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_297])).

cnf(c_1514,plain,
    ( r1_tarski(X0,k2_relat_1(sK3)) = iProver_top
    | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top
    | sK0(X0,sK3) != k1_funct_1(sK3,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_953,c_298,c_1053,c_1109])).

cnf(c_1515,plain,
    ( sK0(X0,sK3) != k1_funct_1(sK3,X1)
    | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top
    | r1_tarski(X0,k2_relat_1(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1514])).

cnf(c_1593,plain,
    ( sK0(X0,sK3) != sK0(sK2,sK3)
    | r2_hidden(sK4(sK0(sK2,sK3)),k1_relat_1(sK3)) != iProver_top
    | r1_tarski(X0,k2_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1590,c_1515])).

cnf(c_1655,plain,
    ( r2_hidden(sK4(sK0(sK2,sK3)),k1_relat_1(sK3)) != iProver_top
    | r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1593])).

cnf(c_1055,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1054])).

cnf(c_1209,plain,
    ( sK2 = k2_relat_1(sK3)
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
    | r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1208])).

cnf(c_1867,plain,
    ( r2_hidden(sK4(sK0(sK2,sK3)),k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1655,c_18,c_1053,c_1055,c_1088,c_1209,c_1558])).

cnf(c_1872,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK4(sK0(sK2,sK3)),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1364,c_1867])).

cnf(c_1552,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relset_1(sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_752])).

cnf(c_1089,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2)
    | k2_relset_1(sK1,sK2,sK3) != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_754])).

cnf(c_1225,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2)
    | k2_relset_1(sK1,sK2,sK3) != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1089])).

cnf(c_1418,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2)
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | k2_relset_1(sK1,sK2,sK3) != k2_relat_1(sK3)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1225])).

cnf(c_20,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | r2_hidden(sK4(X0),sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1181,plain,
    ( ~ r2_hidden(sK0(sK2,sK3),sK2)
    | r2_hidden(sK4(sK0(sK2,sK3)),sK1) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1184,plain,
    ( r2_hidden(sK0(sK2,sK3),sK2) != iProver_top
    | r2_hidden(sK4(sK0(sK2,sK3)),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1181])).

cnf(c_1179,plain,
    ( r2_hidden(sK0(sK2,sK3),sK2)
    | r1_tarski(sK2,k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_282])).

cnf(c_1182,plain,
    ( r2_hidden(sK0(sK2,sK3),sK2) = iProver_top
    | r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1179])).

cnf(c_1123,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_752])).

cnf(c_1061,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2)
    | ~ r1_tarski(sK2,k2_relset_1(sK1,sK2,sK3))
    | k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2230,c_2199,c_1872,c_1558,c_1552,c_1418,c_1209,c_1184,c_1182,c_1123,c_1109,c_1088,c_1061,c_1055,c_1054,c_1053,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n003.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 13:19:27 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 1.75/0.95  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/0.95  
% 1.75/0.95  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.75/0.95  
% 1.75/0.95  ------  iProver source info
% 1.75/0.95  
% 1.75/0.95  git: date: 2020-06-30 10:37:57 +0100
% 1.75/0.95  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.75/0.95  git: non_committed_changes: false
% 1.75/0.95  git: last_make_outside_of_git: false
% 1.75/0.95  
% 1.75/0.95  ------ 
% 1.75/0.95  
% 1.75/0.95  ------ Input Options
% 1.75/0.95  
% 1.75/0.95  --out_options                           all
% 1.75/0.95  --tptp_safe_out                         true
% 1.75/0.95  --problem_path                          ""
% 1.75/0.95  --include_path                          ""
% 1.75/0.95  --clausifier                            res/vclausify_rel
% 1.75/0.95  --clausifier_options                    --mode clausify
% 1.75/0.95  --stdin                                 false
% 1.75/0.95  --stats_out                             all
% 1.75/0.95  
% 1.75/0.95  ------ General Options
% 1.75/0.95  
% 1.75/0.95  --fof                                   false
% 1.75/0.95  --time_out_real                         305.
% 1.75/0.95  --time_out_virtual                      -1.
% 1.75/0.95  --symbol_type_check                     false
% 1.75/0.95  --clausify_out                          false
% 1.75/0.95  --sig_cnt_out                           false
% 1.75/0.95  --trig_cnt_out                          false
% 1.75/0.95  --trig_cnt_out_tolerance                1.
% 1.75/0.95  --trig_cnt_out_sk_spl                   false
% 1.75/0.95  --abstr_cl_out                          false
% 1.75/0.95  
% 1.75/0.95  ------ Global Options
% 1.75/0.95  
% 1.75/0.95  --schedule                              default
% 1.75/0.95  --add_important_lit                     false
% 1.75/0.95  --prop_solver_per_cl                    1000
% 1.75/0.95  --min_unsat_core                        false
% 1.75/0.95  --soft_assumptions                      false
% 1.75/0.95  --soft_lemma_size                       3
% 1.75/0.95  --prop_impl_unit_size                   0
% 1.75/0.95  --prop_impl_unit                        []
% 1.75/0.95  --share_sel_clauses                     true
% 1.75/0.95  --reset_solvers                         false
% 1.75/0.95  --bc_imp_inh                            [conj_cone]
% 1.75/0.95  --conj_cone_tolerance                   3.
% 1.75/0.95  --extra_neg_conj                        none
% 1.75/0.95  --large_theory_mode                     true
% 1.75/0.95  --prolific_symb_bound                   200
% 1.75/0.95  --lt_threshold                          2000
% 1.75/0.95  --clause_weak_htbl                      true
% 1.75/0.95  --gc_record_bc_elim                     false
% 1.75/0.95  
% 1.75/0.95  ------ Preprocessing Options
% 1.75/0.95  
% 1.75/0.95  --preprocessing_flag                    true
% 1.75/0.95  --time_out_prep_mult                    0.1
% 1.75/0.95  --splitting_mode                        input
% 1.75/0.95  --splitting_grd                         true
% 1.75/0.95  --splitting_cvd                         false
% 1.75/0.95  --splitting_cvd_svl                     false
% 1.75/0.95  --splitting_nvd                         32
% 1.75/0.95  --sub_typing                            true
% 1.75/0.95  --prep_gs_sim                           true
% 1.75/0.95  --prep_unflatten                        true
% 1.75/0.95  --prep_res_sim                          true
% 1.75/0.95  --prep_upred                            true
% 1.75/0.95  --prep_sem_filter                       exhaustive
% 1.75/0.95  --prep_sem_filter_out                   false
% 1.75/0.95  --pred_elim                             true
% 1.75/0.95  --res_sim_input                         true
% 1.75/0.95  --eq_ax_congr_red                       true
% 1.75/0.95  --pure_diseq_elim                       true
% 1.75/0.95  --brand_transform                       false
% 1.75/0.95  --non_eq_to_eq                          false
% 1.75/0.95  --prep_def_merge                        true
% 1.75/0.95  --prep_def_merge_prop_impl              false
% 1.75/0.95  --prep_def_merge_mbd                    true
% 1.75/0.95  --prep_def_merge_tr_red                 false
% 1.75/0.95  --prep_def_merge_tr_cl                  false
% 1.75/0.95  --smt_preprocessing                     true
% 1.75/0.95  --smt_ac_axioms                         fast
% 1.75/0.95  --preprocessed_out                      false
% 1.75/0.95  --preprocessed_stats                    false
% 1.75/0.95  
% 1.75/0.95  ------ Abstraction refinement Options
% 1.75/0.95  
% 1.75/0.95  --abstr_ref                             []
% 1.75/0.95  --abstr_ref_prep                        false
% 1.75/0.95  --abstr_ref_until_sat                   false
% 1.75/0.95  --abstr_ref_sig_restrict                funpre
% 1.75/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 1.75/0.95  --abstr_ref_under                       []
% 1.75/0.95  
% 1.75/0.95  ------ SAT Options
% 1.75/0.95  
% 1.75/0.95  --sat_mode                              false
% 1.75/0.95  --sat_fm_restart_options                ""
% 1.75/0.95  --sat_gr_def                            false
% 1.75/0.95  --sat_epr_types                         true
% 1.75/0.95  --sat_non_cyclic_types                  false
% 1.75/0.95  --sat_finite_models                     false
% 1.75/0.95  --sat_fm_lemmas                         false
% 1.75/0.95  --sat_fm_prep                           false
% 1.75/0.95  --sat_fm_uc_incr                        true
% 1.75/0.95  --sat_out_model                         small
% 1.75/0.95  --sat_out_clauses                       false
% 1.75/0.95  
% 1.75/0.95  ------ QBF Options
% 1.75/0.95  
% 1.75/0.95  --qbf_mode                              false
% 1.75/0.95  --qbf_elim_univ                         false
% 1.75/0.95  --qbf_dom_inst                          none
% 1.75/0.95  --qbf_dom_pre_inst                      false
% 1.75/0.95  --qbf_sk_in                             false
% 1.75/0.95  --qbf_pred_elim                         true
% 1.75/0.95  --qbf_split                             512
% 1.75/0.95  
% 1.75/0.95  ------ BMC1 Options
% 1.75/0.95  
% 1.75/0.95  --bmc1_incremental                      false
% 1.75/0.95  --bmc1_axioms                           reachable_all
% 1.75/0.95  --bmc1_min_bound                        0
% 1.75/0.95  --bmc1_max_bound                        -1
% 1.75/0.95  --bmc1_max_bound_default                -1
% 1.75/0.95  --bmc1_symbol_reachability              true
% 1.75/0.95  --bmc1_property_lemmas                  false
% 1.75/0.95  --bmc1_k_induction                      false
% 1.75/0.95  --bmc1_non_equiv_states                 false
% 1.75/0.95  --bmc1_deadlock                         false
% 1.75/0.95  --bmc1_ucm                              false
% 1.75/0.95  --bmc1_add_unsat_core                   none
% 1.75/0.95  --bmc1_unsat_core_children              false
% 1.75/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 1.75/0.95  --bmc1_out_stat                         full
% 1.75/0.95  --bmc1_ground_init                      false
% 1.75/0.95  --bmc1_pre_inst_next_state              false
% 1.75/0.95  --bmc1_pre_inst_state                   false
% 1.75/0.95  --bmc1_pre_inst_reach_state             false
% 1.75/0.95  --bmc1_out_unsat_core                   false
% 1.75/0.95  --bmc1_aig_witness_out                  false
% 1.75/0.95  --bmc1_verbose                          false
% 1.75/0.95  --bmc1_dump_clauses_tptp                false
% 1.75/0.95  --bmc1_dump_unsat_core_tptp             false
% 1.75/0.95  --bmc1_dump_file                        -
% 1.75/0.95  --bmc1_ucm_expand_uc_limit              128
% 1.75/0.95  --bmc1_ucm_n_expand_iterations          6
% 1.75/0.95  --bmc1_ucm_extend_mode                  1
% 1.75/0.95  --bmc1_ucm_init_mode                    2
% 1.75/0.95  --bmc1_ucm_cone_mode                    none
% 1.75/0.95  --bmc1_ucm_reduced_relation_type        0
% 1.75/0.95  --bmc1_ucm_relax_model                  4
% 1.75/0.95  --bmc1_ucm_full_tr_after_sat            true
% 1.75/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 1.75/0.95  --bmc1_ucm_layered_model                none
% 1.75/0.95  --bmc1_ucm_max_lemma_size               10
% 1.75/0.95  
% 1.75/0.95  ------ AIG Options
% 1.75/0.95  
% 1.75/0.95  --aig_mode                              false
% 1.75/0.95  
% 1.75/0.95  ------ Instantiation Options
% 1.75/0.95  
% 1.75/0.95  --instantiation_flag                    true
% 1.75/0.95  --inst_sos_flag                         false
% 1.75/0.95  --inst_sos_phase                        true
% 1.75/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.75/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.75/0.95  --inst_lit_sel_side                     num_symb
% 1.75/0.95  --inst_solver_per_active                1400
% 1.75/0.95  --inst_solver_calls_frac                1.
% 1.75/0.95  --inst_passive_queue_type               priority_queues
% 1.75/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.75/0.95  --inst_passive_queues_freq              [25;2]
% 1.75/0.95  --inst_dismatching                      true
% 1.75/0.95  --inst_eager_unprocessed_to_passive     true
% 1.75/0.95  --inst_prop_sim_given                   true
% 1.75/0.95  --inst_prop_sim_new                     false
% 1.75/0.95  --inst_subs_new                         false
% 1.75/0.95  --inst_eq_res_simp                      false
% 1.75/0.95  --inst_subs_given                       false
% 1.75/0.95  --inst_orphan_elimination               true
% 1.75/0.95  --inst_learning_loop_flag               true
% 1.75/0.95  --inst_learning_start                   3000
% 1.75/0.95  --inst_learning_factor                  2
% 1.75/0.95  --inst_start_prop_sim_after_learn       3
% 1.75/0.95  --inst_sel_renew                        solver
% 1.75/0.95  --inst_lit_activity_flag                true
% 1.75/0.95  --inst_restr_to_given                   false
% 1.75/0.95  --inst_activity_threshold               500
% 1.75/0.95  --inst_out_proof                        true
% 1.75/0.95  
% 1.75/0.95  ------ Resolution Options
% 1.75/0.95  
% 1.75/0.95  --resolution_flag                       true
% 1.75/0.95  --res_lit_sel                           adaptive
% 1.75/0.95  --res_lit_sel_side                      none
% 1.75/0.95  --res_ordering                          kbo
% 1.75/0.95  --res_to_prop_solver                    active
% 1.75/0.95  --res_prop_simpl_new                    false
% 1.75/0.95  --res_prop_simpl_given                  true
% 1.75/0.95  --res_passive_queue_type                priority_queues
% 1.75/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.75/0.95  --res_passive_queues_freq               [15;5]
% 1.75/0.95  --res_forward_subs                      full
% 1.75/0.95  --res_backward_subs                     full
% 1.75/0.95  --res_forward_subs_resolution           true
% 1.75/0.95  --res_backward_subs_resolution          true
% 1.75/0.95  --res_orphan_elimination                true
% 1.75/0.95  --res_time_limit                        2.
% 1.75/0.95  --res_out_proof                         true
% 1.75/0.95  
% 1.75/0.95  ------ Superposition Options
% 1.75/0.95  
% 1.75/0.95  --superposition_flag                    true
% 1.75/0.95  --sup_passive_queue_type                priority_queues
% 1.75/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.75/0.95  --sup_passive_queues_freq               [8;1;4]
% 1.75/0.95  --demod_completeness_check              fast
% 1.75/0.95  --demod_use_ground                      true
% 1.75/0.95  --sup_to_prop_solver                    passive
% 1.75/0.95  --sup_prop_simpl_new                    true
% 1.75/0.95  --sup_prop_simpl_given                  true
% 1.75/0.95  --sup_fun_splitting                     false
% 1.75/0.95  --sup_smt_interval                      50000
% 1.75/0.95  
% 1.75/0.95  ------ Superposition Simplification Setup
% 1.75/0.95  
% 1.75/0.95  --sup_indices_passive                   []
% 1.75/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.75/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.75/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.75/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 1.75/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.75/0.95  --sup_full_bw                           [BwDemod]
% 1.75/0.95  --sup_immed_triv                        [TrivRules]
% 1.75/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.75/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.75/0.95  --sup_immed_bw_main                     []
% 1.75/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.75/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 1.75/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.75/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.75/0.95  
% 1.75/0.95  ------ Combination Options
% 1.75/0.95  
% 1.75/0.95  --comb_res_mult                         3
% 1.75/0.95  --comb_sup_mult                         2
% 1.75/0.95  --comb_inst_mult                        10
% 1.75/0.95  
% 1.75/0.95  ------ Debug Options
% 1.75/0.95  
% 1.75/0.95  --dbg_backtrace                         false
% 1.75/0.95  --dbg_dump_prop_clauses                 false
% 1.75/0.95  --dbg_dump_prop_clauses_file            -
% 1.75/0.95  --dbg_out_stat                          false
% 1.75/0.95  ------ Parsing...
% 1.75/0.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.75/0.95  
% 1.75/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.75/0.95  
% 1.75/0.95  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.75/0.95  
% 1.75/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.75/0.95  ------ Proving...
% 1.75/0.95  ------ Problem Properties 
% 1.75/0.95  
% 1.75/0.95  
% 1.75/0.95  clauses                                 15
% 1.75/0.95  conjectures                             3
% 1.75/0.95  EPR                                     3
% 1.75/0.95  Horn                                    12
% 1.75/0.95  unary                                   3
% 1.75/0.95  binary                                  7
% 1.75/0.95  lits                                    34
% 1.75/0.95  lits eq                                 19
% 1.75/0.95  fd_pure                                 0
% 1.75/0.95  fd_pseudo                               0
% 1.75/0.95  fd_cond                                 0
% 1.75/0.95  fd_pseudo_cond                          1
% 1.75/0.95  AC symbols                              0
% 1.75/0.95  
% 1.75/0.95  ------ Schedule dynamic 5 is on 
% 1.75/0.95  
% 1.75/0.95  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.75/0.95  
% 1.75/0.95  
% 1.75/0.95  ------ 
% 1.75/0.95  Current options:
% 1.75/0.95  ------ 
% 1.75/0.95  
% 1.75/0.95  ------ Input Options
% 1.75/0.95  
% 1.75/0.95  --out_options                           all
% 1.75/0.95  --tptp_safe_out                         true
% 1.75/0.95  --problem_path                          ""
% 1.75/0.95  --include_path                          ""
% 1.75/0.95  --clausifier                            res/vclausify_rel
% 1.75/0.95  --clausifier_options                    --mode clausify
% 1.75/0.95  --stdin                                 false
% 1.75/0.95  --stats_out                             all
% 1.75/0.95  
% 1.75/0.95  ------ General Options
% 1.75/0.95  
% 1.75/0.95  --fof                                   false
% 1.75/0.95  --time_out_real                         305.
% 1.75/0.95  --time_out_virtual                      -1.
% 1.75/0.95  --symbol_type_check                     false
% 1.75/0.95  --clausify_out                          false
% 1.75/0.95  --sig_cnt_out                           false
% 1.75/0.95  --trig_cnt_out                          false
% 1.75/0.95  --trig_cnt_out_tolerance                1.
% 1.75/0.95  --trig_cnt_out_sk_spl                   false
% 1.75/0.95  --abstr_cl_out                          false
% 1.75/0.95  
% 1.75/0.95  ------ Global Options
% 1.75/0.95  
% 1.75/0.95  --schedule                              default
% 1.75/0.95  --add_important_lit                     false
% 1.75/0.95  --prop_solver_per_cl                    1000
% 1.75/0.95  --min_unsat_core                        false
% 1.75/0.95  --soft_assumptions                      false
% 1.75/0.95  --soft_lemma_size                       3
% 1.75/0.95  --prop_impl_unit_size                   0
% 1.75/0.95  --prop_impl_unit                        []
% 1.75/0.95  --share_sel_clauses                     true
% 1.75/0.95  --reset_solvers                         false
% 1.75/0.95  --bc_imp_inh                            [conj_cone]
% 1.75/0.95  --conj_cone_tolerance                   3.
% 1.75/0.95  --extra_neg_conj                        none
% 1.75/0.95  --large_theory_mode                     true
% 1.75/0.95  --prolific_symb_bound                   200
% 1.75/0.95  --lt_threshold                          2000
% 1.75/0.95  --clause_weak_htbl                      true
% 1.75/0.95  --gc_record_bc_elim                     false
% 1.75/0.95  
% 1.75/0.95  ------ Preprocessing Options
% 1.75/0.95  
% 1.75/0.95  --preprocessing_flag                    true
% 1.75/0.95  --time_out_prep_mult                    0.1
% 1.75/0.95  --splitting_mode                        input
% 1.75/0.95  --splitting_grd                         true
% 1.75/0.95  --splitting_cvd                         false
% 1.75/0.95  --splitting_cvd_svl                     false
% 1.75/0.95  --splitting_nvd                         32
% 1.75/0.95  --sub_typing                            true
% 1.75/0.95  --prep_gs_sim                           true
% 1.75/0.95  --prep_unflatten                        true
% 1.75/0.95  --prep_res_sim                          true
% 1.75/0.95  --prep_upred                            true
% 1.75/0.95  --prep_sem_filter                       exhaustive
% 1.75/0.95  --prep_sem_filter_out                   false
% 1.75/0.95  --pred_elim                             true
% 1.75/0.95  --res_sim_input                         true
% 1.75/0.95  --eq_ax_congr_red                       true
% 1.75/0.95  --pure_diseq_elim                       true
% 1.75/0.95  --brand_transform                       false
% 1.75/0.95  --non_eq_to_eq                          false
% 1.75/0.95  --prep_def_merge                        true
% 1.75/0.95  --prep_def_merge_prop_impl              false
% 1.75/0.95  --prep_def_merge_mbd                    true
% 1.75/0.95  --prep_def_merge_tr_red                 false
% 1.75/0.95  --prep_def_merge_tr_cl                  false
% 1.75/0.95  --smt_preprocessing                     true
% 1.75/0.95  --smt_ac_axioms                         fast
% 1.75/0.95  --preprocessed_out                      false
% 1.75/0.95  --preprocessed_stats                    false
% 1.75/0.95  
% 1.75/0.95  ------ Abstraction refinement Options
% 1.75/0.95  
% 1.75/0.95  --abstr_ref                             []
% 1.75/0.95  --abstr_ref_prep                        false
% 1.75/0.95  --abstr_ref_until_sat                   false
% 1.75/0.95  --abstr_ref_sig_restrict                funpre
% 1.75/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 1.75/0.95  --abstr_ref_under                       []
% 1.75/0.95  
% 1.75/0.95  ------ SAT Options
% 1.75/0.95  
% 1.75/0.95  --sat_mode                              false
% 1.75/0.95  --sat_fm_restart_options                ""
% 1.75/0.95  --sat_gr_def                            false
% 1.75/0.95  --sat_epr_types                         true
% 1.75/0.95  --sat_non_cyclic_types                  false
% 1.75/0.95  --sat_finite_models                     false
% 1.75/0.95  --sat_fm_lemmas                         false
% 1.75/0.95  --sat_fm_prep                           false
% 1.75/0.95  --sat_fm_uc_incr                        true
% 1.75/0.95  --sat_out_model                         small
% 1.75/0.95  --sat_out_clauses                       false
% 1.75/0.95  
% 1.75/0.95  ------ QBF Options
% 1.75/0.95  
% 1.75/0.95  --qbf_mode                              false
% 1.75/0.95  --qbf_elim_univ                         false
% 1.75/0.95  --qbf_dom_inst                          none
% 1.75/0.95  --qbf_dom_pre_inst                      false
% 1.75/0.95  --qbf_sk_in                             false
% 1.75/0.95  --qbf_pred_elim                         true
% 1.75/0.95  --qbf_split                             512
% 1.75/0.95  
% 1.75/0.95  ------ BMC1 Options
% 1.75/0.95  
% 1.75/0.95  --bmc1_incremental                      false
% 1.75/0.95  --bmc1_axioms                           reachable_all
% 1.75/0.95  --bmc1_min_bound                        0
% 1.75/0.95  --bmc1_max_bound                        -1
% 1.75/0.95  --bmc1_max_bound_default                -1
% 1.75/0.95  --bmc1_symbol_reachability              true
% 1.75/0.95  --bmc1_property_lemmas                  false
% 1.75/0.95  --bmc1_k_induction                      false
% 1.75/0.95  --bmc1_non_equiv_states                 false
% 1.75/0.95  --bmc1_deadlock                         false
% 1.75/0.95  --bmc1_ucm                              false
% 1.75/0.95  --bmc1_add_unsat_core                   none
% 1.75/0.95  --bmc1_unsat_core_children              false
% 1.75/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 1.75/0.95  --bmc1_out_stat                         full
% 1.75/0.95  --bmc1_ground_init                      false
% 1.75/0.95  --bmc1_pre_inst_next_state              false
% 1.75/0.95  --bmc1_pre_inst_state                   false
% 1.75/0.95  --bmc1_pre_inst_reach_state             false
% 1.75/0.95  --bmc1_out_unsat_core                   false
% 1.75/0.95  --bmc1_aig_witness_out                  false
% 1.75/0.95  --bmc1_verbose                          false
% 1.75/0.95  --bmc1_dump_clauses_tptp                false
% 1.75/0.95  --bmc1_dump_unsat_core_tptp             false
% 1.75/0.95  --bmc1_dump_file                        -
% 1.75/0.95  --bmc1_ucm_expand_uc_limit              128
% 1.75/0.95  --bmc1_ucm_n_expand_iterations          6
% 1.75/0.95  --bmc1_ucm_extend_mode                  1
% 1.75/0.95  --bmc1_ucm_init_mode                    2
% 1.75/0.95  --bmc1_ucm_cone_mode                    none
% 1.75/0.95  --bmc1_ucm_reduced_relation_type        0
% 1.75/0.95  --bmc1_ucm_relax_model                  4
% 1.75/0.95  --bmc1_ucm_full_tr_after_sat            true
% 1.75/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 1.75/0.95  --bmc1_ucm_layered_model                none
% 1.75/0.95  --bmc1_ucm_max_lemma_size               10
% 1.75/0.95  
% 1.75/0.95  ------ AIG Options
% 1.75/0.95  
% 1.75/0.95  --aig_mode                              false
% 1.75/0.95  
% 1.75/0.95  ------ Instantiation Options
% 1.75/0.95  
% 1.75/0.95  --instantiation_flag                    true
% 1.75/0.95  --inst_sos_flag                         false
% 1.75/0.95  --inst_sos_phase                        true
% 1.75/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.75/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.75/0.95  --inst_lit_sel_side                     none
% 1.75/0.95  --inst_solver_per_active                1400
% 1.75/0.95  --inst_solver_calls_frac                1.
% 1.75/0.95  --inst_passive_queue_type               priority_queues
% 1.75/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.75/0.95  --inst_passive_queues_freq              [25;2]
% 1.75/0.95  --inst_dismatching                      true
% 1.75/0.95  --inst_eager_unprocessed_to_passive     true
% 1.75/0.95  --inst_prop_sim_given                   true
% 1.75/0.95  --inst_prop_sim_new                     false
% 1.75/0.95  --inst_subs_new                         false
% 1.75/0.95  --inst_eq_res_simp                      false
% 1.75/0.95  --inst_subs_given                       false
% 1.75/0.95  --inst_orphan_elimination               true
% 1.75/0.95  --inst_learning_loop_flag               true
% 1.75/0.95  --inst_learning_start                   3000
% 1.75/0.95  --inst_learning_factor                  2
% 1.75/0.95  --inst_start_prop_sim_after_learn       3
% 1.75/0.95  --inst_sel_renew                        solver
% 1.75/0.95  --inst_lit_activity_flag                true
% 1.75/0.95  --inst_restr_to_given                   false
% 1.75/0.95  --inst_activity_threshold               500
% 1.75/0.95  --inst_out_proof                        true
% 1.75/0.95  
% 1.75/0.95  ------ Resolution Options
% 1.75/0.95  
% 1.75/0.95  --resolution_flag                       false
% 1.75/0.95  --res_lit_sel                           adaptive
% 1.75/0.95  --res_lit_sel_side                      none
% 1.75/0.95  --res_ordering                          kbo
% 1.75/0.95  --res_to_prop_solver                    active
% 1.75/0.95  --res_prop_simpl_new                    false
% 1.75/0.95  --res_prop_simpl_given                  true
% 1.75/0.95  --res_passive_queue_type                priority_queues
% 1.75/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.75/0.95  --res_passive_queues_freq               [15;5]
% 1.75/0.95  --res_forward_subs                      full
% 1.75/0.95  --res_backward_subs                     full
% 1.75/0.95  --res_forward_subs_resolution           true
% 1.75/0.95  --res_backward_subs_resolution          true
% 1.75/0.95  --res_orphan_elimination                true
% 1.75/0.95  --res_time_limit                        2.
% 1.75/0.95  --res_out_proof                         true
% 1.75/0.95  
% 1.75/0.95  ------ Superposition Options
% 1.75/0.95  
% 1.75/0.95  --superposition_flag                    true
% 1.75/0.95  --sup_passive_queue_type                priority_queues
% 1.75/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.75/0.95  --sup_passive_queues_freq               [8;1;4]
% 1.75/0.95  --demod_completeness_check              fast
% 1.75/0.95  --demod_use_ground                      true
% 1.75/0.95  --sup_to_prop_solver                    passive
% 1.75/0.95  --sup_prop_simpl_new                    true
% 1.75/0.95  --sup_prop_simpl_given                  true
% 1.75/0.95  --sup_fun_splitting                     false
% 1.75/0.95  --sup_smt_interval                      50000
% 1.75/0.95  
% 1.75/0.95  ------ Superposition Simplification Setup
% 1.75/0.95  
% 1.75/0.95  --sup_indices_passive                   []
% 1.75/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.75/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.75/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.75/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 1.75/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.75/0.95  --sup_full_bw                           [BwDemod]
% 1.75/0.95  --sup_immed_triv                        [TrivRules]
% 1.75/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.75/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.75/0.95  --sup_immed_bw_main                     []
% 1.75/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.75/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 1.75/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.75/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.75/0.95  
% 1.75/0.95  ------ Combination Options
% 1.75/0.95  
% 1.75/0.95  --comb_res_mult                         3
% 1.75/0.95  --comb_sup_mult                         2
% 1.75/0.95  --comb_inst_mult                        10
% 1.75/0.95  
% 1.75/0.95  ------ Debug Options
% 1.75/0.95  
% 1.75/0.95  --dbg_backtrace                         false
% 1.75/0.95  --dbg_dump_prop_clauses                 false
% 1.75/0.95  --dbg_dump_prop_clauses_file            -
% 1.75/0.95  --dbg_out_stat                          false
% 1.75/0.95  
% 1.75/0.95  
% 1.75/0.95  
% 1.75/0.95  
% 1.75/0.95  ------ Proving...
% 1.75/0.95  
% 1.75/0.95  
% 1.75/0.95  % SZS status Theorem for theBenchmark.p
% 1.75/0.95  
% 1.75/0.95  % SZS output start CNFRefutation for theBenchmark.p
% 1.75/0.95  
% 1.75/0.95  fof(f2,axiom,(
% 1.75/0.95    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.75/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.95  
% 1.75/0.95  fof(f36,plain,(
% 1.75/0.95    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.75/0.95    inference(cnf_transformation,[],[f2])).
% 1.75/0.95  
% 1.75/0.95  fof(f10,conjecture,(
% 1.75/0.95    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.75/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.95  
% 1.75/0.95  fof(f11,negated_conjecture,(
% 1.75/0.95    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.75/0.95    inference(negated_conjecture,[],[f10])).
% 1.75/0.95  
% 1.75/0.95  fof(f22,plain,(
% 1.75/0.95    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.75/0.96    inference(ennf_transformation,[],[f11])).
% 1.75/0.96  
% 1.75/0.96  fof(f23,plain,(
% 1.75/0.96    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.75/0.96    inference(flattening,[],[f22])).
% 1.75/0.96  
% 1.75/0.96  fof(f31,plain,(
% 1.75/0.96    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK4(X3)) = X3 & r2_hidden(sK4(X3),X0)))) )),
% 1.75/0.96    introduced(choice_axiom,[])).
% 1.75/0.96  
% 1.75/0.96  fof(f30,plain,(
% 1.75/0.96    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK1,sK2,sK3) != sK2 & ! [X3] : (? [X4] : (k1_funct_1(sK3,X4) = X3 & r2_hidden(X4,sK1)) | ~r2_hidden(X3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 1.75/0.96    introduced(choice_axiom,[])).
% 1.75/0.96  
% 1.75/0.96  fof(f32,plain,(
% 1.75/0.96    k2_relset_1(sK1,sK2,sK3) != sK2 & ! [X3] : ((k1_funct_1(sK3,sK4(X3)) = X3 & r2_hidden(sK4(X3),sK1)) | ~r2_hidden(X3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 1.75/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f23,f31,f30])).
% 1.75/0.96  
% 1.75/0.96  fof(f52,plain,(
% 1.75/0.96    v1_funct_2(sK3,sK1,sK2)),
% 1.75/0.96    inference(cnf_transformation,[],[f32])).
% 1.75/0.96  
% 1.75/0.96  fof(f9,axiom,(
% 1.75/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.75/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.96  
% 1.75/0.96  fof(f20,plain,(
% 1.75/0.96    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.96    inference(ennf_transformation,[],[f9])).
% 1.75/0.96  
% 1.75/0.96  fof(f21,plain,(
% 1.75/0.96    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.96    inference(flattening,[],[f20])).
% 1.75/0.96  
% 1.75/0.96  fof(f29,plain,(
% 1.75/0.96    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.96    inference(nnf_transformation,[],[f21])).
% 1.75/0.96  
% 1.75/0.96  fof(f45,plain,(
% 1.75/0.96    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.75/0.96    inference(cnf_transformation,[],[f29])).
% 1.75/0.96  
% 1.75/0.96  fof(f53,plain,(
% 1.75/0.96    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.75/0.96    inference(cnf_transformation,[],[f32])).
% 1.75/0.96  
% 1.75/0.96  fof(f7,axiom,(
% 1.75/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.75/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.96  
% 1.75/0.96  fof(f18,plain,(
% 1.75/0.96    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.96    inference(ennf_transformation,[],[f7])).
% 1.75/0.96  
% 1.75/0.96  fof(f43,plain,(
% 1.75/0.96    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.75/0.96    inference(cnf_transformation,[],[f18])).
% 1.75/0.96  
% 1.75/0.96  fof(f4,axiom,(
% 1.75/0.96    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : ~(! [X3] : ~(k1_funct_1(X1,X3) = X2 & r2_hidden(X3,k1_relat_1(X1))) & r2_hidden(X2,X0)) => r1_tarski(X0,k2_relat_1(X1))))),
% 1.75/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.96  
% 1.75/0.96  fof(f14,plain,(
% 1.75/0.96    ! [X0,X1] : ((r1_tarski(X0,k2_relat_1(X1)) | ? [X2] : (! [X3] : (k1_funct_1(X1,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X1))) & r2_hidden(X2,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.75/0.96    inference(ennf_transformation,[],[f4])).
% 1.75/0.96  
% 1.75/0.96  fof(f15,plain,(
% 1.75/0.96    ! [X0,X1] : (r1_tarski(X0,k2_relat_1(X1)) | ? [X2] : (! [X3] : (k1_funct_1(X1,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X1))) & r2_hidden(X2,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.75/0.96    inference(flattening,[],[f14])).
% 1.75/0.96  
% 1.75/0.96  fof(f27,plain,(
% 1.75/0.96    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X1,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X1))) & r2_hidden(X2,X0)) => (! [X3] : (k1_funct_1(X1,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X1))) & r2_hidden(sK0(X0,X1),X0)))),
% 1.75/0.96    introduced(choice_axiom,[])).
% 1.75/0.96  
% 1.75/0.96  fof(f28,plain,(
% 1.75/0.96    ! [X0,X1] : (r1_tarski(X0,k2_relat_1(X1)) | (! [X3] : (k1_funct_1(X1,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X1))) & r2_hidden(sK0(X0,X1),X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.75/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f27])).
% 1.75/0.96  
% 1.75/0.96  fof(f39,plain,(
% 1.75/0.96    ( ! [X0,X1] : (r1_tarski(X0,k2_relat_1(X1)) | r2_hidden(sK0(X0,X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.75/0.96    inference(cnf_transformation,[],[f28])).
% 1.75/0.96  
% 1.75/0.96  fof(f51,plain,(
% 1.75/0.96    v1_funct_1(sK3)),
% 1.75/0.96    inference(cnf_transformation,[],[f32])).
% 1.75/0.96  
% 1.75/0.96  fof(f5,axiom,(
% 1.75/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.75/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.96  
% 1.75/0.96  fof(f16,plain,(
% 1.75/0.96    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.96    inference(ennf_transformation,[],[f5])).
% 1.75/0.96  
% 1.75/0.96  fof(f41,plain,(
% 1.75/0.96    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.75/0.96    inference(cnf_transformation,[],[f16])).
% 1.75/0.96  
% 1.75/0.96  fof(f55,plain,(
% 1.75/0.96    ( ! [X3] : (k1_funct_1(sK3,sK4(X3)) = X3 | ~r2_hidden(X3,sK2)) )),
% 1.75/0.96    inference(cnf_transformation,[],[f32])).
% 1.75/0.96  
% 1.75/0.96  fof(f56,plain,(
% 1.75/0.96    k2_relset_1(sK1,sK2,sK3) != sK2),
% 1.75/0.96    inference(cnf_transformation,[],[f32])).
% 1.75/0.96  
% 1.75/0.96  fof(f3,axiom,(
% 1.75/0.96    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.75/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.96  
% 1.75/0.96  fof(f13,plain,(
% 1.75/0.96    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.75/0.96    inference(ennf_transformation,[],[f3])).
% 1.75/0.96  
% 1.75/0.96  fof(f26,plain,(
% 1.75/0.96    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.75/0.96    inference(nnf_transformation,[],[f13])).
% 1.75/0.96  
% 1.75/0.96  fof(f37,plain,(
% 1.75/0.96    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.75/0.96    inference(cnf_transformation,[],[f26])).
% 1.75/0.96  
% 1.75/0.96  fof(f6,axiom,(
% 1.75/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.75/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.96  
% 1.75/0.96  fof(f12,plain,(
% 1.75/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.75/0.96    inference(pure_predicate_removal,[],[f6])).
% 1.75/0.96  
% 1.75/0.96  fof(f17,plain,(
% 1.75/0.96    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.96    inference(ennf_transformation,[],[f12])).
% 1.75/0.96  
% 1.75/0.96  fof(f42,plain,(
% 1.75/0.96    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.75/0.96    inference(cnf_transformation,[],[f17])).
% 1.75/0.96  
% 1.75/0.96  fof(f8,axiom,(
% 1.75/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.75/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.96  
% 1.75/0.96  fof(f19,plain,(
% 1.75/0.96    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.96    inference(ennf_transformation,[],[f8])).
% 1.75/0.96  
% 1.75/0.96  fof(f44,plain,(
% 1.75/0.96    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.75/0.96    inference(cnf_transformation,[],[f19])).
% 1.75/0.96  
% 1.75/0.96  fof(f1,axiom,(
% 1.75/0.96    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.75/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.96  
% 1.75/0.96  fof(f24,plain,(
% 1.75/0.96    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.75/0.96    inference(nnf_transformation,[],[f1])).
% 1.75/0.96  
% 1.75/0.96  fof(f25,plain,(
% 1.75/0.96    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.75/0.96    inference(flattening,[],[f24])).
% 1.75/0.96  
% 1.75/0.96  fof(f35,plain,(
% 1.75/0.96    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.75/0.96    inference(cnf_transformation,[],[f25])).
% 1.75/0.96  
% 1.75/0.96  fof(f40,plain,(
% 1.75/0.96    ( ! [X0,X3,X1] : (r1_tarski(X0,k2_relat_1(X1)) | k1_funct_1(X1,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.75/0.96    inference(cnf_transformation,[],[f28])).
% 1.75/0.96  
% 1.75/0.96  fof(f54,plain,(
% 1.75/0.96    ( ! [X3] : (r2_hidden(sK4(X3),sK1) | ~r2_hidden(X3,sK2)) )),
% 1.75/0.96    inference(cnf_transformation,[],[f32])).
% 1.75/0.96  
% 1.75/0.96  cnf(c_754,plain,
% 1.75/0.96      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.75/0.96      theory(equality) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1559,plain,
% 1.75/0.96      ( ~ r1_tarski(X0,X1)
% 1.75/0.96      | r1_tarski(sK2,k2_relset_1(sK1,sK2,sK3))
% 1.75/0.96      | k2_relset_1(sK1,sK2,sK3) != X1
% 1.75/0.96      | sK2 != X0 ),
% 1.75/0.96      inference(instantiation,[status(thm)],[c_754]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_2228,plain,
% 1.75/0.96      ( ~ r1_tarski(X0,k2_relset_1(sK1,sK2,sK3))
% 1.75/0.96      | r1_tarski(sK2,k2_relset_1(sK1,sK2,sK3))
% 1.75/0.96      | k2_relset_1(sK1,sK2,sK3) != k2_relset_1(sK1,sK2,sK3)
% 1.75/0.96      | sK2 != X0 ),
% 1.75/0.96      inference(instantiation,[status(thm)],[c_1559]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_2230,plain,
% 1.75/0.96      ( r1_tarski(sK2,k2_relset_1(sK1,sK2,sK3))
% 1.75/0.96      | ~ r1_tarski(k1_xboole_0,k2_relset_1(sK1,sK2,sK3))
% 1.75/0.96      | k2_relset_1(sK1,sK2,sK3) != k2_relset_1(sK1,sK2,sK3)
% 1.75/0.96      | sK2 != k1_xboole_0 ),
% 1.75/0.96      inference(instantiation,[status(thm)],[c_2228]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_3,plain,
% 1.75/0.96      ( r1_tarski(k1_xboole_0,X0) ),
% 1.75/0.96      inference(cnf_transformation,[],[f36]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_2199,plain,
% 1.75/0.96      ( r1_tarski(k1_xboole_0,k2_relset_1(sK1,sK2,sK3)) ),
% 1.75/0.96      inference(instantiation,[status(thm)],[c_3]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_22,negated_conjecture,
% 1.75/0.96      ( v1_funct_2(sK3,sK1,sK2) ),
% 1.75/0.96      inference(cnf_transformation,[],[f52]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_17,plain,
% 1.75/0.96      ( ~ v1_funct_2(X0,X1,X2)
% 1.75/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.75/0.96      | k1_relset_1(X1,X2,X0) = X1
% 1.75/0.96      | k1_xboole_0 = X2 ),
% 1.75/0.96      inference(cnf_transformation,[],[f45]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_21,negated_conjecture,
% 1.75/0.96      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 1.75/0.96      inference(cnf_transformation,[],[f53]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_375,plain,
% 1.75/0.96      ( ~ v1_funct_2(X0,X1,X2)
% 1.75/0.96      | k1_relset_1(X1,X2,X0) = X1
% 1.75/0.96      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.75/0.96      | sK3 != X0
% 1.75/0.96      | k1_xboole_0 = X2 ),
% 1.75/0.96      inference(resolution_lifted,[status(thm)],[c_17,c_21]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_376,plain,
% 1.75/0.96      ( ~ v1_funct_2(sK3,X0,X1)
% 1.75/0.96      | k1_relset_1(X0,X1,sK3) = X0
% 1.75/0.96      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.75/0.96      | k1_xboole_0 = X1 ),
% 1.75/0.96      inference(unflattening,[status(thm)],[c_375]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_590,plain,
% 1.75/0.96      ( k1_relset_1(X0,X1,sK3) = X0
% 1.75/0.96      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.75/0.96      | sK3 != sK3
% 1.75/0.96      | sK2 != X1
% 1.75/0.96      | sK1 != X0
% 1.75/0.96      | k1_xboole_0 = X1 ),
% 1.75/0.96      inference(resolution_lifted,[status(thm)],[c_22,c_376]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_591,plain,
% 1.75/0.96      ( k1_relset_1(sK1,sK2,sK3) = sK1
% 1.75/0.96      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.75/0.96      | k1_xboole_0 = sK2 ),
% 1.75/0.96      inference(unflattening,[status(thm)],[c_590]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_653,plain,
% 1.75/0.96      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 1.75/0.96      inference(equality_resolution_simp,[status(thm)],[c_591]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_10,plain,
% 1.75/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.75/0.96      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.75/0.96      inference(cnf_transformation,[],[f43]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_420,plain,
% 1.75/0.96      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.75/0.96      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.75/0.96      | sK3 != X2 ),
% 1.75/0.96      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_421,plain,
% 1.75/0.96      ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
% 1.75/0.96      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.75/0.96      inference(unflattening,[status(thm)],[c_420]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1096,plain,
% 1.75/0.96      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 1.75/0.96      inference(equality_resolution,[status(thm)],[c_421]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1364,plain,
% 1.75/0.96      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 1.75/0.96      inference(superposition,[status(thm)],[c_653,c_1096]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_7,plain,
% 1.75/0.96      ( r2_hidden(sK0(X0,X1),X0)
% 1.75/0.96      | r1_tarski(X0,k2_relat_1(X1))
% 1.75/0.96      | ~ v1_funct_1(X1)
% 1.75/0.96      | ~ v1_relat_1(X1) ),
% 1.75/0.96      inference(cnf_transformation,[],[f39]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_23,negated_conjecture,
% 1.75/0.96      ( v1_funct_1(sK3) ),
% 1.75/0.96      inference(cnf_transformation,[],[f51]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_281,plain,
% 1.75/0.96      ( r2_hidden(sK0(X0,X1),X0)
% 1.75/0.96      | r1_tarski(X0,k2_relat_1(X1))
% 1.75/0.96      | ~ v1_relat_1(X1)
% 1.75/0.96      | sK3 != X1 ),
% 1.75/0.96      inference(resolution_lifted,[status(thm)],[c_7,c_23]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_282,plain,
% 1.75/0.96      ( r2_hidden(sK0(X0,sK3),X0)
% 1.75/0.96      | r1_tarski(X0,k2_relat_1(sK3))
% 1.75/0.96      | ~ v1_relat_1(sK3) ),
% 1.75/0.96      inference(unflattening,[status(thm)],[c_281]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_954,plain,
% 1.75/0.96      ( r2_hidden(sK0(X0,sK3),X0) = iProver_top
% 1.75/0.96      | r1_tarski(X0,k2_relat_1(sK3)) = iProver_top
% 1.75/0.96      | v1_relat_1(sK3) != iProver_top ),
% 1.75/0.96      inference(predicate_to_equality,[status(thm)],[c_282]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_283,plain,
% 1.75/0.96      ( r2_hidden(sK0(X0,sK3),X0) = iProver_top
% 1.75/0.96      | r1_tarski(X0,k2_relat_1(sK3)) = iProver_top
% 1.75/0.96      | v1_relat_1(sK3) != iProver_top ),
% 1.75/0.96      inference(predicate_to_equality,[status(thm)],[c_282]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_752,plain,( X0 = X0 ),theory(equality) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1053,plain,
% 1.75/0.96      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.75/0.96      inference(instantiation,[status(thm)],[c_752]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_8,plain,
% 1.75/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.75/0.96      | v1_relat_1(X0) ),
% 1.75/0.96      inference(cnf_transformation,[],[f41]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_429,plain,
% 1.75/0.96      ( v1_relat_1(X0)
% 1.75/0.96      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.75/0.96      | sK3 != X0 ),
% 1.75/0.96      inference(resolution_lifted,[status(thm)],[c_8,c_21]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_430,plain,
% 1.75/0.96      ( v1_relat_1(sK3)
% 1.75/0.96      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.75/0.96      inference(unflattening,[status(thm)],[c_429]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1108,plain,
% 1.75/0.96      ( v1_relat_1(sK3)
% 1.75/0.96      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.75/0.96      inference(instantiation,[status(thm)],[c_430]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1109,plain,
% 1.75/0.96      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.75/0.96      | v1_relat_1(sK3) = iProver_top ),
% 1.75/0.96      inference(predicate_to_equality,[status(thm)],[c_1108]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1524,plain,
% 1.75/0.96      ( r1_tarski(X0,k2_relat_1(sK3)) = iProver_top
% 1.75/0.96      | r2_hidden(sK0(X0,sK3),X0) = iProver_top ),
% 1.75/0.96      inference(global_propositional_subsumption,
% 1.75/0.96                [status(thm)],
% 1.75/0.96                [c_954,c_283,c_1053,c_1109]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1525,plain,
% 1.75/0.96      ( r2_hidden(sK0(X0,sK3),X0) = iProver_top
% 1.75/0.96      | r1_tarski(X0,k2_relat_1(sK3)) = iProver_top ),
% 1.75/0.96      inference(renaming,[status(thm)],[c_1524]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_19,negated_conjecture,
% 1.75/0.96      ( ~ r2_hidden(X0,sK2) | k1_funct_1(sK3,sK4(X0)) = X0 ),
% 1.75/0.96      inference(cnf_transformation,[],[f55]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_956,plain,
% 1.75/0.96      ( k1_funct_1(sK3,sK4(X0)) = X0 | r2_hidden(X0,sK2) != iProver_top ),
% 1.75/0.96      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1532,plain,
% 1.75/0.96      ( k1_funct_1(sK3,sK4(sK0(sK2,sK3))) = sK0(sK2,sK3)
% 1.75/0.96      | r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top ),
% 1.75/0.96      inference(superposition,[status(thm)],[c_1525,c_956]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_18,negated_conjecture,
% 1.75/0.96      ( k2_relset_1(sK1,sK2,sK3) != sK2 ),
% 1.75/0.96      inference(cnf_transformation,[],[f56]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_5,plain,
% 1.75/0.96      ( ~ v5_relat_1(X0,X1)
% 1.75/0.96      | r1_tarski(k2_relat_1(X0),X1)
% 1.75/0.96      | ~ v1_relat_1(X0) ),
% 1.75/0.96      inference(cnf_transformation,[],[f37]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_9,plain,
% 1.75/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.75/0.96      | v5_relat_1(X0,X2) ),
% 1.75/0.96      inference(cnf_transformation,[],[f42]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_260,plain,
% 1.75/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.75/0.96      | r1_tarski(k2_relat_1(X3),X4)
% 1.75/0.96      | ~ v1_relat_1(X3)
% 1.75/0.96      | X0 != X3
% 1.75/0.96      | X2 != X4 ),
% 1.75/0.96      inference(resolution_lifted,[status(thm)],[c_5,c_9]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_261,plain,
% 1.75/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.75/0.96      | r1_tarski(k2_relat_1(X0),X2)
% 1.75/0.96      | ~ v1_relat_1(X0) ),
% 1.75/0.96      inference(unflattening,[status(thm)],[c_260]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_265,plain,
% 1.75/0.96      ( r1_tarski(k2_relat_1(X0),X2)
% 1.75/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.75/0.96      inference(global_propositional_subsumption,
% 1.75/0.96                [status(thm)],
% 1.75/0.96                [c_261,c_8]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_266,plain,
% 1.75/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.75/0.96      | r1_tarski(k2_relat_1(X0),X2) ),
% 1.75/0.96      inference(renaming,[status(thm)],[c_265]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_363,plain,
% 1.75/0.96      ( r1_tarski(k2_relat_1(X0),X1)
% 1.75/0.96      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.75/0.96      | sK3 != X0 ),
% 1.75/0.96      inference(resolution_lifted,[status(thm)],[c_266,c_21]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_364,plain,
% 1.75/0.96      ( r1_tarski(k2_relat_1(sK3),X0)
% 1.75/0.96      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.75/0.96      inference(unflattening,[status(thm)],[c_363]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1054,plain,
% 1.75/0.96      ( r1_tarski(k2_relat_1(sK3),sK2)
% 1.75/0.96      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.75/0.96      inference(instantiation,[status(thm)],[c_364]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_11,plain,
% 1.75/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.75/0.96      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.75/0.96      inference(cnf_transformation,[],[f44]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_411,plain,
% 1.75/0.96      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 1.75/0.96      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.75/0.96      | sK3 != X2 ),
% 1.75/0.96      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_412,plain,
% 1.75/0.96      ( k2_relset_1(X0,X1,sK3) = k2_relat_1(sK3)
% 1.75/0.96      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.75/0.96      inference(unflattening,[status(thm)],[c_411]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1088,plain,
% 1.75/0.96      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 1.75/0.96      inference(equality_resolution,[status(thm)],[c_412]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_0,plain,
% 1.75/0.96      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 1.75/0.96      inference(cnf_transformation,[],[f35]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1100,plain,
% 1.75/0.96      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | sK2 = X0 ),
% 1.75/0.96      inference(instantiation,[status(thm)],[c_0]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1208,plain,
% 1.75/0.96      ( ~ r1_tarski(k2_relat_1(sK3),sK2)
% 1.75/0.96      | ~ r1_tarski(sK2,k2_relat_1(sK3))
% 1.75/0.96      | sK2 = k2_relat_1(sK3) ),
% 1.75/0.96      inference(instantiation,[status(thm)],[c_1100]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1533,plain,
% 1.75/0.96      ( r1_tarski(sK2,k2_relat_1(sK3))
% 1.75/0.96      | k1_funct_1(sK3,sK4(sK0(sK2,sK3))) = sK0(sK2,sK3) ),
% 1.75/0.96      inference(predicate_to_equality_rev,[status(thm)],[c_1532]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_753,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1076,plain,
% 1.75/0.96      ( k2_relset_1(sK1,sK2,sK3) != X0
% 1.75/0.96      | k2_relset_1(sK1,sK2,sK3) = sK2
% 1.75/0.96      | sK2 != X0 ),
% 1.75/0.96      inference(instantiation,[status(thm)],[c_753]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1558,plain,
% 1.75/0.96      ( k2_relset_1(sK1,sK2,sK3) != k2_relat_1(sK3)
% 1.75/0.96      | k2_relset_1(sK1,sK2,sK3) = sK2
% 1.75/0.96      | sK2 != k2_relat_1(sK3) ),
% 1.75/0.96      inference(instantiation,[status(thm)],[c_1076]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1590,plain,
% 1.75/0.96      ( k1_funct_1(sK3,sK4(sK0(sK2,sK3))) = sK0(sK2,sK3) ),
% 1.75/0.96      inference(global_propositional_subsumption,
% 1.75/0.96                [status(thm)],
% 1.75/0.96                [c_1532,c_18,c_1053,c_1054,c_1088,c_1208,c_1533,c_1558]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_6,plain,
% 1.75/0.96      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.75/0.96      | r1_tarski(X2,k2_relat_1(X1))
% 1.75/0.96      | ~ v1_funct_1(X1)
% 1.75/0.96      | ~ v1_relat_1(X1)
% 1.75/0.96      | sK0(X2,X1) != k1_funct_1(X1,X0) ),
% 1.75/0.96      inference(cnf_transformation,[],[f40]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_296,plain,
% 1.75/0.96      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.75/0.96      | r1_tarski(X2,k2_relat_1(X1))
% 1.75/0.96      | ~ v1_relat_1(X1)
% 1.75/0.96      | sK0(X2,X1) != k1_funct_1(X1,X0)
% 1.75/0.96      | sK3 != X1 ),
% 1.75/0.96      inference(resolution_lifted,[status(thm)],[c_6,c_23]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_297,plain,
% 1.75/0.96      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 1.75/0.96      | r1_tarski(X1,k2_relat_1(sK3))
% 1.75/0.96      | ~ v1_relat_1(sK3)
% 1.75/0.96      | sK0(X1,sK3) != k1_funct_1(sK3,X0) ),
% 1.75/0.96      inference(unflattening,[status(thm)],[c_296]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_953,plain,
% 1.75/0.96      ( sK0(X0,sK3) != k1_funct_1(sK3,X1)
% 1.75/0.96      | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top
% 1.75/0.96      | r1_tarski(X0,k2_relat_1(sK3)) = iProver_top
% 1.75/0.96      | v1_relat_1(sK3) != iProver_top ),
% 1.75/0.96      inference(predicate_to_equality,[status(thm)],[c_297]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_298,plain,
% 1.75/0.96      ( sK0(X0,sK3) != k1_funct_1(sK3,X1)
% 1.75/0.96      | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top
% 1.75/0.96      | r1_tarski(X0,k2_relat_1(sK3)) = iProver_top
% 1.75/0.96      | v1_relat_1(sK3) != iProver_top ),
% 1.75/0.96      inference(predicate_to_equality,[status(thm)],[c_297]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1514,plain,
% 1.75/0.96      ( r1_tarski(X0,k2_relat_1(sK3)) = iProver_top
% 1.75/0.96      | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top
% 1.75/0.96      | sK0(X0,sK3) != k1_funct_1(sK3,X1) ),
% 1.75/0.96      inference(global_propositional_subsumption,
% 1.75/0.96                [status(thm)],
% 1.75/0.96                [c_953,c_298,c_1053,c_1109]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1515,plain,
% 1.75/0.96      ( sK0(X0,sK3) != k1_funct_1(sK3,X1)
% 1.75/0.96      | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top
% 1.75/0.96      | r1_tarski(X0,k2_relat_1(sK3)) = iProver_top ),
% 1.75/0.96      inference(renaming,[status(thm)],[c_1514]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1593,plain,
% 1.75/0.96      ( sK0(X0,sK3) != sK0(sK2,sK3)
% 1.75/0.96      | r2_hidden(sK4(sK0(sK2,sK3)),k1_relat_1(sK3)) != iProver_top
% 1.75/0.96      | r1_tarski(X0,k2_relat_1(sK3)) = iProver_top ),
% 1.75/0.96      inference(superposition,[status(thm)],[c_1590,c_1515]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1655,plain,
% 1.75/0.96      ( r2_hidden(sK4(sK0(sK2,sK3)),k1_relat_1(sK3)) != iProver_top
% 1.75/0.96      | r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top ),
% 1.75/0.96      inference(equality_resolution,[status(thm)],[c_1593]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1055,plain,
% 1.75/0.96      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.75/0.96      | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
% 1.75/0.96      inference(predicate_to_equality,[status(thm)],[c_1054]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1209,plain,
% 1.75/0.96      ( sK2 = k2_relat_1(sK3)
% 1.75/0.96      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
% 1.75/0.96      | r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
% 1.75/0.96      inference(predicate_to_equality,[status(thm)],[c_1208]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1867,plain,
% 1.75/0.96      ( r2_hidden(sK4(sK0(sK2,sK3)),k1_relat_1(sK3)) != iProver_top ),
% 1.75/0.96      inference(global_propositional_subsumption,
% 1.75/0.96                [status(thm)],
% 1.75/0.96                [c_1655,c_18,c_1053,c_1055,c_1088,c_1209,c_1558]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1872,plain,
% 1.75/0.96      ( sK2 = k1_xboole_0
% 1.75/0.96      | r2_hidden(sK4(sK0(sK2,sK3)),sK1) != iProver_top ),
% 1.75/0.96      inference(superposition,[status(thm)],[c_1364,c_1867]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1552,plain,
% 1.75/0.96      ( k2_relset_1(sK1,sK2,sK3) = k2_relset_1(sK1,sK2,sK3) ),
% 1.75/0.96      inference(instantiation,[status(thm)],[c_752]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1089,plain,
% 1.75/0.96      ( ~ r1_tarski(X0,X1)
% 1.75/0.96      | r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2)
% 1.75/0.96      | k2_relset_1(sK1,sK2,sK3) != X0
% 1.75/0.96      | sK2 != X1 ),
% 1.75/0.96      inference(instantiation,[status(thm)],[c_754]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1225,plain,
% 1.75/0.96      ( ~ r1_tarski(X0,sK2)
% 1.75/0.96      | r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2)
% 1.75/0.96      | k2_relset_1(sK1,sK2,sK3) != X0
% 1.75/0.96      | sK2 != sK2 ),
% 1.75/0.96      inference(instantiation,[status(thm)],[c_1089]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1418,plain,
% 1.75/0.96      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2)
% 1.75/0.96      | ~ r1_tarski(k2_relat_1(sK3),sK2)
% 1.75/0.96      | k2_relset_1(sK1,sK2,sK3) != k2_relat_1(sK3)
% 1.75/0.96      | sK2 != sK2 ),
% 1.75/0.96      inference(instantiation,[status(thm)],[c_1225]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_20,negated_conjecture,
% 1.75/0.96      ( ~ r2_hidden(X0,sK2) | r2_hidden(sK4(X0),sK1) ),
% 1.75/0.96      inference(cnf_transformation,[],[f54]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1181,plain,
% 1.75/0.96      ( ~ r2_hidden(sK0(sK2,sK3),sK2)
% 1.75/0.96      | r2_hidden(sK4(sK0(sK2,sK3)),sK1) ),
% 1.75/0.96      inference(instantiation,[status(thm)],[c_20]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1184,plain,
% 1.75/0.96      ( r2_hidden(sK0(sK2,sK3),sK2) != iProver_top
% 1.75/0.96      | r2_hidden(sK4(sK0(sK2,sK3)),sK1) = iProver_top ),
% 1.75/0.96      inference(predicate_to_equality,[status(thm)],[c_1181]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1179,plain,
% 1.75/0.96      ( r2_hidden(sK0(sK2,sK3),sK2)
% 1.75/0.96      | r1_tarski(sK2,k2_relat_1(sK3))
% 1.75/0.96      | ~ v1_relat_1(sK3) ),
% 1.75/0.96      inference(instantiation,[status(thm)],[c_282]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1182,plain,
% 1.75/0.96      ( r2_hidden(sK0(sK2,sK3),sK2) = iProver_top
% 1.75/0.96      | r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top
% 1.75/0.96      | v1_relat_1(sK3) != iProver_top ),
% 1.75/0.96      inference(predicate_to_equality,[status(thm)],[c_1179]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1123,plain,
% 1.75/0.96      ( sK2 = sK2 ),
% 1.75/0.96      inference(instantiation,[status(thm)],[c_752]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(c_1061,plain,
% 1.75/0.96      ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2)
% 1.75/0.96      | ~ r1_tarski(sK2,k2_relset_1(sK1,sK2,sK3))
% 1.75/0.96      | k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 1.75/0.96      inference(instantiation,[status(thm)],[c_0]) ).
% 1.75/0.96  
% 1.75/0.96  cnf(contradiction,plain,
% 1.75/0.96      ( $false ),
% 1.75/0.96      inference(minisat,
% 1.75/0.96                [status(thm)],
% 1.75/0.96                [c_2230,c_2199,c_1872,c_1558,c_1552,c_1418,c_1209,c_1184,
% 1.75/0.96                 c_1182,c_1123,c_1109,c_1088,c_1061,c_1055,c_1054,c_1053,
% 1.75/0.96                 c_18]) ).
% 1.75/0.96  
% 1.75/0.96  
% 1.75/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 1.75/0.96  
% 1.75/0.96  ------                               Statistics
% 1.75/0.96  
% 1.75/0.96  ------ General
% 1.75/0.96  
% 1.75/0.96  abstr_ref_over_cycles:                  0
% 1.75/0.96  abstr_ref_under_cycles:                 0
% 1.75/0.96  gc_basic_clause_elim:                   0
% 1.75/0.96  forced_gc_time:                         0
% 1.75/0.96  parsing_time:                           0.008
% 1.75/0.96  unif_index_cands_time:                  0.
% 1.75/0.96  unif_index_add_time:                    0.
% 1.75/0.96  orderings_time:                         0.
% 1.75/0.96  out_proof_time:                         0.008
% 1.75/0.96  total_time:                             0.078
% 1.75/0.96  num_of_symbols:                         51
% 1.75/0.96  num_of_terms:                           1842
% 1.75/0.96  
% 1.75/0.96  ------ Preprocessing
% 1.75/0.96  
% 1.75/0.96  num_of_splits:                          0
% 1.75/0.96  num_of_split_atoms:                     0
% 1.75/0.96  num_of_reused_defs:                     0
% 1.75/0.96  num_eq_ax_congr_red:                    14
% 1.75/0.96  num_of_sem_filtered_clauses:            1
% 1.75/0.96  num_of_subtypes:                        0
% 1.75/0.96  monotx_restored_types:                  0
% 1.75/0.96  sat_num_of_epr_types:                   0
% 1.75/0.96  sat_num_of_non_cyclic_types:            0
% 1.75/0.96  sat_guarded_non_collapsed_types:        0
% 1.75/0.96  num_pure_diseq_elim:                    0
% 1.75/0.96  simp_replaced_by:                       0
% 1.75/0.96  res_preprocessed:                       95
% 1.75/0.96  prep_upred:                             0
% 1.75/0.96  prep_unflattend:                        32
% 1.75/0.96  smt_new_axioms:                         0
% 1.75/0.96  pred_elim_cands:                        3
% 1.75/0.96  pred_elim:                              4
% 1.75/0.96  pred_elim_cl:                           8
% 1.75/0.96  pred_elim_cycles:                       8
% 1.75/0.96  merged_defs:                            0
% 1.75/0.96  merged_defs_ncl:                        0
% 1.75/0.96  bin_hyper_res:                          0
% 1.75/0.96  prep_cycles:                            4
% 1.75/0.96  pred_elim_time:                         0.005
% 1.75/0.96  splitting_time:                         0.
% 1.75/0.96  sem_filter_time:                        0.
% 1.75/0.96  monotx_time:                            0.
% 1.75/0.96  subtype_inf_time:                       0.
% 1.75/0.96  
% 1.75/0.96  ------ Problem properties
% 1.75/0.96  
% 1.75/0.96  clauses:                                15
% 1.75/0.96  conjectures:                            3
% 1.75/0.96  epr:                                    3
% 1.75/0.96  horn:                                   12
% 1.75/0.96  ground:                                 4
% 1.75/0.96  unary:                                  3
% 1.75/0.96  binary:                                 7
% 1.75/0.96  lits:                                   34
% 1.75/0.96  lits_eq:                                19
% 1.75/0.96  fd_pure:                                0
% 1.75/0.96  fd_pseudo:                              0
% 1.75/0.96  fd_cond:                                0
% 1.75/0.96  fd_pseudo_cond:                         1
% 1.75/0.96  ac_symbols:                             0
% 1.75/0.96  
% 1.75/0.96  ------ Propositional Solver
% 1.75/0.96  
% 1.75/0.96  prop_solver_calls:                      27
% 1.75/0.96  prop_fast_solver_calls:                 612
% 1.75/0.96  smt_solver_calls:                       0
% 1.75/0.96  smt_fast_solver_calls:                  0
% 1.75/0.96  prop_num_of_clauses:                    752
% 1.75/0.96  prop_preprocess_simplified:             3162
% 1.75/0.96  prop_fo_subsumed:                       8
% 1.75/0.96  prop_solver_time:                       0.
% 1.75/0.96  smt_solver_time:                        0.
% 1.75/0.96  smt_fast_solver_time:                   0.
% 1.75/0.96  prop_fast_solver_time:                  0.
% 1.75/0.96  prop_unsat_core_time:                   0.
% 1.75/0.96  
% 1.75/0.96  ------ QBF
% 1.75/0.96  
% 1.75/0.96  qbf_q_res:                              0
% 1.75/0.96  qbf_num_tautologies:                    0
% 1.75/0.96  qbf_prep_cycles:                        0
% 1.75/0.96  
% 1.75/0.96  ------ BMC1
% 1.75/0.96  
% 1.75/0.96  bmc1_current_bound:                     -1
% 1.75/0.96  bmc1_last_solved_bound:                 -1
% 1.75/0.96  bmc1_unsat_core_size:                   -1
% 1.75/0.96  bmc1_unsat_core_parents_size:           -1
% 1.75/0.96  bmc1_merge_next_fun:                    0
% 1.75/0.96  bmc1_unsat_core_clauses_time:           0.
% 1.75/0.96  
% 1.75/0.96  ------ Instantiation
% 1.75/0.96  
% 1.75/0.96  inst_num_of_clauses:                    249
% 1.75/0.96  inst_num_in_passive:                    106
% 1.75/0.96  inst_num_in_active:                     131
% 1.75/0.96  inst_num_in_unprocessed:                12
% 1.75/0.96  inst_num_of_loops:                      159
% 1.75/0.96  inst_num_of_learning_restarts:          0
% 1.75/0.96  inst_num_moves_active_passive:          24
% 1.75/0.96  inst_lit_activity:                      0
% 1.75/0.96  inst_lit_activity_moves:                0
% 1.75/0.96  inst_num_tautologies:                   0
% 1.75/0.96  inst_num_prop_implied:                  0
% 1.75/0.96  inst_num_existing_simplified:           0
% 1.75/0.96  inst_num_eq_res_simplified:             0
% 1.75/0.96  inst_num_child_elim:                    0
% 1.75/0.96  inst_num_of_dismatching_blockings:      21
% 1.75/0.96  inst_num_of_non_proper_insts:           199
% 1.75/0.96  inst_num_of_duplicates:                 0
% 1.75/0.96  inst_inst_num_from_inst_to_res:         0
% 1.75/0.96  inst_dismatching_checking_time:         0.
% 1.75/0.96  
% 1.75/0.96  ------ Resolution
% 1.75/0.96  
% 1.75/0.96  res_num_of_clauses:                     0
% 1.75/0.96  res_num_in_passive:                     0
% 1.75/0.96  res_num_in_active:                      0
% 1.75/0.96  res_num_of_loops:                       99
% 1.75/0.96  res_forward_subset_subsumed:            34
% 1.75/0.96  res_backward_subset_subsumed:           2
% 1.75/0.96  res_forward_subsumed:                   0
% 1.75/0.96  res_backward_subsumed:                  0
% 1.75/0.96  res_forward_subsumption_resolution:     0
% 1.75/0.96  res_backward_subsumption_resolution:    0
% 1.75/0.96  res_clause_to_clause_subsumption:       124
% 1.75/0.96  res_orphan_elimination:                 0
% 1.75/0.96  res_tautology_del:                      33
% 1.75/0.96  res_num_eq_res_simplified:              1
% 1.75/0.96  res_num_sel_changes:                    0
% 1.75/0.96  res_moves_from_active_to_pass:          0
% 1.75/0.96  
% 1.75/0.96  ------ Superposition
% 1.75/0.96  
% 1.75/0.96  sup_time_total:                         0.
% 1.75/0.96  sup_time_generating:                    0.
% 1.75/0.96  sup_time_sim_full:                      0.
% 1.75/0.96  sup_time_sim_immed:                     0.
% 1.75/0.96  
% 1.75/0.96  sup_num_of_clauses:                     24
% 1.75/0.96  sup_num_in_active:                      13
% 1.75/0.96  sup_num_in_passive:                     11
% 1.75/0.96  sup_num_of_loops:                       30
% 1.75/0.96  sup_fw_superposition:                   7
% 1.75/0.96  sup_bw_superposition:                   4
% 1.75/0.96  sup_immediate_simplified:               2
% 1.75/0.96  sup_given_eliminated:                   0
% 1.75/0.96  comparisons_done:                       0
% 1.75/0.96  comparisons_avoided:                    3
% 1.75/0.96  
% 1.75/0.96  ------ Simplifications
% 1.75/0.96  
% 1.75/0.96  
% 1.75/0.96  sim_fw_subset_subsumed:                 1
% 1.75/0.96  sim_bw_subset_subsumed:                 0
% 1.75/0.96  sim_fw_subsumed:                        0
% 1.75/0.96  sim_bw_subsumed:                        1
% 1.75/0.96  sim_fw_subsumption_res:                 0
% 1.75/0.96  sim_bw_subsumption_res:                 0
% 1.75/0.96  sim_tautology_del:                      0
% 1.75/0.96  sim_eq_tautology_del:                   3
% 1.75/0.96  sim_eq_res_simp:                        1
% 1.75/0.96  sim_fw_demodulated:                     0
% 1.75/0.96  sim_bw_demodulated:                     17
% 1.75/0.96  sim_light_normalised:                   0
% 1.75/0.96  sim_joinable_taut:                      0
% 1.75/0.96  sim_joinable_simp:                      0
% 1.75/0.96  sim_ac_normalised:                      0
% 1.75/0.96  sim_smt_subsumption:                    0
% 1.75/0.96  
%------------------------------------------------------------------------------
