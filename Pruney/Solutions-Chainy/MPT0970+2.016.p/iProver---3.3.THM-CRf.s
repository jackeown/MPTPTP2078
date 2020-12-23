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
% DateTime   : Thu Dec  3 12:00:48 EST 2020

% Result     : Theorem 11.89s
% Output     : CNFRefutation 11.89s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 603 expanded)
%              Number of clauses        :  100 ( 218 expanded)
%              Number of leaves         :   20 ( 139 expanded)
%              Depth                    :   20
%              Number of atoms          :  486 (2564 expanded)
%              Number of equality atoms :  214 ( 740 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f39,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK5(X3)) = X3
        & r2_hidden(sK5(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
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

fof(f40,plain,
    ( k2_relset_1(sK2,sK3,sK4) != sK3
    & ! [X3] :
        ( ( k1_funct_1(sK4,sK5(X3)) = X3
          & r2_hidden(sK5(X3),sK2) )
        | ~ r2_hidden(X3,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f28,f39,f38])).

fof(f63,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,(
    ! [X3] :
      ( k1_funct_1(sK4,sK5(X3)) = X3
      | ~ r2_hidden(X3,sK3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f66,plain,(
    k2_relset_1(sK2,sK3,sK4) != sK3 ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK1(X0,X1),X1)
      | ~ r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,(
    ! [X3] :
      ( r2_hidden(sK5(X3),sK2)
      | ~ r2_hidden(X3,sK3) ) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1003,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_6045,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK5(sK1(k2_relat_1(sK4),sK3)),sK2)
    | X0 != sK5(sK1(k2_relat_1(sK4),sK3))
    | X1 != sK2 ),
    inference(instantiation,[status(thm)],[c_1003])).

cnf(c_14287,plain,
    ( r2_hidden(sK5(sK1(k2_relat_1(sK4),sK3)),X0)
    | ~ r2_hidden(sK5(sK1(k2_relat_1(sK4),sK3)),sK2)
    | X0 != sK2
    | sK5(sK1(k2_relat_1(sK4),sK3)) != sK5(sK1(k2_relat_1(sK4),sK3)) ),
    inference(instantiation,[status(thm)],[c_6045])).

cnf(c_37569,plain,
    ( r2_hidden(sK5(sK1(k2_relat_1(sK4),sK3)),k1_relat_1(sK4))
    | ~ r2_hidden(sK5(sK1(k2_relat_1(sK4),sK3)),sK2)
    | sK5(sK1(k2_relat_1(sK4),sK3)) != sK5(sK1(k2_relat_1(sK4),sK3))
    | k1_relat_1(sK4) != sK2 ),
    inference(instantiation,[status(thm)],[c_14287])).

cnf(c_7,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_306,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_11])).

cnf(c_307,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_311,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_307,c_10])).

cnf(c_312,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_311])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_458,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_312,c_23])).

cnf(c_459,plain,
    ( r1_tarski(k2_relat_1(sK4),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_1268,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | r1_tarski(k2_relat_1(sK4),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_459])).

cnf(c_2959,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1268])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1273,plain,
    ( X0 = X1
    | r2_hidden(sK1(X1,X0),X0) = iProver_top
    | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_21,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK4,sK5(X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1270,plain,
    ( k1_funct_1(sK4,sK5(X0)) = X0
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1495,plain,
    ( k1_funct_1(sK4,sK5(sK1(X0,sK3))) = sK1(X0,sK3)
    | sK3 = X0
    | r2_hidden(sK1(X0,sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1273,c_1270])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1275,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4741,plain,
    ( k1_funct_1(sK4,sK5(sK1(X0,sK3))) = sK1(X0,sK3)
    | sK3 = X0
    | r2_hidden(sK1(X0,sK3),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1495,c_1275])).

cnf(c_11593,plain,
    ( k1_funct_1(sK4,sK5(sK1(X0,sK3))) = sK1(X0,sK3)
    | sK3 = X0
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4741,c_1270])).

cnf(c_11751,plain,
    ( k1_funct_1(sK4,sK5(sK1(k2_relat_1(sK4),sK3))) = sK1(k2_relat_1(sK4),sK3)
    | k2_relat_1(sK4) = sK3 ),
    inference(superposition,[status(thm)],[c_2959,c_11593])).

cnf(c_20,negated_conjecture,
    ( k2_relset_1(sK2,sK3,sK4) != sK3 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_506,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_507,plain,
    ( k2_relset_1(X0,X1,sK4) = k2_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_506])).

cnf(c_1320,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_507])).

cnf(c_1000,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1335,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1000])).

cnf(c_1336,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_459])).

cnf(c_1001,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1363,plain,
    ( k2_relset_1(sK2,sK3,sK4) != X0
    | k2_relset_1(sK2,sK3,sK4) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1001])).

cnf(c_1463,plain,
    ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
    | k2_relset_1(sK2,sK3,sK4) = sK3
    | sK3 != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1363])).

cnf(c_1420,plain,
    ( r2_hidden(sK1(X0,sK3),X0)
    | r2_hidden(sK1(X0,sK3),sK3)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1535,plain,
    ( r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
    | r2_hidden(sK1(k2_relat_1(sK4),sK3),sK3)
    | sK3 = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1420])).

cnf(c_1795,plain,
    ( r2_hidden(sK1(k2_relat_1(sK4),sK3),X0)
    | ~ r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
    | ~ r1_tarski(k2_relat_1(sK4),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2694,plain,
    ( ~ r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
    | r2_hidden(sK1(k2_relat_1(sK4),sK3),sK3)
    | ~ r1_tarski(k2_relat_1(sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_1795])).

cnf(c_3494,plain,
    ( ~ r2_hidden(sK1(k2_relat_1(sK4),sK3),sK3)
    | k1_funct_1(sK4,sK5(sK1(k2_relat_1(sK4),sK3))) = sK1(k2_relat_1(sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_26326,plain,
    ( k1_funct_1(sK4,sK5(sK1(k2_relat_1(sK4),sK3))) = sK1(k2_relat_1(sK4),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11751,c_20,c_1320,c_1335,c_1336,c_1463,c_1535,c_2694,c_3494])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_286,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_25])).

cnf(c_287,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_327,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X3),k2_relat_1(sK4))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_287])).

cnf(c_328,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X2),k2_relat_1(sK4)) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_589,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_328])).

cnf(c_822,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(equality_resolution_simp,[status(thm)],[c_589])).

cnf(c_997,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_822])).

cnf(c_1266,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_997])).

cnf(c_998,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_822])).

cnf(c_1022,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_998])).

cnf(c_1023,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_997])).

cnf(c_996,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_822])).

cnf(c_1830,plain,
    ( ~ sP0_iProver_split ),
    inference(resolution,[status(thm)],[c_996,c_1000])).

cnf(c_1831,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1830])).

cnf(c_2246,plain,
    ( r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1266,c_1022,c_1023,c_1831])).

cnf(c_2247,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2246])).

cnf(c_26331,plain,
    ( r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4)) = iProver_top
    | r2_hidden(sK5(sK1(k2_relat_1(sK4),sK3)),k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_26326,c_2247])).

cnf(c_26339,plain,
    ( r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
    | ~ r2_hidden(sK5(sK1(k2_relat_1(sK4),sK3)),k1_relat_1(sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_26331])).

cnf(c_14288,plain,
    ( sK5(sK1(k2_relat_1(sK4),sK3)) = sK5(sK1(k2_relat_1(sK4),sK3)) ),
    inference(instantiation,[status(thm)],[c_1000])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1272,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1545,plain,
    ( X0 = X1
    | r2_hidden(sK1(X0,X1),X0) = iProver_top
    | r2_hidden(sK1(X0,X1),X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1273,c_1275])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1271,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5054,plain,
    ( X0 = X1
    | r2_hidden(sK1(X1,X0),X1) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X2,sK1(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1545,c_1271])).

cnf(c_7949,plain,
    ( X0 = X1
    | r2_hidden(sK1(X0,X1),X0) = iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1272,c_5054])).

cnf(c_7959,plain,
    ( X0 = X1
    | r2_hidden(sK1(X1,X0),X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7949,c_1275])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | ~ r2_hidden(sK1(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1274,plain,
    ( X0 = X1
    | r2_hidden(sK1(X1,X0),X0) != iProver_top
    | r2_hidden(sK1(X1,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8493,plain,
    ( X0 = X1
    | r2_hidden(sK1(X0,X1),X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7959,c_1274])).

cnf(c_8901,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8493,c_7949])).

cnf(c_11557,plain,
    ( k2_relat_1(sK4) = sK3
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2959,c_8901])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_470,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_23])).

cnf(c_471,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_756,plain,
    ( k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != sK4
    | sK3 != X1
    | sK2 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_471])).

cnf(c_757,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_756])).

cnf(c_821,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_757])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_515,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_23])).

cnf(c_516,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_515])).

cnf(c_1386,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_516])).

cnf(c_3733,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_821,c_1386])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(sK5(X0),sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3495,plain,
    ( ~ r2_hidden(sK1(k2_relat_1(sK4),sK3),sK3)
    | r2_hidden(sK5(sK1(k2_relat_1(sK4),sK3)),sK2) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_3314,plain,
    ( k2_relat_1(sK4) != sK3 ),
    inference(superposition,[status(thm)],[c_1320,c_20])).

cnf(c_1807,plain,
    ( ~ r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
    | ~ r2_hidden(sK1(k2_relat_1(sK4),sK3),sK3)
    | sK3 = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1002,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_1735,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,X1)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1002])).

cnf(c_1736,plain,
    ( sK3 != X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK3,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1735])).

cnf(c_1738,plain,
    ( sK3 != k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1736])).

cnf(c_77,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_79,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_77])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_37569,c_26339,c_14288,c_11557,c_3733,c_3495,c_3314,c_2694,c_1807,c_1738,c_1535,c_1463,c_1336,c_1335,c_1320,c_79,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:40:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.89/2.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.89/2.04  
% 11.89/2.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.89/2.04  
% 11.89/2.04  ------  iProver source info
% 11.89/2.04  
% 11.89/2.04  git: date: 2020-06-30 10:37:57 +0100
% 11.89/2.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.89/2.04  git: non_committed_changes: false
% 11.89/2.04  git: last_make_outside_of_git: false
% 11.89/2.04  
% 11.89/2.04  ------ 
% 11.89/2.04  ------ Parsing...
% 11.89/2.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.89/2.04  
% 11.89/2.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 11.89/2.04  
% 11.89/2.04  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.89/2.04  
% 11.89/2.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.89/2.04  ------ Proving...
% 11.89/2.04  ------ Problem Properties 
% 11.89/2.04  
% 11.89/2.04  
% 11.89/2.04  clauses                                 19
% 11.89/2.04  conjectures                             3
% 11.89/2.04  EPR                                     4
% 11.89/2.04  Horn                                    14
% 11.89/2.04  unary                                   2
% 11.89/2.04  binary                                  11
% 11.89/2.04  lits                                    43
% 11.89/2.04  lits eq                                 19
% 11.89/2.04  fd_pure                                 0
% 11.89/2.04  fd_pseudo                               0
% 11.89/2.04  fd_cond                                 0
% 11.89/2.04  fd_pseudo_cond                          2
% 11.89/2.04  AC symbols                              0
% 11.89/2.04  
% 11.89/2.04  ------ Input Options Time Limit: Unbounded
% 11.89/2.04  
% 11.89/2.04  
% 11.89/2.04  ------ 
% 11.89/2.04  Current options:
% 11.89/2.04  ------ 
% 11.89/2.04  
% 11.89/2.04  
% 11.89/2.04  
% 11.89/2.04  
% 11.89/2.04  ------ Proving...
% 11.89/2.04  
% 11.89/2.04  
% 11.89/2.04  % SZS status Theorem for theBenchmark.p
% 11.89/2.04  
% 11.89/2.04  % SZS output start CNFRefutation for theBenchmark.p
% 11.89/2.04  
% 11.89/2.04  fof(f4,axiom,(
% 11.89/2.04    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 11.89/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.89/2.04  
% 11.89/2.04  fof(f17,plain,(
% 11.89/2.04    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.89/2.04    inference(ennf_transformation,[],[f4])).
% 11.89/2.04  
% 11.89/2.04  fof(f36,plain,(
% 11.89/2.04    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.89/2.04    inference(nnf_transformation,[],[f17])).
% 11.89/2.04  
% 11.89/2.04  fof(f47,plain,(
% 11.89/2.04    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.89/2.04    inference(cnf_transformation,[],[f36])).
% 11.89/2.04  
% 11.89/2.04  fof(f8,axiom,(
% 11.89/2.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.89/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.89/2.04  
% 11.89/2.04  fof(f14,plain,(
% 11.89/2.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 11.89/2.04    inference(pure_predicate_removal,[],[f8])).
% 11.89/2.04  
% 11.89/2.04  fof(f22,plain,(
% 11.89/2.04    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.89/2.04    inference(ennf_transformation,[],[f14])).
% 11.89/2.04  
% 11.89/2.04  fof(f52,plain,(
% 11.89/2.04    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.89/2.04    inference(cnf_transformation,[],[f22])).
% 11.89/2.04  
% 11.89/2.04  fof(f7,axiom,(
% 11.89/2.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.89/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.89/2.04  
% 11.89/2.04  fof(f21,plain,(
% 11.89/2.04    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.89/2.04    inference(ennf_transformation,[],[f7])).
% 11.89/2.04  
% 11.89/2.04  fof(f51,plain,(
% 11.89/2.04    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.89/2.04    inference(cnf_transformation,[],[f21])).
% 11.89/2.04  
% 11.89/2.04  fof(f12,conjecture,(
% 11.89/2.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 11.89/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.89/2.04  
% 11.89/2.04  fof(f13,negated_conjecture,(
% 11.89/2.04    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 11.89/2.04    inference(negated_conjecture,[],[f12])).
% 11.89/2.04  
% 11.89/2.04  fof(f27,plain,(
% 11.89/2.04    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 11.89/2.04    inference(ennf_transformation,[],[f13])).
% 11.89/2.04  
% 11.89/2.04  fof(f28,plain,(
% 11.89/2.04    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 11.89/2.04    inference(flattening,[],[f27])).
% 11.89/2.04  
% 11.89/2.04  fof(f39,plain,(
% 11.89/2.04    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK5(X3)) = X3 & r2_hidden(sK5(X3),X0)))) )),
% 11.89/2.04    introduced(choice_axiom,[])).
% 11.89/2.04  
% 11.89/2.04  fof(f38,plain,(
% 11.89/2.04    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK2,sK3,sK4) != sK3 & ! [X3] : (? [X4] : (k1_funct_1(sK4,X4) = X3 & r2_hidden(X4,sK2)) | ~r2_hidden(X3,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 11.89/2.04    introduced(choice_axiom,[])).
% 11.89/2.04  
% 11.89/2.04  fof(f40,plain,(
% 11.89/2.04    k2_relset_1(sK2,sK3,sK4) != sK3 & ! [X3] : ((k1_funct_1(sK4,sK5(X3)) = X3 & r2_hidden(sK5(X3),sK2)) | ~r2_hidden(X3,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 11.89/2.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f28,f39,f38])).
% 11.89/2.04  
% 11.89/2.04  fof(f63,plain,(
% 11.89/2.04    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 11.89/2.04    inference(cnf_transformation,[],[f40])).
% 11.89/2.04  
% 11.89/2.04  fof(f2,axiom,(
% 11.89/2.04    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 11.89/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.89/2.04  
% 11.89/2.04  fof(f16,plain,(
% 11.89/2.04    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 11.89/2.04    inference(ennf_transformation,[],[f2])).
% 11.89/2.04  
% 11.89/2.04  fof(f33,plain,(
% 11.89/2.04    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 11.89/2.04    inference(nnf_transformation,[],[f16])).
% 11.89/2.04  
% 11.89/2.04  fof(f34,plain,(
% 11.89/2.04    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 11.89/2.04    introduced(choice_axiom,[])).
% 11.89/2.04  
% 11.89/2.04  fof(f35,plain,(
% 11.89/2.04    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 11.89/2.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).
% 11.89/2.04  
% 11.89/2.04  fof(f44,plain,(
% 11.89/2.04    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 11.89/2.04    inference(cnf_transformation,[],[f35])).
% 11.89/2.04  
% 11.89/2.04  fof(f65,plain,(
% 11.89/2.04    ( ! [X3] : (k1_funct_1(sK4,sK5(X3)) = X3 | ~r2_hidden(X3,sK3)) )),
% 11.89/2.04    inference(cnf_transformation,[],[f40])).
% 11.89/2.04  
% 11.89/2.04  fof(f1,axiom,(
% 11.89/2.04    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.89/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.89/2.04  
% 11.89/2.04  fof(f15,plain,(
% 11.89/2.04    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.89/2.04    inference(ennf_transformation,[],[f1])).
% 11.89/2.04  
% 11.89/2.04  fof(f29,plain,(
% 11.89/2.04    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.89/2.04    inference(nnf_transformation,[],[f15])).
% 11.89/2.04  
% 11.89/2.04  fof(f30,plain,(
% 11.89/2.04    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.89/2.04    inference(rectify,[],[f29])).
% 11.89/2.04  
% 11.89/2.04  fof(f31,plain,(
% 11.89/2.04    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.89/2.04    introduced(choice_axiom,[])).
% 11.89/2.04  
% 11.89/2.04  fof(f32,plain,(
% 11.89/2.04    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.89/2.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 11.89/2.04  
% 11.89/2.04  fof(f41,plain,(
% 11.89/2.04    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 11.89/2.04    inference(cnf_transformation,[],[f32])).
% 11.89/2.04  
% 11.89/2.04  fof(f66,plain,(
% 11.89/2.04    k2_relset_1(sK2,sK3,sK4) != sK3),
% 11.89/2.04    inference(cnf_transformation,[],[f40])).
% 11.89/2.04  
% 11.89/2.04  fof(f10,axiom,(
% 11.89/2.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.89/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.89/2.04  
% 11.89/2.04  fof(f24,plain,(
% 11.89/2.04    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.89/2.04    inference(ennf_transformation,[],[f10])).
% 11.89/2.04  
% 11.89/2.04  fof(f54,plain,(
% 11.89/2.04    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.89/2.04    inference(cnf_transformation,[],[f24])).
% 11.89/2.04  
% 11.89/2.04  fof(f5,axiom,(
% 11.89/2.04    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 11.89/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.89/2.04  
% 11.89/2.04  fof(f18,plain,(
% 11.89/2.04    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.89/2.04    inference(ennf_transformation,[],[f5])).
% 11.89/2.04  
% 11.89/2.04  fof(f19,plain,(
% 11.89/2.04    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.89/2.04    inference(flattening,[],[f18])).
% 11.89/2.04  
% 11.89/2.04  fof(f49,plain,(
% 11.89/2.04    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.89/2.04    inference(cnf_transformation,[],[f19])).
% 11.89/2.04  
% 11.89/2.04  fof(f61,plain,(
% 11.89/2.04    v1_funct_1(sK4)),
% 11.89/2.04    inference(cnf_transformation,[],[f40])).
% 11.89/2.04  
% 11.89/2.04  fof(f3,axiom,(
% 11.89/2.04    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.89/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.89/2.04  
% 11.89/2.04  fof(f46,plain,(
% 11.89/2.04    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.89/2.04    inference(cnf_transformation,[],[f3])).
% 11.89/2.04  
% 11.89/2.04  fof(f6,axiom,(
% 11.89/2.04    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 11.89/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.89/2.04  
% 11.89/2.04  fof(f20,plain,(
% 11.89/2.04    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 11.89/2.04    inference(ennf_transformation,[],[f6])).
% 11.89/2.04  
% 11.89/2.04  fof(f50,plain,(
% 11.89/2.04    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 11.89/2.04    inference(cnf_transformation,[],[f20])).
% 11.89/2.04  
% 11.89/2.04  fof(f45,plain,(
% 11.89/2.04    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) )),
% 11.89/2.04    inference(cnf_transformation,[],[f35])).
% 11.89/2.04  
% 11.89/2.04  fof(f62,plain,(
% 11.89/2.04    v1_funct_2(sK4,sK2,sK3)),
% 11.89/2.04    inference(cnf_transformation,[],[f40])).
% 11.89/2.04  
% 11.89/2.04  fof(f11,axiom,(
% 11.89/2.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 11.89/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.89/2.04  
% 11.89/2.04  fof(f25,plain,(
% 11.89/2.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.89/2.04    inference(ennf_transformation,[],[f11])).
% 11.89/2.04  
% 11.89/2.04  fof(f26,plain,(
% 11.89/2.04    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.89/2.04    inference(flattening,[],[f25])).
% 11.89/2.04  
% 11.89/2.04  fof(f37,plain,(
% 11.89/2.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.89/2.04    inference(nnf_transformation,[],[f26])).
% 11.89/2.04  
% 11.89/2.04  fof(f55,plain,(
% 11.89/2.04    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.89/2.04    inference(cnf_transformation,[],[f37])).
% 11.89/2.04  
% 11.89/2.04  fof(f9,axiom,(
% 11.89/2.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 11.89/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.89/2.04  
% 11.89/2.04  fof(f23,plain,(
% 11.89/2.04    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.89/2.04    inference(ennf_transformation,[],[f9])).
% 11.89/2.04  
% 11.89/2.04  fof(f53,plain,(
% 11.89/2.04    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.89/2.04    inference(cnf_transformation,[],[f23])).
% 11.89/2.04  
% 11.89/2.04  fof(f64,plain,(
% 11.89/2.04    ( ! [X3] : (r2_hidden(sK5(X3),sK2) | ~r2_hidden(X3,sK3)) )),
% 11.89/2.04    inference(cnf_transformation,[],[f40])).
% 11.89/2.04  
% 11.89/2.04  cnf(c_1003,plain,
% 11.89/2.04      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.89/2.04      theory(equality) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_6045,plain,
% 11.89/2.04      ( r2_hidden(X0,X1)
% 11.89/2.04      | ~ r2_hidden(sK5(sK1(k2_relat_1(sK4),sK3)),sK2)
% 11.89/2.04      | X0 != sK5(sK1(k2_relat_1(sK4),sK3))
% 11.89/2.04      | X1 != sK2 ),
% 11.89/2.04      inference(instantiation,[status(thm)],[c_1003]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_14287,plain,
% 11.89/2.04      ( r2_hidden(sK5(sK1(k2_relat_1(sK4),sK3)),X0)
% 11.89/2.04      | ~ r2_hidden(sK5(sK1(k2_relat_1(sK4),sK3)),sK2)
% 11.89/2.04      | X0 != sK2
% 11.89/2.04      | sK5(sK1(k2_relat_1(sK4),sK3)) != sK5(sK1(k2_relat_1(sK4),sK3)) ),
% 11.89/2.04      inference(instantiation,[status(thm)],[c_6045]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_37569,plain,
% 11.89/2.04      ( r2_hidden(sK5(sK1(k2_relat_1(sK4),sK3)),k1_relat_1(sK4))
% 11.89/2.04      | ~ r2_hidden(sK5(sK1(k2_relat_1(sK4),sK3)),sK2)
% 11.89/2.04      | sK5(sK1(k2_relat_1(sK4),sK3)) != sK5(sK1(k2_relat_1(sK4),sK3))
% 11.89/2.04      | k1_relat_1(sK4) != sK2 ),
% 11.89/2.04      inference(instantiation,[status(thm)],[c_14287]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_7,plain,
% 11.89/2.04      ( ~ v5_relat_1(X0,X1)
% 11.89/2.04      | r1_tarski(k2_relat_1(X0),X1)
% 11.89/2.04      | ~ v1_relat_1(X0) ),
% 11.89/2.04      inference(cnf_transformation,[],[f47]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_11,plain,
% 11.89/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.89/2.04      | v5_relat_1(X0,X2) ),
% 11.89/2.04      inference(cnf_transformation,[],[f52]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_306,plain,
% 11.89/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.89/2.04      | r1_tarski(k2_relat_1(X3),X4)
% 11.89/2.04      | ~ v1_relat_1(X3)
% 11.89/2.04      | X0 != X3
% 11.89/2.04      | X2 != X4 ),
% 11.89/2.04      inference(resolution_lifted,[status(thm)],[c_7,c_11]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_307,plain,
% 11.89/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.89/2.04      | r1_tarski(k2_relat_1(X0),X2)
% 11.89/2.04      | ~ v1_relat_1(X0) ),
% 11.89/2.04      inference(unflattening,[status(thm)],[c_306]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_10,plain,
% 11.89/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.89/2.04      | v1_relat_1(X0) ),
% 11.89/2.04      inference(cnf_transformation,[],[f51]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_311,plain,
% 11.89/2.04      ( r1_tarski(k2_relat_1(X0),X2)
% 11.89/2.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.89/2.04      inference(global_propositional_subsumption,
% 11.89/2.04                [status(thm)],
% 11.89/2.04                [c_307,c_10]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_312,plain,
% 11.89/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.89/2.04      | r1_tarski(k2_relat_1(X0),X2) ),
% 11.89/2.04      inference(renaming,[status(thm)],[c_311]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_23,negated_conjecture,
% 11.89/2.04      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 11.89/2.04      inference(cnf_transformation,[],[f63]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_458,plain,
% 11.89/2.04      ( r1_tarski(k2_relat_1(X0),X1)
% 11.89/2.04      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 11.89/2.04      | sK4 != X0 ),
% 11.89/2.04      inference(resolution_lifted,[status(thm)],[c_312,c_23]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_459,plain,
% 11.89/2.04      ( r1_tarski(k2_relat_1(sK4),X0)
% 11.89/2.04      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 11.89/2.04      inference(unflattening,[status(thm)],[c_458]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_1268,plain,
% 11.89/2.04      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 11.89/2.04      | r1_tarski(k2_relat_1(sK4),X1) = iProver_top ),
% 11.89/2.04      inference(predicate_to_equality,[status(thm)],[c_459]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_2959,plain,
% 11.89/2.04      ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
% 11.89/2.04      inference(equality_resolution,[status(thm)],[c_1268]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_4,plain,
% 11.89/2.04      ( r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0) | X1 = X0 ),
% 11.89/2.04      inference(cnf_transformation,[],[f44]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_1273,plain,
% 11.89/2.04      ( X0 = X1
% 11.89/2.04      | r2_hidden(sK1(X1,X0),X0) = iProver_top
% 11.89/2.04      | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
% 11.89/2.04      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_21,negated_conjecture,
% 11.89/2.04      ( ~ r2_hidden(X0,sK3) | k1_funct_1(sK4,sK5(X0)) = X0 ),
% 11.89/2.04      inference(cnf_transformation,[],[f65]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_1270,plain,
% 11.89/2.04      ( k1_funct_1(sK4,sK5(X0)) = X0 | r2_hidden(X0,sK3) != iProver_top ),
% 11.89/2.04      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_1495,plain,
% 11.89/2.04      ( k1_funct_1(sK4,sK5(sK1(X0,sK3))) = sK1(X0,sK3)
% 11.89/2.04      | sK3 = X0
% 11.89/2.04      | r2_hidden(sK1(X0,sK3),X0) = iProver_top ),
% 11.89/2.04      inference(superposition,[status(thm)],[c_1273,c_1270]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_2,plain,
% 11.89/2.04      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 11.89/2.04      inference(cnf_transformation,[],[f41]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_1275,plain,
% 11.89/2.04      ( r2_hidden(X0,X1) != iProver_top
% 11.89/2.04      | r2_hidden(X0,X2) = iProver_top
% 11.89/2.04      | r1_tarski(X1,X2) != iProver_top ),
% 11.89/2.04      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_4741,plain,
% 11.89/2.04      ( k1_funct_1(sK4,sK5(sK1(X0,sK3))) = sK1(X0,sK3)
% 11.89/2.04      | sK3 = X0
% 11.89/2.04      | r2_hidden(sK1(X0,sK3),X1) = iProver_top
% 11.89/2.04      | r1_tarski(X0,X1) != iProver_top ),
% 11.89/2.04      inference(superposition,[status(thm)],[c_1495,c_1275]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_11593,plain,
% 11.89/2.04      ( k1_funct_1(sK4,sK5(sK1(X0,sK3))) = sK1(X0,sK3)
% 11.89/2.04      | sK3 = X0
% 11.89/2.04      | r1_tarski(X0,sK3) != iProver_top ),
% 11.89/2.04      inference(superposition,[status(thm)],[c_4741,c_1270]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_11751,plain,
% 11.89/2.04      ( k1_funct_1(sK4,sK5(sK1(k2_relat_1(sK4),sK3))) = sK1(k2_relat_1(sK4),sK3)
% 11.89/2.04      | k2_relat_1(sK4) = sK3 ),
% 11.89/2.04      inference(superposition,[status(thm)],[c_2959,c_11593]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_20,negated_conjecture,
% 11.89/2.04      ( k2_relset_1(sK2,sK3,sK4) != sK3 ),
% 11.89/2.04      inference(cnf_transformation,[],[f66]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_13,plain,
% 11.89/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.89/2.04      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.89/2.04      inference(cnf_transformation,[],[f54]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_506,plain,
% 11.89/2.04      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 11.89/2.04      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 11.89/2.04      | sK4 != X2 ),
% 11.89/2.04      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_507,plain,
% 11.89/2.04      ( k2_relset_1(X0,X1,sK4) = k2_relat_1(sK4)
% 11.89/2.04      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 11.89/2.04      inference(unflattening,[status(thm)],[c_506]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_1320,plain,
% 11.89/2.04      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 11.89/2.04      inference(equality_resolution,[status(thm)],[c_507]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_1000,plain,( X0 = X0 ),theory(equality) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_1335,plain,
% 11.89/2.04      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 11.89/2.04      inference(instantiation,[status(thm)],[c_1000]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_1336,plain,
% 11.89/2.04      ( r1_tarski(k2_relat_1(sK4),sK3)
% 11.89/2.04      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 11.89/2.04      inference(instantiation,[status(thm)],[c_459]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_1001,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_1363,plain,
% 11.89/2.04      ( k2_relset_1(sK2,sK3,sK4) != X0
% 11.89/2.04      | k2_relset_1(sK2,sK3,sK4) = sK3
% 11.89/2.04      | sK3 != X0 ),
% 11.89/2.04      inference(instantiation,[status(thm)],[c_1001]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_1463,plain,
% 11.89/2.04      ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
% 11.89/2.04      | k2_relset_1(sK2,sK3,sK4) = sK3
% 11.89/2.04      | sK3 != k2_relat_1(sK4) ),
% 11.89/2.04      inference(instantiation,[status(thm)],[c_1363]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_1420,plain,
% 11.89/2.04      ( r2_hidden(sK1(X0,sK3),X0)
% 11.89/2.04      | r2_hidden(sK1(X0,sK3),sK3)
% 11.89/2.04      | sK3 = X0 ),
% 11.89/2.04      inference(instantiation,[status(thm)],[c_4]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_1535,plain,
% 11.89/2.04      ( r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
% 11.89/2.04      | r2_hidden(sK1(k2_relat_1(sK4),sK3),sK3)
% 11.89/2.04      | sK3 = k2_relat_1(sK4) ),
% 11.89/2.04      inference(instantiation,[status(thm)],[c_1420]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_1795,plain,
% 11.89/2.04      ( r2_hidden(sK1(k2_relat_1(sK4),sK3),X0)
% 11.89/2.04      | ~ r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
% 11.89/2.04      | ~ r1_tarski(k2_relat_1(sK4),X0) ),
% 11.89/2.04      inference(instantiation,[status(thm)],[c_2]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_2694,plain,
% 11.89/2.04      ( ~ r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
% 11.89/2.04      | r2_hidden(sK1(k2_relat_1(sK4),sK3),sK3)
% 11.89/2.04      | ~ r1_tarski(k2_relat_1(sK4),sK3) ),
% 11.89/2.04      inference(instantiation,[status(thm)],[c_1795]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_3494,plain,
% 11.89/2.04      ( ~ r2_hidden(sK1(k2_relat_1(sK4),sK3),sK3)
% 11.89/2.04      | k1_funct_1(sK4,sK5(sK1(k2_relat_1(sK4),sK3))) = sK1(k2_relat_1(sK4),sK3) ),
% 11.89/2.04      inference(instantiation,[status(thm)],[c_21]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_26326,plain,
% 11.89/2.04      ( k1_funct_1(sK4,sK5(sK1(k2_relat_1(sK4),sK3))) = sK1(k2_relat_1(sK4),sK3) ),
% 11.89/2.04      inference(global_propositional_subsumption,
% 11.89/2.04                [status(thm)],
% 11.89/2.04                [c_11751,c_20,c_1320,c_1335,c_1336,c_1463,c_1535,c_2694,
% 11.89/2.04                 c_3494]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_8,plain,
% 11.89/2.04      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 11.89/2.04      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 11.89/2.04      | ~ v1_funct_1(X1)
% 11.89/2.04      | ~ v1_relat_1(X1) ),
% 11.89/2.04      inference(cnf_transformation,[],[f49]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_25,negated_conjecture,
% 11.89/2.04      ( v1_funct_1(sK4) ),
% 11.89/2.04      inference(cnf_transformation,[],[f61]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_286,plain,
% 11.89/2.04      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 11.89/2.04      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 11.89/2.04      | ~ v1_relat_1(X1)
% 11.89/2.04      | sK4 != X1 ),
% 11.89/2.04      inference(resolution_lifted,[status(thm)],[c_8,c_25]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_287,plain,
% 11.89/2.04      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 11.89/2.04      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
% 11.89/2.04      | ~ v1_relat_1(sK4) ),
% 11.89/2.04      inference(unflattening,[status(thm)],[c_286]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_327,plain,
% 11.89/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.89/2.04      | ~ r2_hidden(X3,k1_relat_1(sK4))
% 11.89/2.04      | r2_hidden(k1_funct_1(sK4,X3),k2_relat_1(sK4))
% 11.89/2.04      | sK4 != X0 ),
% 11.89/2.04      inference(resolution_lifted,[status(thm)],[c_10,c_287]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_328,plain,
% 11.89/2.04      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.89/2.04      | ~ r2_hidden(X2,k1_relat_1(sK4))
% 11.89/2.04      | r2_hidden(k1_funct_1(sK4,X2),k2_relat_1(sK4)) ),
% 11.89/2.04      inference(unflattening,[status(thm)],[c_327]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_589,plain,
% 11.89/2.04      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 11.89/2.04      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
% 11.89/2.04      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 11.89/2.04      | sK4 != sK4 ),
% 11.89/2.04      inference(resolution_lifted,[status(thm)],[c_23,c_328]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_822,plain,
% 11.89/2.04      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 11.89/2.04      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
% 11.89/2.04      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 11.89/2.04      inference(equality_resolution_simp,[status(thm)],[c_589]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_997,plain,
% 11.89/2.04      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 11.89/2.04      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
% 11.89/2.04      | ~ sP1_iProver_split ),
% 11.89/2.04      inference(splitting,
% 11.89/2.04                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 11.89/2.04                [c_822]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_1266,plain,
% 11.89/2.04      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 11.89/2.04      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
% 11.89/2.04      | sP1_iProver_split != iProver_top ),
% 11.89/2.04      inference(predicate_to_equality,[status(thm)],[c_997]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_998,plain,
% 11.89/2.04      ( sP1_iProver_split | sP0_iProver_split ),
% 11.89/2.04      inference(splitting,
% 11.89/2.04                [splitting(split),new_symbols(definition,[])],
% 11.89/2.04                [c_822]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_1022,plain,
% 11.89/2.04      ( sP1_iProver_split = iProver_top
% 11.89/2.04      | sP0_iProver_split = iProver_top ),
% 11.89/2.04      inference(predicate_to_equality,[status(thm)],[c_998]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_1023,plain,
% 11.89/2.04      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 11.89/2.04      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
% 11.89/2.04      | sP1_iProver_split != iProver_top ),
% 11.89/2.04      inference(predicate_to_equality,[status(thm)],[c_997]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_996,plain,
% 11.89/2.04      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 11.89/2.04      | ~ sP0_iProver_split ),
% 11.89/2.04      inference(splitting,
% 11.89/2.04                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 11.89/2.04                [c_822]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_1830,plain,
% 11.89/2.04      ( ~ sP0_iProver_split ),
% 11.89/2.04      inference(resolution,[status(thm)],[c_996,c_1000]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_1831,plain,
% 11.89/2.04      ( sP0_iProver_split != iProver_top ),
% 11.89/2.04      inference(predicate_to_equality,[status(thm)],[c_1830]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_2246,plain,
% 11.89/2.04      ( r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
% 11.89/2.04      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 11.89/2.04      inference(global_propositional_subsumption,
% 11.89/2.04                [status(thm)],
% 11.89/2.04                [c_1266,c_1022,c_1023,c_1831]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_2247,plain,
% 11.89/2.04      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 11.89/2.04      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
% 11.89/2.04      inference(renaming,[status(thm)],[c_2246]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_26331,plain,
% 11.89/2.04      ( r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4)) = iProver_top
% 11.89/2.04      | r2_hidden(sK5(sK1(k2_relat_1(sK4),sK3)),k1_relat_1(sK4)) != iProver_top ),
% 11.89/2.04      inference(superposition,[status(thm)],[c_26326,c_2247]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_26339,plain,
% 11.89/2.04      ( r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
% 11.89/2.04      | ~ r2_hidden(sK5(sK1(k2_relat_1(sK4),sK3)),k1_relat_1(sK4)) ),
% 11.89/2.04      inference(predicate_to_equality_rev,[status(thm)],[c_26331]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_14288,plain,
% 11.89/2.04      ( sK5(sK1(k2_relat_1(sK4),sK3)) = sK5(sK1(k2_relat_1(sK4),sK3)) ),
% 11.89/2.04      inference(instantiation,[status(thm)],[c_1000]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_5,plain,
% 11.89/2.04      ( r1_tarski(k1_xboole_0,X0) ),
% 11.89/2.04      inference(cnf_transformation,[],[f46]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_1272,plain,
% 11.89/2.04      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.89/2.04      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_1545,plain,
% 11.89/2.04      ( X0 = X1
% 11.89/2.04      | r2_hidden(sK1(X0,X1),X0) = iProver_top
% 11.89/2.04      | r2_hidden(sK1(X0,X1),X2) = iProver_top
% 11.89/2.04      | r1_tarski(X1,X2) != iProver_top ),
% 11.89/2.04      inference(superposition,[status(thm)],[c_1273,c_1275]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_9,plain,
% 11.89/2.04      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 11.89/2.04      inference(cnf_transformation,[],[f50]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_1271,plain,
% 11.89/2.04      ( r2_hidden(X0,X1) != iProver_top
% 11.89/2.04      | r1_tarski(X1,X0) != iProver_top ),
% 11.89/2.04      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_5054,plain,
% 11.89/2.04      ( X0 = X1
% 11.89/2.04      | r2_hidden(sK1(X1,X0),X1) = iProver_top
% 11.89/2.04      | r1_tarski(X0,X2) != iProver_top
% 11.89/2.04      | r1_tarski(X2,sK1(X1,X0)) != iProver_top ),
% 11.89/2.04      inference(superposition,[status(thm)],[c_1545,c_1271]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_7949,plain,
% 11.89/2.04      ( X0 = X1
% 11.89/2.04      | r2_hidden(sK1(X0,X1),X0) = iProver_top
% 11.89/2.04      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 11.89/2.04      inference(superposition,[status(thm)],[c_1272,c_5054]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_7959,plain,
% 11.89/2.04      ( X0 = X1
% 11.89/2.04      | r2_hidden(sK1(X1,X0),X2) = iProver_top
% 11.89/2.04      | r1_tarski(X1,X2) != iProver_top
% 11.89/2.04      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.89/2.04      inference(superposition,[status(thm)],[c_7949,c_1275]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_3,plain,
% 11.89/2.04      ( ~ r2_hidden(sK1(X0,X1),X1)
% 11.89/2.04      | ~ r2_hidden(sK1(X0,X1),X0)
% 11.89/2.04      | X1 = X0 ),
% 11.89/2.04      inference(cnf_transformation,[],[f45]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_1274,plain,
% 11.89/2.04      ( X0 = X1
% 11.89/2.04      | r2_hidden(sK1(X1,X0),X0) != iProver_top
% 11.89/2.04      | r2_hidden(sK1(X1,X0),X1) != iProver_top ),
% 11.89/2.04      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_8493,plain,
% 11.89/2.04      ( X0 = X1
% 11.89/2.04      | r2_hidden(sK1(X0,X1),X0) != iProver_top
% 11.89/2.04      | r1_tarski(X0,X1) != iProver_top
% 11.89/2.04      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 11.89/2.04      inference(superposition,[status(thm)],[c_7959,c_1274]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_8901,plain,
% 11.89/2.04      ( X0 = X1
% 11.89/2.04      | r1_tarski(X0,X1) != iProver_top
% 11.89/2.04      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 11.89/2.04      inference(global_propositional_subsumption,
% 11.89/2.04                [status(thm)],
% 11.89/2.04                [c_8493,c_7949]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_11557,plain,
% 11.89/2.04      ( k2_relat_1(sK4) = sK3
% 11.89/2.04      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 11.89/2.04      inference(superposition,[status(thm)],[c_2959,c_8901]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_24,negated_conjecture,
% 11.89/2.04      ( v1_funct_2(sK4,sK2,sK3) ),
% 11.89/2.04      inference(cnf_transformation,[],[f62]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_19,plain,
% 11.89/2.04      ( ~ v1_funct_2(X0,X1,X2)
% 11.89/2.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.89/2.04      | k1_relset_1(X1,X2,X0) = X1
% 11.89/2.04      | k1_xboole_0 = X2 ),
% 11.89/2.04      inference(cnf_transformation,[],[f55]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_470,plain,
% 11.89/2.04      ( ~ v1_funct_2(X0,X1,X2)
% 11.89/2.04      | k1_relset_1(X1,X2,X0) = X1
% 11.89/2.04      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 11.89/2.04      | sK4 != X0
% 11.89/2.04      | k1_xboole_0 = X2 ),
% 11.89/2.04      inference(resolution_lifted,[status(thm)],[c_19,c_23]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_471,plain,
% 11.89/2.04      ( ~ v1_funct_2(sK4,X0,X1)
% 11.89/2.04      | k1_relset_1(X0,X1,sK4) = X0
% 11.89/2.04      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 11.89/2.04      | k1_xboole_0 = X1 ),
% 11.89/2.04      inference(unflattening,[status(thm)],[c_470]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_756,plain,
% 11.89/2.04      ( k1_relset_1(X0,X1,sK4) = X0
% 11.89/2.04      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 11.89/2.04      | sK4 != sK4
% 11.89/2.04      | sK3 != X1
% 11.89/2.04      | sK2 != X0
% 11.89/2.04      | k1_xboole_0 = X1 ),
% 11.89/2.04      inference(resolution_lifted,[status(thm)],[c_24,c_471]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_757,plain,
% 11.89/2.04      ( k1_relset_1(sK2,sK3,sK4) = sK2
% 11.89/2.04      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 11.89/2.04      | k1_xboole_0 = sK3 ),
% 11.89/2.04      inference(unflattening,[status(thm)],[c_756]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_821,plain,
% 11.89/2.04      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 11.89/2.04      inference(equality_resolution_simp,[status(thm)],[c_757]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_12,plain,
% 11.89/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.89/2.04      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 11.89/2.04      inference(cnf_transformation,[],[f53]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_515,plain,
% 11.89/2.04      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 11.89/2.04      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 11.89/2.04      | sK4 != X2 ),
% 11.89/2.04      inference(resolution_lifted,[status(thm)],[c_12,c_23]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_516,plain,
% 11.89/2.04      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 11.89/2.04      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 11.89/2.04      inference(unflattening,[status(thm)],[c_515]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_1386,plain,
% 11.89/2.04      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 11.89/2.04      inference(equality_resolution,[status(thm)],[c_516]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_3733,plain,
% 11.89/2.04      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 11.89/2.04      inference(superposition,[status(thm)],[c_821,c_1386]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_22,negated_conjecture,
% 11.89/2.04      ( ~ r2_hidden(X0,sK3) | r2_hidden(sK5(X0),sK2) ),
% 11.89/2.04      inference(cnf_transformation,[],[f64]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_3495,plain,
% 11.89/2.04      ( ~ r2_hidden(sK1(k2_relat_1(sK4),sK3),sK3)
% 11.89/2.04      | r2_hidden(sK5(sK1(k2_relat_1(sK4),sK3)),sK2) ),
% 11.89/2.04      inference(instantiation,[status(thm)],[c_22]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_3314,plain,
% 11.89/2.04      ( k2_relat_1(sK4) != sK3 ),
% 11.89/2.04      inference(superposition,[status(thm)],[c_1320,c_20]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_1807,plain,
% 11.89/2.04      ( ~ r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
% 11.89/2.04      | ~ r2_hidden(sK1(k2_relat_1(sK4),sK3),sK3)
% 11.89/2.04      | sK3 = k2_relat_1(sK4) ),
% 11.89/2.04      inference(instantiation,[status(thm)],[c_3]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_1002,plain,
% 11.89/2.04      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 11.89/2.04      theory(equality) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_1735,plain,
% 11.89/2.04      ( ~ r1_tarski(X0,X1) | r1_tarski(sK3,X1) | sK3 != X0 ),
% 11.89/2.04      inference(instantiation,[status(thm)],[c_1002]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_1736,plain,
% 11.89/2.04      ( sK3 != X0
% 11.89/2.04      | r1_tarski(X0,X1) != iProver_top
% 11.89/2.04      | r1_tarski(sK3,X1) = iProver_top ),
% 11.89/2.04      inference(predicate_to_equality,[status(thm)],[c_1735]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_1738,plain,
% 11.89/2.04      ( sK3 != k1_xboole_0
% 11.89/2.04      | r1_tarski(sK3,k1_xboole_0) = iProver_top
% 11.89/2.04      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 11.89/2.04      inference(instantiation,[status(thm)],[c_1736]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_77,plain,
% 11.89/2.04      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.89/2.04      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(c_79,plain,
% 11.89/2.04      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 11.89/2.04      inference(instantiation,[status(thm)],[c_77]) ).
% 11.89/2.04  
% 11.89/2.04  cnf(contradiction,plain,
% 11.89/2.04      ( $false ),
% 11.89/2.04      inference(minisat,
% 11.89/2.04                [status(thm)],
% 11.89/2.04                [c_37569,c_26339,c_14288,c_11557,c_3733,c_3495,c_3314,
% 11.89/2.04                 c_2694,c_1807,c_1738,c_1535,c_1463,c_1336,c_1335,c_1320,
% 11.89/2.04                 c_79,c_20]) ).
% 11.89/2.04  
% 11.89/2.04  
% 11.89/2.04  % SZS output end CNFRefutation for theBenchmark.p
% 11.89/2.04  
% 11.89/2.04  ------                               Statistics
% 11.89/2.04  
% 11.89/2.04  ------ Selected
% 11.89/2.04  
% 11.89/2.04  total_time:                             1.15
% 11.89/2.04  
%------------------------------------------------------------------------------
