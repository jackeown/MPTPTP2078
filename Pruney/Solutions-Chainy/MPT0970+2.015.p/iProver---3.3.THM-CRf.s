%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:48 EST 2020

% Result     : Theorem 11.99s
% Output     : CNFRefutation 11.99s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 501 expanded)
%              Number of clauses        :   90 ( 171 expanded)
%              Number of leaves         :   17 ( 110 expanded)
%              Depth                    :   17
%              Number of atoms          :  460 (2081 expanded)
%              Number of equality atoms :  219 ( 641 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f26,plain,(
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
    inference(flattening,[],[f26])).

fof(f40,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK5(X3)) = X3
        & r2_hidden(sK5(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
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

fof(f41,plain,
    ( k2_relset_1(sK2,sK3,sK4) != sK3
    & ! [X3] :
        ( ( k1_funct_1(sK4,sK5(X3)) = X3
          & r2_hidden(sK5(X3),sK2) )
        | ~ r2_hidden(X3,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f27,f40,f39])).

fof(f66,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f24,plain,(
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
    inference(flattening,[],[f24])).

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
    inference(nnf_transformation,[],[f25])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

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

fof(f32,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f33,plain,(
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

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,(
    ! [X3] :
      ( k1_funct_1(sK4,sK5(X3)) = X3
      | ~ r2_hidden(X3,sK3) ) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f28,plain,(
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

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,(
    k2_relset_1(sK2,sK3,sK4) != sK3 ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f64,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK1(X0,X1),X1)
      | ~ r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f67,plain,(
    ! [X3] :
      ( r2_hidden(sK5(X3),sK2)
      | ~ r2_hidden(X3,sK3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f35])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f70,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f49])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_650,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_653,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1460,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_650,c_653])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_29,plain,
    ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3438,plain,
    ( sK3 = k1_xboole_0
    | k1_relset_1(sK2,sK3,sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1460,c_29])).

cnf(c_3439,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3438])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_660,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1846,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_650,c_660])).

cnf(c_3440,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3439,c_1846])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_661,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v5_relat_1(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1511,plain,
    ( v5_relat_1(sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_650,c_661])).

cnf(c_10,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_664,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_667,plain,
    ( X0 = X1
    | r2_hidden(sK1(X1,X0),X0) = iProver_top
    | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK4,sK5(X0)) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_652,plain,
    ( k1_funct_1(sK4,sK5(X0)) = X0
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2325,plain,
    ( k1_funct_1(sK4,sK5(sK1(sK3,X0))) = sK1(sK3,X0)
    | sK3 = X0
    | r2_hidden(sK1(sK3,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_667,c_652])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_669,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3846,plain,
    ( k1_funct_1(sK4,sK5(sK1(sK3,X0))) = sK1(sK3,X0)
    | sK3 = X0
    | r2_hidden(sK1(sK3,X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2325,c_669])).

cnf(c_8108,plain,
    ( k1_funct_1(sK4,sK5(sK1(sK3,X0))) = sK1(sK3,X0)
    | sK3 = X0
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3846,c_652])).

cnf(c_8154,plain,
    ( k1_funct_1(sK4,sK5(sK1(sK3,k2_relat_1(X0)))) = sK1(sK3,k2_relat_1(X0))
    | k2_relat_1(X0) = sK3
    | v5_relat_1(X0,sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_664,c_8108])).

cnf(c_14541,plain,
    ( k1_funct_1(sK4,sK5(sK1(sK3,k2_relat_1(sK4)))) = sK1(sK3,k2_relat_1(sK4))
    | k2_relat_1(sK4) = sK3
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_8154])).

cnf(c_30,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_894,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_895,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_894])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_659,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1582,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_650,c_659])).

cnf(c_22,negated_conjecture,
    ( k2_relset_1(sK2,sK3,sK4) != sK3 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3329,plain,
    ( k2_relat_1(sK4) != sK3 ),
    inference(demodulation,[status(thm)],[c_1582,c_22])).

cnf(c_52923,plain,
    ( k1_funct_1(sK4,sK5(sK1(sK3,k2_relat_1(sK4)))) = sK1(sK3,k2_relat_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14541,c_30,c_895,c_3329])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_663,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_52928,plain,
    ( r2_hidden(sK1(sK3,k2_relat_1(sK4)),k2_relat_1(sK4)) = iProver_top
    | r2_hidden(sK5(sK1(sK3,k2_relat_1(sK4))),k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_52923,c_663])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_28,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_902,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v5_relat_1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_903,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v5_relat_1(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_902])).

cnf(c_984,plain,
    ( ~ v5_relat_1(sK4,X0)
    | r1_tarski(k2_relat_1(sK4),X0)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1125,plain,
    ( ~ v5_relat_1(sK4,sK3)
    | r1_tarski(k2_relat_1(sK4),sK3)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_984])).

cnf(c_1126,plain,
    ( v5_relat_1(sK4,sK3) != iProver_top
    | r1_tarski(k2_relat_1(sK4),sK3) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1125])).

cnf(c_2886,plain,
    ( r2_hidden(sK1(X0,k2_relat_1(sK4)),X0)
    | r2_hidden(sK1(X0,k2_relat_1(sK4)),k2_relat_1(sK4))
    | k2_relat_1(sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_7786,plain,
    ( r2_hidden(sK1(sK3,k2_relat_1(sK4)),k2_relat_1(sK4))
    | r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3)
    | k2_relat_1(sK4) = sK3 ),
    inference(instantiation,[status(thm)],[c_2886])).

cnf(c_7789,plain,
    ( k2_relat_1(sK4) = sK3
    | r2_hidden(sK1(sK3,k2_relat_1(sK4)),k2_relat_1(sK4)) = iProver_top
    | r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7786])).

cnf(c_2121,plain,
    ( ~ r2_hidden(sK1(sK3,X0),X0)
    | r2_hidden(sK1(sK3,X0),X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_6149,plain,
    ( ~ r2_hidden(sK1(sK3,X0),X0)
    | r2_hidden(sK1(sK3,X0),sK3)
    | ~ r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_2121])).

cnf(c_33692,plain,
    ( ~ r2_hidden(sK1(sK3,k2_relat_1(sK4)),k2_relat_1(sK4))
    | r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3)
    | ~ r1_tarski(k2_relat_1(sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_6149])).

cnf(c_33693,plain,
    ( r2_hidden(sK1(sK3,k2_relat_1(sK4)),k2_relat_1(sK4)) != iProver_top
    | r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3) = iProver_top
    | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33692])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | ~ r2_hidden(sK1(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_6150,plain,
    ( ~ r2_hidden(sK1(sK3,X0),X0)
    | ~ r2_hidden(sK1(sK3,X0),sK3)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_43743,plain,
    ( ~ r2_hidden(sK1(sK3,k2_relat_1(sK4)),k2_relat_1(sK4))
    | ~ r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3)
    | k2_relat_1(sK4) = sK3 ),
    inference(instantiation,[status(thm)],[c_6150])).

cnf(c_43750,plain,
    ( k2_relat_1(sK4) = sK3
    | r2_hidden(sK1(sK3,k2_relat_1(sK4)),k2_relat_1(sK4)) != iProver_top
    | r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43743])).

cnf(c_53109,plain,
    ( r2_hidden(sK5(sK1(sK3,k2_relat_1(sK4))),k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_52928,c_28,c_30,c_895,c_903,c_1126,c_3329,c_7789,c_33693,c_43750])).

cnf(c_53115,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK5(sK1(sK3,k2_relat_1(sK4))),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3440,c_53109])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(sK5(X0),sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_9362,plain,
    ( ~ r2_hidden(sK1(sK3,X0),sK3)
    | r2_hidden(sK5(sK1(sK3,X0)),sK2) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_43745,plain,
    ( ~ r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3)
    | r2_hidden(sK5(sK1(sK3,k2_relat_1(sK4))),sK2) ),
    inference(instantiation,[status(thm)],[c_9362])).

cnf(c_43746,plain,
    ( r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3) != iProver_top
    | r2_hidden(sK5(sK1(sK3,k2_relat_1(sK4))),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43745])).

cnf(c_2497,plain,
    ( X0 = X1
    | r2_hidden(sK1(X0,X1),X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_667,c_669])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_666,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_957,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_666])).

cnf(c_6289,plain,
    ( X0 = X1
    | r2_hidden(sK1(X1,X0),X0) = iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2497,c_957])).

cnf(c_6367,plain,
    ( X0 = X1
    | r2_hidden(sK1(X0,X1),X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6289,c_669])).

cnf(c_668,plain,
    ( X0 = X1
    | r2_hidden(sK1(X1,X0),X0) != iProver_top
    | r2_hidden(sK1(X1,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6370,plain,
    ( X0 = X1
    | r2_hidden(sK1(X0,X1),X0) != iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6289,c_668])).

cnf(c_6705,plain,
    ( X0 = X1
    | r2_hidden(sK1(X0,X1),X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_667,c_6370])).

cnf(c_6754,plain,
    ( X0 = X1
    | r2_hidden(sK1(X1,X0),X1) != iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6705,c_668])).

cnf(c_10142,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6367,c_6754])).

cnf(c_42943,plain,
    ( k2_relat_1(X0) = X1
    | v5_relat_1(X0,X1) != iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_664,c_10142])).

cnf(c_43032,plain,
    ( k2_relat_1(sK4) = sK3
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_42943])).

cnf(c_238,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_3935,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,X1)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_238])).

cnf(c_3936,plain,
    ( sK3 != X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK3,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3935])).

cnf(c_3938,plain,
    ( sK3 != k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3936])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1090,plain,
    ( r1_tarski(X0,X0) ),
    inference(resolution,[status(thm)],[c_0,c_1])).

cnf(c_1091,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1090])).

cnf(c_1093,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1091])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_53115,c_43746,c_43032,c_33693,c_7789,c_3938,c_3329,c_1126,c_1093,c_903,c_895,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 11.99/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.99/2.00  
% 11.99/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.99/2.00  
% 11.99/2.00  ------  iProver source info
% 11.99/2.00  
% 11.99/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.99/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.99/2.00  git: non_committed_changes: false
% 11.99/2.00  git: last_make_outside_of_git: false
% 11.99/2.00  
% 11.99/2.00  ------ 
% 11.99/2.00  
% 11.99/2.00  ------ Input Options
% 11.99/2.00  
% 11.99/2.00  --out_options                           all
% 11.99/2.00  --tptp_safe_out                         true
% 11.99/2.00  --problem_path                          ""
% 11.99/2.00  --include_path                          ""
% 11.99/2.00  --clausifier                            res/vclausify_rel
% 11.99/2.00  --clausifier_options                    --mode clausify
% 11.99/2.00  --stdin                                 false
% 11.99/2.00  --stats_out                             sel
% 11.99/2.00  
% 11.99/2.00  ------ General Options
% 11.99/2.00  
% 11.99/2.00  --fof                                   false
% 11.99/2.00  --time_out_real                         604.99
% 11.99/2.00  --time_out_virtual                      -1.
% 11.99/2.00  --symbol_type_check                     false
% 11.99/2.00  --clausify_out                          false
% 11.99/2.00  --sig_cnt_out                           false
% 11.99/2.00  --trig_cnt_out                          false
% 11.99/2.00  --trig_cnt_out_tolerance                1.
% 11.99/2.00  --trig_cnt_out_sk_spl                   false
% 11.99/2.00  --abstr_cl_out                          false
% 11.99/2.00  
% 11.99/2.00  ------ Global Options
% 11.99/2.00  
% 11.99/2.00  --schedule                              none
% 11.99/2.00  --add_important_lit                     false
% 11.99/2.00  --prop_solver_per_cl                    1000
% 11.99/2.00  --min_unsat_core                        false
% 11.99/2.00  --soft_assumptions                      false
% 11.99/2.00  --soft_lemma_size                       3
% 11.99/2.00  --prop_impl_unit_size                   0
% 11.99/2.00  --prop_impl_unit                        []
% 11.99/2.00  --share_sel_clauses                     true
% 11.99/2.00  --reset_solvers                         false
% 11.99/2.00  --bc_imp_inh                            [conj_cone]
% 11.99/2.00  --conj_cone_tolerance                   3.
% 11.99/2.00  --extra_neg_conj                        none
% 11.99/2.00  --large_theory_mode                     true
% 11.99/2.00  --prolific_symb_bound                   200
% 11.99/2.00  --lt_threshold                          2000
% 11.99/2.00  --clause_weak_htbl                      true
% 11.99/2.00  --gc_record_bc_elim                     false
% 11.99/2.00  
% 11.99/2.00  ------ Preprocessing Options
% 11.99/2.00  
% 11.99/2.00  --preprocessing_flag                    true
% 11.99/2.00  --time_out_prep_mult                    0.1
% 11.99/2.00  --splitting_mode                        input
% 11.99/2.00  --splitting_grd                         true
% 11.99/2.00  --splitting_cvd                         false
% 11.99/2.00  --splitting_cvd_svl                     false
% 11.99/2.00  --splitting_nvd                         32
% 11.99/2.00  --sub_typing                            true
% 11.99/2.00  --prep_gs_sim                           false
% 11.99/2.00  --prep_unflatten                        true
% 11.99/2.00  --prep_res_sim                          true
% 11.99/2.00  --prep_upred                            true
% 11.99/2.00  --prep_sem_filter                       exhaustive
% 11.99/2.00  --prep_sem_filter_out                   false
% 11.99/2.00  --pred_elim                             false
% 11.99/2.00  --res_sim_input                         true
% 11.99/2.00  --eq_ax_congr_red                       true
% 11.99/2.00  --pure_diseq_elim                       true
% 11.99/2.00  --brand_transform                       false
% 11.99/2.00  --non_eq_to_eq                          false
% 11.99/2.00  --prep_def_merge                        true
% 11.99/2.00  --prep_def_merge_prop_impl              false
% 11.99/2.00  --prep_def_merge_mbd                    true
% 11.99/2.00  --prep_def_merge_tr_red                 false
% 11.99/2.00  --prep_def_merge_tr_cl                  false
% 11.99/2.00  --smt_preprocessing                     true
% 11.99/2.00  --smt_ac_axioms                         fast
% 11.99/2.00  --preprocessed_out                      false
% 11.99/2.00  --preprocessed_stats                    false
% 11.99/2.00  
% 11.99/2.00  ------ Abstraction refinement Options
% 11.99/2.00  
% 11.99/2.00  --abstr_ref                             []
% 11.99/2.00  --abstr_ref_prep                        false
% 11.99/2.00  --abstr_ref_until_sat                   false
% 11.99/2.00  --abstr_ref_sig_restrict                funpre
% 11.99/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.99/2.00  --abstr_ref_under                       []
% 11.99/2.00  
% 11.99/2.00  ------ SAT Options
% 11.99/2.00  
% 11.99/2.00  --sat_mode                              false
% 11.99/2.00  --sat_fm_restart_options                ""
% 11.99/2.00  --sat_gr_def                            false
% 11.99/2.00  --sat_epr_types                         true
% 11.99/2.00  --sat_non_cyclic_types                  false
% 11.99/2.00  --sat_finite_models                     false
% 11.99/2.00  --sat_fm_lemmas                         false
% 11.99/2.00  --sat_fm_prep                           false
% 11.99/2.00  --sat_fm_uc_incr                        true
% 11.99/2.00  --sat_out_model                         small
% 11.99/2.00  --sat_out_clauses                       false
% 11.99/2.00  
% 11.99/2.00  ------ QBF Options
% 11.99/2.00  
% 11.99/2.00  --qbf_mode                              false
% 11.99/2.00  --qbf_elim_univ                         false
% 11.99/2.00  --qbf_dom_inst                          none
% 11.99/2.00  --qbf_dom_pre_inst                      false
% 11.99/2.00  --qbf_sk_in                             false
% 11.99/2.00  --qbf_pred_elim                         true
% 11.99/2.00  --qbf_split                             512
% 11.99/2.00  
% 11.99/2.00  ------ BMC1 Options
% 11.99/2.00  
% 11.99/2.00  --bmc1_incremental                      false
% 11.99/2.00  --bmc1_axioms                           reachable_all
% 11.99/2.00  --bmc1_min_bound                        0
% 11.99/2.00  --bmc1_max_bound                        -1
% 11.99/2.00  --bmc1_max_bound_default                -1
% 11.99/2.00  --bmc1_symbol_reachability              true
% 11.99/2.00  --bmc1_property_lemmas                  false
% 11.99/2.00  --bmc1_k_induction                      false
% 11.99/2.00  --bmc1_non_equiv_states                 false
% 11.99/2.00  --bmc1_deadlock                         false
% 11.99/2.00  --bmc1_ucm                              false
% 11.99/2.00  --bmc1_add_unsat_core                   none
% 11.99/2.00  --bmc1_unsat_core_children              false
% 11.99/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.99/2.00  --bmc1_out_stat                         full
% 11.99/2.00  --bmc1_ground_init                      false
% 11.99/2.00  --bmc1_pre_inst_next_state              false
% 11.99/2.00  --bmc1_pre_inst_state                   false
% 11.99/2.00  --bmc1_pre_inst_reach_state             false
% 11.99/2.00  --bmc1_out_unsat_core                   false
% 11.99/2.00  --bmc1_aig_witness_out                  false
% 11.99/2.00  --bmc1_verbose                          false
% 11.99/2.00  --bmc1_dump_clauses_tptp                false
% 11.99/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.99/2.00  --bmc1_dump_file                        -
% 11.99/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.99/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.99/2.00  --bmc1_ucm_extend_mode                  1
% 11.99/2.00  --bmc1_ucm_init_mode                    2
% 11.99/2.00  --bmc1_ucm_cone_mode                    none
% 11.99/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.99/2.00  --bmc1_ucm_relax_model                  4
% 11.99/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.99/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.99/2.00  --bmc1_ucm_layered_model                none
% 11.99/2.00  --bmc1_ucm_max_lemma_size               10
% 11.99/2.00  
% 11.99/2.00  ------ AIG Options
% 11.99/2.00  
% 11.99/2.00  --aig_mode                              false
% 11.99/2.00  
% 11.99/2.00  ------ Instantiation Options
% 11.99/2.00  
% 11.99/2.00  --instantiation_flag                    true
% 11.99/2.00  --inst_sos_flag                         false
% 11.99/2.00  --inst_sos_phase                        true
% 11.99/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.99/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.99/2.00  --inst_lit_sel_side                     num_symb
% 11.99/2.00  --inst_solver_per_active                1400
% 11.99/2.00  --inst_solver_calls_frac                1.
% 11.99/2.00  --inst_passive_queue_type               priority_queues
% 11.99/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.99/2.00  --inst_passive_queues_freq              [25;2]
% 11.99/2.00  --inst_dismatching                      true
% 11.99/2.00  --inst_eager_unprocessed_to_passive     true
% 11.99/2.00  --inst_prop_sim_given                   true
% 11.99/2.00  --inst_prop_sim_new                     false
% 11.99/2.00  --inst_subs_new                         false
% 11.99/2.00  --inst_eq_res_simp                      false
% 11.99/2.00  --inst_subs_given                       false
% 11.99/2.00  --inst_orphan_elimination               true
% 11.99/2.00  --inst_learning_loop_flag               true
% 11.99/2.00  --inst_learning_start                   3000
% 11.99/2.00  --inst_learning_factor                  2
% 11.99/2.00  --inst_start_prop_sim_after_learn       3
% 11.99/2.00  --inst_sel_renew                        solver
% 11.99/2.00  --inst_lit_activity_flag                true
% 11.99/2.00  --inst_restr_to_given                   false
% 11.99/2.00  --inst_activity_threshold               500
% 11.99/2.00  --inst_out_proof                        true
% 11.99/2.00  
% 11.99/2.00  ------ Resolution Options
% 11.99/2.00  
% 11.99/2.00  --resolution_flag                       true
% 11.99/2.00  --res_lit_sel                           adaptive
% 11.99/2.00  --res_lit_sel_side                      none
% 11.99/2.00  --res_ordering                          kbo
% 11.99/2.00  --res_to_prop_solver                    active
% 11.99/2.00  --res_prop_simpl_new                    false
% 11.99/2.00  --res_prop_simpl_given                  true
% 11.99/2.00  --res_passive_queue_type                priority_queues
% 11.99/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.99/2.00  --res_passive_queues_freq               [15;5]
% 11.99/2.00  --res_forward_subs                      full
% 11.99/2.00  --res_backward_subs                     full
% 11.99/2.00  --res_forward_subs_resolution           true
% 11.99/2.00  --res_backward_subs_resolution          true
% 11.99/2.00  --res_orphan_elimination                true
% 11.99/2.00  --res_time_limit                        2.
% 11.99/2.00  --res_out_proof                         true
% 11.99/2.00  
% 11.99/2.00  ------ Superposition Options
% 11.99/2.00  
% 11.99/2.00  --superposition_flag                    true
% 11.99/2.00  --sup_passive_queue_type                priority_queues
% 11.99/2.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.99/2.00  --sup_passive_queues_freq               [1;4]
% 11.99/2.00  --demod_completeness_check              fast
% 11.99/2.00  --demod_use_ground                      true
% 11.99/2.00  --sup_to_prop_solver                    passive
% 11.99/2.00  --sup_prop_simpl_new                    true
% 11.99/2.00  --sup_prop_simpl_given                  true
% 11.99/2.00  --sup_fun_splitting                     false
% 11.99/2.00  --sup_smt_interval                      50000
% 11.99/2.00  
% 11.99/2.00  ------ Superposition Simplification Setup
% 11.99/2.00  
% 11.99/2.00  --sup_indices_passive                   []
% 11.99/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.99/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.99/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.99/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.99/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.99/2.00  --sup_full_bw                           [BwDemod]
% 11.99/2.00  --sup_immed_triv                        [TrivRules]
% 11.99/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.99/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.99/2.00  --sup_immed_bw_main                     []
% 11.99/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.99/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.99/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.99/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.99/2.00  
% 11.99/2.00  ------ Combination Options
% 11.99/2.00  
% 11.99/2.00  --comb_res_mult                         3
% 11.99/2.00  --comb_sup_mult                         2
% 11.99/2.00  --comb_inst_mult                        10
% 11.99/2.00  
% 11.99/2.00  ------ Debug Options
% 11.99/2.00  
% 11.99/2.00  --dbg_backtrace                         false
% 11.99/2.00  --dbg_dump_prop_clauses                 false
% 11.99/2.00  --dbg_dump_prop_clauses_file            -
% 11.99/2.00  --dbg_out_stat                          false
% 11.99/2.00  ------ Parsing...
% 11.99/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.99/2.00  
% 11.99/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 11.99/2.00  
% 11.99/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.99/2.00  
% 11.99/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.99/2.00  ------ Proving...
% 11.99/2.00  ------ Problem Properties 
% 11.99/2.00  
% 11.99/2.00  
% 11.99/2.00  clauses                                 28
% 11.99/2.00  conjectures                             6
% 11.99/2.00  EPR                                     3
% 11.99/2.00  Horn                                    21
% 11.99/2.00  unary                                   7
% 11.99/2.00  binary                                  8
% 11.99/2.00  lits                                    66
% 11.99/2.00  lits eq                                 20
% 11.99/2.00  fd_pure                                 0
% 11.99/2.00  fd_pseudo                               0
% 11.99/2.00  fd_cond                                 4
% 11.99/2.00  fd_pseudo_cond                          2
% 11.99/2.00  AC symbols                              0
% 11.99/2.00  
% 11.99/2.00  ------ Input Options Time Limit: Unbounded
% 11.99/2.00  
% 11.99/2.00  
% 11.99/2.00  ------ 
% 11.99/2.00  Current options:
% 11.99/2.00  ------ 
% 11.99/2.00  
% 11.99/2.00  ------ Input Options
% 11.99/2.00  
% 11.99/2.00  --out_options                           all
% 11.99/2.00  --tptp_safe_out                         true
% 11.99/2.00  --problem_path                          ""
% 11.99/2.00  --include_path                          ""
% 11.99/2.00  --clausifier                            res/vclausify_rel
% 11.99/2.00  --clausifier_options                    --mode clausify
% 11.99/2.00  --stdin                                 false
% 11.99/2.00  --stats_out                             sel
% 11.99/2.00  
% 11.99/2.00  ------ General Options
% 11.99/2.00  
% 11.99/2.00  --fof                                   false
% 11.99/2.00  --time_out_real                         604.99
% 11.99/2.00  --time_out_virtual                      -1.
% 11.99/2.00  --symbol_type_check                     false
% 11.99/2.00  --clausify_out                          false
% 11.99/2.00  --sig_cnt_out                           false
% 11.99/2.00  --trig_cnt_out                          false
% 11.99/2.00  --trig_cnt_out_tolerance                1.
% 11.99/2.00  --trig_cnt_out_sk_spl                   false
% 11.99/2.00  --abstr_cl_out                          false
% 11.99/2.00  
% 11.99/2.00  ------ Global Options
% 11.99/2.00  
% 11.99/2.00  --schedule                              none
% 11.99/2.00  --add_important_lit                     false
% 11.99/2.00  --prop_solver_per_cl                    1000
% 11.99/2.00  --min_unsat_core                        false
% 11.99/2.00  --soft_assumptions                      false
% 11.99/2.00  --soft_lemma_size                       3
% 11.99/2.00  --prop_impl_unit_size                   0
% 11.99/2.00  --prop_impl_unit                        []
% 11.99/2.00  --share_sel_clauses                     true
% 11.99/2.00  --reset_solvers                         false
% 11.99/2.00  --bc_imp_inh                            [conj_cone]
% 11.99/2.00  --conj_cone_tolerance                   3.
% 11.99/2.00  --extra_neg_conj                        none
% 11.99/2.00  --large_theory_mode                     true
% 11.99/2.00  --prolific_symb_bound                   200
% 11.99/2.00  --lt_threshold                          2000
% 11.99/2.00  --clause_weak_htbl                      true
% 11.99/2.00  --gc_record_bc_elim                     false
% 11.99/2.00  
% 11.99/2.00  ------ Preprocessing Options
% 11.99/2.00  
% 11.99/2.00  --preprocessing_flag                    true
% 11.99/2.00  --time_out_prep_mult                    0.1
% 11.99/2.00  --splitting_mode                        input
% 11.99/2.00  --splitting_grd                         true
% 11.99/2.00  --splitting_cvd                         false
% 11.99/2.00  --splitting_cvd_svl                     false
% 11.99/2.00  --splitting_nvd                         32
% 11.99/2.00  --sub_typing                            true
% 11.99/2.00  --prep_gs_sim                           false
% 11.99/2.00  --prep_unflatten                        true
% 11.99/2.00  --prep_res_sim                          true
% 11.99/2.00  --prep_upred                            true
% 11.99/2.00  --prep_sem_filter                       exhaustive
% 11.99/2.00  --prep_sem_filter_out                   false
% 11.99/2.00  --pred_elim                             false
% 11.99/2.00  --res_sim_input                         true
% 11.99/2.00  --eq_ax_congr_red                       true
% 11.99/2.00  --pure_diseq_elim                       true
% 11.99/2.00  --brand_transform                       false
% 11.99/2.00  --non_eq_to_eq                          false
% 11.99/2.00  --prep_def_merge                        true
% 11.99/2.00  --prep_def_merge_prop_impl              false
% 11.99/2.00  --prep_def_merge_mbd                    true
% 11.99/2.00  --prep_def_merge_tr_red                 false
% 11.99/2.00  --prep_def_merge_tr_cl                  false
% 11.99/2.00  --smt_preprocessing                     true
% 11.99/2.00  --smt_ac_axioms                         fast
% 11.99/2.00  --preprocessed_out                      false
% 11.99/2.00  --preprocessed_stats                    false
% 11.99/2.00  
% 11.99/2.00  ------ Abstraction refinement Options
% 11.99/2.00  
% 11.99/2.00  --abstr_ref                             []
% 11.99/2.00  --abstr_ref_prep                        false
% 11.99/2.00  --abstr_ref_until_sat                   false
% 11.99/2.00  --abstr_ref_sig_restrict                funpre
% 11.99/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.99/2.00  --abstr_ref_under                       []
% 11.99/2.00  
% 11.99/2.00  ------ SAT Options
% 11.99/2.00  
% 11.99/2.00  --sat_mode                              false
% 11.99/2.00  --sat_fm_restart_options                ""
% 11.99/2.00  --sat_gr_def                            false
% 11.99/2.00  --sat_epr_types                         true
% 11.99/2.00  --sat_non_cyclic_types                  false
% 11.99/2.00  --sat_finite_models                     false
% 11.99/2.00  --sat_fm_lemmas                         false
% 11.99/2.00  --sat_fm_prep                           false
% 11.99/2.00  --sat_fm_uc_incr                        true
% 11.99/2.00  --sat_out_model                         small
% 11.99/2.00  --sat_out_clauses                       false
% 11.99/2.00  
% 11.99/2.00  ------ QBF Options
% 11.99/2.00  
% 11.99/2.00  --qbf_mode                              false
% 11.99/2.00  --qbf_elim_univ                         false
% 11.99/2.00  --qbf_dom_inst                          none
% 11.99/2.00  --qbf_dom_pre_inst                      false
% 11.99/2.00  --qbf_sk_in                             false
% 11.99/2.00  --qbf_pred_elim                         true
% 11.99/2.00  --qbf_split                             512
% 11.99/2.00  
% 11.99/2.00  ------ BMC1 Options
% 11.99/2.00  
% 11.99/2.00  --bmc1_incremental                      false
% 11.99/2.00  --bmc1_axioms                           reachable_all
% 11.99/2.00  --bmc1_min_bound                        0
% 11.99/2.00  --bmc1_max_bound                        -1
% 11.99/2.00  --bmc1_max_bound_default                -1
% 11.99/2.00  --bmc1_symbol_reachability              true
% 11.99/2.00  --bmc1_property_lemmas                  false
% 11.99/2.00  --bmc1_k_induction                      false
% 11.99/2.00  --bmc1_non_equiv_states                 false
% 11.99/2.00  --bmc1_deadlock                         false
% 11.99/2.00  --bmc1_ucm                              false
% 11.99/2.00  --bmc1_add_unsat_core                   none
% 11.99/2.00  --bmc1_unsat_core_children              false
% 11.99/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.99/2.00  --bmc1_out_stat                         full
% 11.99/2.00  --bmc1_ground_init                      false
% 11.99/2.00  --bmc1_pre_inst_next_state              false
% 11.99/2.00  --bmc1_pre_inst_state                   false
% 11.99/2.00  --bmc1_pre_inst_reach_state             false
% 11.99/2.00  --bmc1_out_unsat_core                   false
% 11.99/2.00  --bmc1_aig_witness_out                  false
% 11.99/2.00  --bmc1_verbose                          false
% 11.99/2.00  --bmc1_dump_clauses_tptp                false
% 11.99/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.99/2.00  --bmc1_dump_file                        -
% 11.99/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.99/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.99/2.00  --bmc1_ucm_extend_mode                  1
% 11.99/2.00  --bmc1_ucm_init_mode                    2
% 11.99/2.00  --bmc1_ucm_cone_mode                    none
% 11.99/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.99/2.00  --bmc1_ucm_relax_model                  4
% 11.99/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.99/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.99/2.00  --bmc1_ucm_layered_model                none
% 11.99/2.00  --bmc1_ucm_max_lemma_size               10
% 11.99/2.00  
% 11.99/2.00  ------ AIG Options
% 11.99/2.00  
% 11.99/2.00  --aig_mode                              false
% 11.99/2.00  
% 11.99/2.00  ------ Instantiation Options
% 11.99/2.00  
% 11.99/2.00  --instantiation_flag                    true
% 11.99/2.00  --inst_sos_flag                         false
% 11.99/2.00  --inst_sos_phase                        true
% 11.99/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.99/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.99/2.00  --inst_lit_sel_side                     num_symb
% 11.99/2.00  --inst_solver_per_active                1400
% 11.99/2.00  --inst_solver_calls_frac                1.
% 11.99/2.00  --inst_passive_queue_type               priority_queues
% 11.99/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.99/2.00  --inst_passive_queues_freq              [25;2]
% 11.99/2.00  --inst_dismatching                      true
% 11.99/2.00  --inst_eager_unprocessed_to_passive     true
% 11.99/2.00  --inst_prop_sim_given                   true
% 11.99/2.00  --inst_prop_sim_new                     false
% 11.99/2.00  --inst_subs_new                         false
% 11.99/2.00  --inst_eq_res_simp                      false
% 11.99/2.00  --inst_subs_given                       false
% 11.99/2.00  --inst_orphan_elimination               true
% 11.99/2.00  --inst_learning_loop_flag               true
% 11.99/2.00  --inst_learning_start                   3000
% 11.99/2.00  --inst_learning_factor                  2
% 11.99/2.00  --inst_start_prop_sim_after_learn       3
% 11.99/2.00  --inst_sel_renew                        solver
% 11.99/2.00  --inst_lit_activity_flag                true
% 11.99/2.00  --inst_restr_to_given                   false
% 11.99/2.00  --inst_activity_threshold               500
% 11.99/2.00  --inst_out_proof                        true
% 11.99/2.00  
% 11.99/2.00  ------ Resolution Options
% 11.99/2.00  
% 11.99/2.00  --resolution_flag                       true
% 11.99/2.00  --res_lit_sel                           adaptive
% 11.99/2.00  --res_lit_sel_side                      none
% 11.99/2.00  --res_ordering                          kbo
% 11.99/2.00  --res_to_prop_solver                    active
% 11.99/2.00  --res_prop_simpl_new                    false
% 11.99/2.00  --res_prop_simpl_given                  true
% 11.99/2.00  --res_passive_queue_type                priority_queues
% 11.99/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.99/2.00  --res_passive_queues_freq               [15;5]
% 11.99/2.00  --res_forward_subs                      full
% 11.99/2.00  --res_backward_subs                     full
% 11.99/2.00  --res_forward_subs_resolution           true
% 11.99/2.00  --res_backward_subs_resolution          true
% 11.99/2.00  --res_orphan_elimination                true
% 11.99/2.00  --res_time_limit                        2.
% 11.99/2.00  --res_out_proof                         true
% 11.99/2.00  
% 11.99/2.00  ------ Superposition Options
% 11.99/2.00  
% 11.99/2.00  --superposition_flag                    true
% 11.99/2.00  --sup_passive_queue_type                priority_queues
% 11.99/2.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.99/2.00  --sup_passive_queues_freq               [1;4]
% 11.99/2.00  --demod_completeness_check              fast
% 11.99/2.00  --demod_use_ground                      true
% 11.99/2.00  --sup_to_prop_solver                    passive
% 11.99/2.00  --sup_prop_simpl_new                    true
% 11.99/2.00  --sup_prop_simpl_given                  true
% 11.99/2.00  --sup_fun_splitting                     false
% 11.99/2.00  --sup_smt_interval                      50000
% 11.99/2.00  
% 11.99/2.00  ------ Superposition Simplification Setup
% 11.99/2.00  
% 11.99/2.00  --sup_indices_passive                   []
% 11.99/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.99/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.99/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.99/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.99/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.99/2.00  --sup_full_bw                           [BwDemod]
% 11.99/2.00  --sup_immed_triv                        [TrivRules]
% 11.99/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.99/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.99/2.00  --sup_immed_bw_main                     []
% 11.99/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.99/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.99/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.99/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.99/2.00  
% 11.99/2.00  ------ Combination Options
% 11.99/2.00  
% 11.99/2.00  --comb_res_mult                         3
% 11.99/2.00  --comb_sup_mult                         2
% 11.99/2.00  --comb_inst_mult                        10
% 11.99/2.00  
% 11.99/2.00  ------ Debug Options
% 11.99/2.00  
% 11.99/2.00  --dbg_backtrace                         false
% 11.99/2.00  --dbg_dump_prop_clauses                 false
% 11.99/2.00  --dbg_dump_prop_clauses_file            -
% 11.99/2.00  --dbg_out_stat                          false
% 11.99/2.00  
% 11.99/2.00  
% 11.99/2.00  
% 11.99/2.00  
% 11.99/2.00  ------ Proving...
% 11.99/2.00  
% 11.99/2.00  
% 11.99/2.00  % SZS status Theorem for theBenchmark.p
% 11.99/2.00  
% 11.99/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.99/2.00  
% 11.99/2.00  fof(f12,conjecture,(
% 11.99/2.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 11.99/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f13,negated_conjecture,(
% 11.99/2.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 11.99/2.00    inference(negated_conjecture,[],[f12])).
% 11.99/2.00  
% 11.99/2.00  fof(f26,plain,(
% 11.99/2.00    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 11.99/2.00    inference(ennf_transformation,[],[f13])).
% 11.99/2.00  
% 11.99/2.00  fof(f27,plain,(
% 11.99/2.00    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 11.99/2.00    inference(flattening,[],[f26])).
% 11.99/2.00  
% 11.99/2.00  fof(f40,plain,(
% 11.99/2.00    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK5(X3)) = X3 & r2_hidden(sK5(X3),X0)))) )),
% 11.99/2.00    introduced(choice_axiom,[])).
% 11.99/2.00  
% 11.99/2.00  fof(f39,plain,(
% 11.99/2.00    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK2,sK3,sK4) != sK3 & ! [X3] : (? [X4] : (k1_funct_1(sK4,X4) = X3 & r2_hidden(X4,sK2)) | ~r2_hidden(X3,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 11.99/2.00    introduced(choice_axiom,[])).
% 11.99/2.00  
% 11.99/2.00  fof(f41,plain,(
% 11.99/2.00    k2_relset_1(sK2,sK3,sK4) != sK3 & ! [X3] : ((k1_funct_1(sK4,sK5(X3)) = X3 & r2_hidden(sK5(X3),sK2)) | ~r2_hidden(X3,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 11.99/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f27,f40,f39])).
% 11.99/2.00  
% 11.99/2.00  fof(f66,plain,(
% 11.99/2.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 11.99/2.00    inference(cnf_transformation,[],[f41])).
% 11.99/2.00  
% 11.99/2.00  fof(f11,axiom,(
% 11.99/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 11.99/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f24,plain,(
% 11.99/2.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.99/2.00    inference(ennf_transformation,[],[f11])).
% 11.99/2.00  
% 11.99/2.00  fof(f25,plain,(
% 11.99/2.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.99/2.00    inference(flattening,[],[f24])).
% 11.99/2.00  
% 11.99/2.00  fof(f38,plain,(
% 11.99/2.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.99/2.00    inference(nnf_transformation,[],[f25])).
% 11.99/2.00  
% 11.99/2.00  fof(f58,plain,(
% 11.99/2.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.99/2.00    inference(cnf_transformation,[],[f38])).
% 11.99/2.00  
% 11.99/2.00  fof(f65,plain,(
% 11.99/2.00    v1_funct_2(sK4,sK2,sK3)),
% 11.99/2.00    inference(cnf_transformation,[],[f41])).
% 11.99/2.00  
% 11.99/2.00  fof(f9,axiom,(
% 11.99/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 11.99/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f22,plain,(
% 11.99/2.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.99/2.00    inference(ennf_transformation,[],[f9])).
% 11.99/2.00  
% 11.99/2.00  fof(f56,plain,(
% 11.99/2.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.99/2.00    inference(cnf_transformation,[],[f22])).
% 11.99/2.00  
% 11.99/2.00  fof(f8,axiom,(
% 11.99/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.99/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f14,plain,(
% 11.99/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 11.99/2.00    inference(pure_predicate_removal,[],[f8])).
% 11.99/2.00  
% 11.99/2.00  fof(f21,plain,(
% 11.99/2.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.99/2.00    inference(ennf_transformation,[],[f14])).
% 11.99/2.00  
% 11.99/2.00  fof(f55,plain,(
% 11.99/2.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.99/2.00    inference(cnf_transformation,[],[f21])).
% 11.99/2.00  
% 11.99/2.00  fof(f5,axiom,(
% 11.99/2.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 11.99/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f17,plain,(
% 11.99/2.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.99/2.00    inference(ennf_transformation,[],[f5])).
% 11.99/2.00  
% 11.99/2.00  fof(f37,plain,(
% 11.99/2.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.99/2.00    inference(nnf_transformation,[],[f17])).
% 11.99/2.00  
% 11.99/2.00  fof(f51,plain,(
% 11.99/2.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f37])).
% 11.99/2.00  
% 11.99/2.00  fof(f2,axiom,(
% 11.99/2.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 11.99/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f16,plain,(
% 11.99/2.00    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 11.99/2.00    inference(ennf_transformation,[],[f2])).
% 11.99/2.00  
% 11.99/2.00  fof(f32,plain,(
% 11.99/2.00    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 11.99/2.00    inference(nnf_transformation,[],[f16])).
% 11.99/2.00  
% 11.99/2.00  fof(f33,plain,(
% 11.99/2.00    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 11.99/2.00    introduced(choice_axiom,[])).
% 11.99/2.00  
% 11.99/2.00  fof(f34,plain,(
% 11.99/2.00    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 11.99/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 11.99/2.00  
% 11.99/2.00  fof(f45,plain,(
% 11.99/2.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f34])).
% 11.99/2.00  
% 11.99/2.00  fof(f68,plain,(
% 11.99/2.00    ( ! [X3] : (k1_funct_1(sK4,sK5(X3)) = X3 | ~r2_hidden(X3,sK3)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f41])).
% 11.99/2.00  
% 11.99/2.00  fof(f1,axiom,(
% 11.99/2.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.99/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f15,plain,(
% 11.99/2.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.99/2.00    inference(ennf_transformation,[],[f1])).
% 11.99/2.00  
% 11.99/2.00  fof(f28,plain,(
% 11.99/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.99/2.00    inference(nnf_transformation,[],[f15])).
% 11.99/2.00  
% 11.99/2.00  fof(f29,plain,(
% 11.99/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.99/2.00    inference(rectify,[],[f28])).
% 11.99/2.00  
% 11.99/2.00  fof(f30,plain,(
% 11.99/2.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.99/2.00    introduced(choice_axiom,[])).
% 11.99/2.00  
% 11.99/2.00  fof(f31,plain,(
% 11.99/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.99/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 11.99/2.00  
% 11.99/2.00  fof(f42,plain,(
% 11.99/2.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f31])).
% 11.99/2.00  
% 11.99/2.00  fof(f7,axiom,(
% 11.99/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.99/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f20,plain,(
% 11.99/2.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.99/2.00    inference(ennf_transformation,[],[f7])).
% 11.99/2.00  
% 11.99/2.00  fof(f54,plain,(
% 11.99/2.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.99/2.00    inference(cnf_transformation,[],[f20])).
% 11.99/2.00  
% 11.99/2.00  fof(f10,axiom,(
% 11.99/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.99/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f23,plain,(
% 11.99/2.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.99/2.00    inference(ennf_transformation,[],[f10])).
% 11.99/2.00  
% 11.99/2.00  fof(f57,plain,(
% 11.99/2.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.99/2.00    inference(cnf_transformation,[],[f23])).
% 11.99/2.00  
% 11.99/2.00  fof(f69,plain,(
% 11.99/2.00    k2_relset_1(sK2,sK3,sK4) != sK3),
% 11.99/2.00    inference(cnf_transformation,[],[f41])).
% 11.99/2.00  
% 11.99/2.00  fof(f6,axiom,(
% 11.99/2.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 11.99/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f18,plain,(
% 11.99/2.00    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.99/2.00    inference(ennf_transformation,[],[f6])).
% 11.99/2.00  
% 11.99/2.00  fof(f19,plain,(
% 11.99/2.00    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.99/2.00    inference(flattening,[],[f18])).
% 11.99/2.00  
% 11.99/2.00  fof(f53,plain,(
% 11.99/2.00    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f19])).
% 11.99/2.00  
% 11.99/2.00  fof(f64,plain,(
% 11.99/2.00    v1_funct_1(sK4)),
% 11.99/2.00    inference(cnf_transformation,[],[f41])).
% 11.99/2.00  
% 11.99/2.00  fof(f46,plain,(
% 11.99/2.00    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f34])).
% 11.99/2.00  
% 11.99/2.00  fof(f67,plain,(
% 11.99/2.00    ( ! [X3] : (r2_hidden(sK5(X3),sK2) | ~r2_hidden(X3,sK3)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f41])).
% 11.99/2.00  
% 11.99/2.00  fof(f3,axiom,(
% 11.99/2.00    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.99/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f35,plain,(
% 11.99/2.00    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 11.99/2.00    inference(nnf_transformation,[],[f3])).
% 11.99/2.00  
% 11.99/2.00  fof(f36,plain,(
% 11.99/2.00    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 11.99/2.00    inference(flattening,[],[f35])).
% 11.99/2.00  
% 11.99/2.00  fof(f49,plain,(
% 11.99/2.00    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 11.99/2.00    inference(cnf_transformation,[],[f36])).
% 11.99/2.00  
% 11.99/2.00  fof(f70,plain,(
% 11.99/2.00    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 11.99/2.00    inference(equality_resolution,[],[f49])).
% 11.99/2.00  
% 11.99/2.00  fof(f4,axiom,(
% 11.99/2.00    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 11.99/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f50,plain,(
% 11.99/2.00    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 11.99/2.00    inference(cnf_transformation,[],[f4])).
% 11.99/2.00  
% 11.99/2.00  fof(f44,plain,(
% 11.99/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f31])).
% 11.99/2.00  
% 11.99/2.00  fof(f43,plain,(
% 11.99/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f31])).
% 11.99/2.00  
% 11.99/2.00  cnf(c_25,negated_conjecture,
% 11.99/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 11.99/2.00      inference(cnf_transformation,[],[f66]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_650,plain,
% 11.99/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_21,plain,
% 11.99/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.99/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.99/2.00      | k1_relset_1(X1,X2,X0) = X1
% 11.99/2.00      | k1_xboole_0 = X2 ),
% 11.99/2.00      inference(cnf_transformation,[],[f58]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_653,plain,
% 11.99/2.00      ( k1_relset_1(X0,X1,X2) = X0
% 11.99/2.00      | k1_xboole_0 = X1
% 11.99/2.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.99/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1460,plain,
% 11.99/2.00      ( k1_relset_1(sK2,sK3,sK4) = sK2
% 11.99/2.00      | sK3 = k1_xboole_0
% 11.99/2.00      | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_650,c_653]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_26,negated_conjecture,
% 11.99/2.00      ( v1_funct_2(sK4,sK2,sK3) ),
% 11.99/2.00      inference(cnf_transformation,[],[f65]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_29,plain,
% 11.99/2.00      ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_3438,plain,
% 11.99/2.00      ( sK3 = k1_xboole_0 | k1_relset_1(sK2,sK3,sK4) = sK2 ),
% 11.99/2.00      inference(global_propositional_subsumption,
% 11.99/2.00                [status(thm)],
% 11.99/2.00                [c_1460,c_29]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_3439,plain,
% 11.99/2.00      ( k1_relset_1(sK2,sK3,sK4) = sK2 | sK3 = k1_xboole_0 ),
% 11.99/2.00      inference(renaming,[status(thm)],[c_3438]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_14,plain,
% 11.99/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.99/2.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 11.99/2.00      inference(cnf_transformation,[],[f56]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_660,plain,
% 11.99/2.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 11.99/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1846,plain,
% 11.99/2.00      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_650,c_660]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_3440,plain,
% 11.99/2.00      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 11.99/2.00      inference(demodulation,[status(thm)],[c_3439,c_1846]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_13,plain,
% 11.99/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.99/2.00      | v5_relat_1(X0,X2) ),
% 11.99/2.00      inference(cnf_transformation,[],[f55]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_661,plain,
% 11.99/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.99/2.00      | v5_relat_1(X0,X2) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1511,plain,
% 11.99/2.00      ( v5_relat_1(sK4,sK3) = iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_650,c_661]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_10,plain,
% 11.99/2.00      ( ~ v5_relat_1(X0,X1)
% 11.99/2.00      | r1_tarski(k2_relat_1(X0),X1)
% 11.99/2.00      | ~ v1_relat_1(X0) ),
% 11.99/2.00      inference(cnf_transformation,[],[f51]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_664,plain,
% 11.99/2.00      ( v5_relat_1(X0,X1) != iProver_top
% 11.99/2.00      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 11.99/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_4,plain,
% 11.99/2.00      ( r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0) | X1 = X0 ),
% 11.99/2.00      inference(cnf_transformation,[],[f45]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_667,plain,
% 11.99/2.00      ( X0 = X1
% 11.99/2.00      | r2_hidden(sK1(X1,X0),X0) = iProver_top
% 11.99/2.00      | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_23,negated_conjecture,
% 11.99/2.00      ( ~ r2_hidden(X0,sK3) | k1_funct_1(sK4,sK5(X0)) = X0 ),
% 11.99/2.00      inference(cnf_transformation,[],[f68]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_652,plain,
% 11.99/2.00      ( k1_funct_1(sK4,sK5(X0)) = X0 | r2_hidden(X0,sK3) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2325,plain,
% 11.99/2.00      ( k1_funct_1(sK4,sK5(sK1(sK3,X0))) = sK1(sK3,X0)
% 11.99/2.00      | sK3 = X0
% 11.99/2.00      | r2_hidden(sK1(sK3,X0),X0) = iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_667,c_652]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2,plain,
% 11.99/2.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 11.99/2.00      inference(cnf_transformation,[],[f42]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_669,plain,
% 11.99/2.00      ( r2_hidden(X0,X1) != iProver_top
% 11.99/2.00      | r2_hidden(X0,X2) = iProver_top
% 11.99/2.00      | r1_tarski(X1,X2) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_3846,plain,
% 11.99/2.00      ( k1_funct_1(sK4,sK5(sK1(sK3,X0))) = sK1(sK3,X0)
% 11.99/2.00      | sK3 = X0
% 11.99/2.00      | r2_hidden(sK1(sK3,X0),X1) = iProver_top
% 11.99/2.00      | r1_tarski(X0,X1) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_2325,c_669]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_8108,plain,
% 11.99/2.00      ( k1_funct_1(sK4,sK5(sK1(sK3,X0))) = sK1(sK3,X0)
% 11.99/2.00      | sK3 = X0
% 11.99/2.00      | r1_tarski(X0,sK3) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_3846,c_652]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_8154,plain,
% 11.99/2.00      ( k1_funct_1(sK4,sK5(sK1(sK3,k2_relat_1(X0)))) = sK1(sK3,k2_relat_1(X0))
% 11.99/2.00      | k2_relat_1(X0) = sK3
% 11.99/2.00      | v5_relat_1(X0,sK3) != iProver_top
% 11.99/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_664,c_8108]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_14541,plain,
% 11.99/2.00      ( k1_funct_1(sK4,sK5(sK1(sK3,k2_relat_1(sK4)))) = sK1(sK3,k2_relat_1(sK4))
% 11.99/2.00      | k2_relat_1(sK4) = sK3
% 11.99/2.00      | v1_relat_1(sK4) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1511,c_8154]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_30,plain,
% 11.99/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_12,plain,
% 11.99/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.99/2.00      | v1_relat_1(X0) ),
% 11.99/2.00      inference(cnf_transformation,[],[f54]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_894,plain,
% 11.99/2.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 11.99/2.00      | v1_relat_1(sK4) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_12]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_895,plain,
% 11.99/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 11.99/2.00      | v1_relat_1(sK4) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_894]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_15,plain,
% 11.99/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.99/2.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.99/2.00      inference(cnf_transformation,[],[f57]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_659,plain,
% 11.99/2.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 11.99/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1582,plain,
% 11.99/2.00      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_650,c_659]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_22,negated_conjecture,
% 11.99/2.00      ( k2_relset_1(sK2,sK3,sK4) != sK3 ),
% 11.99/2.00      inference(cnf_transformation,[],[f69]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_3329,plain,
% 11.99/2.00      ( k2_relat_1(sK4) != sK3 ),
% 11.99/2.00      inference(demodulation,[status(thm)],[c_1582,c_22]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_52923,plain,
% 11.99/2.00      ( k1_funct_1(sK4,sK5(sK1(sK3,k2_relat_1(sK4)))) = sK1(sK3,k2_relat_1(sK4)) ),
% 11.99/2.00      inference(global_propositional_subsumption,
% 11.99/2.00                [status(thm)],
% 11.99/2.00                [c_14541,c_30,c_895,c_3329]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_11,plain,
% 11.99/2.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 11.99/2.00      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 11.99/2.00      | ~ v1_funct_1(X1)
% 11.99/2.00      | ~ v1_relat_1(X1) ),
% 11.99/2.00      inference(cnf_transformation,[],[f53]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_663,plain,
% 11.99/2.00      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 11.99/2.00      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 11.99/2.00      | v1_funct_1(X1) != iProver_top
% 11.99/2.00      | v1_relat_1(X1) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_52928,plain,
% 11.99/2.00      ( r2_hidden(sK1(sK3,k2_relat_1(sK4)),k2_relat_1(sK4)) = iProver_top
% 11.99/2.00      | r2_hidden(sK5(sK1(sK3,k2_relat_1(sK4))),k1_relat_1(sK4)) != iProver_top
% 11.99/2.00      | v1_funct_1(sK4) != iProver_top
% 11.99/2.00      | v1_relat_1(sK4) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_52923,c_663]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_27,negated_conjecture,
% 11.99/2.00      ( v1_funct_1(sK4) ),
% 11.99/2.00      inference(cnf_transformation,[],[f64]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_28,plain,
% 11.99/2.00      ( v1_funct_1(sK4) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_902,plain,
% 11.99/2.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 11.99/2.00      | v5_relat_1(sK4,sK3) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_13]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_903,plain,
% 11.99/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 11.99/2.00      | v5_relat_1(sK4,sK3) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_902]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_984,plain,
% 11.99/2.00      ( ~ v5_relat_1(sK4,X0)
% 11.99/2.00      | r1_tarski(k2_relat_1(sK4),X0)
% 11.99/2.00      | ~ v1_relat_1(sK4) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_10]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1125,plain,
% 11.99/2.00      ( ~ v5_relat_1(sK4,sK3)
% 11.99/2.00      | r1_tarski(k2_relat_1(sK4),sK3)
% 11.99/2.00      | ~ v1_relat_1(sK4) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_984]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1126,plain,
% 11.99/2.00      ( v5_relat_1(sK4,sK3) != iProver_top
% 11.99/2.00      | r1_tarski(k2_relat_1(sK4),sK3) = iProver_top
% 11.99/2.00      | v1_relat_1(sK4) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_1125]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2886,plain,
% 11.99/2.00      ( r2_hidden(sK1(X0,k2_relat_1(sK4)),X0)
% 11.99/2.00      | r2_hidden(sK1(X0,k2_relat_1(sK4)),k2_relat_1(sK4))
% 11.99/2.00      | k2_relat_1(sK4) = X0 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_4]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_7786,plain,
% 11.99/2.00      ( r2_hidden(sK1(sK3,k2_relat_1(sK4)),k2_relat_1(sK4))
% 11.99/2.00      | r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3)
% 11.99/2.00      | k2_relat_1(sK4) = sK3 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_2886]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_7789,plain,
% 11.99/2.00      ( k2_relat_1(sK4) = sK3
% 11.99/2.00      | r2_hidden(sK1(sK3,k2_relat_1(sK4)),k2_relat_1(sK4)) = iProver_top
% 11.99/2.00      | r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_7786]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2121,plain,
% 11.99/2.00      ( ~ r2_hidden(sK1(sK3,X0),X0)
% 11.99/2.00      | r2_hidden(sK1(sK3,X0),X1)
% 11.99/2.00      | ~ r1_tarski(X0,X1) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_2]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_6149,plain,
% 11.99/2.00      ( ~ r2_hidden(sK1(sK3,X0),X0)
% 11.99/2.00      | r2_hidden(sK1(sK3,X0),sK3)
% 11.99/2.00      | ~ r1_tarski(X0,sK3) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_2121]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_33692,plain,
% 11.99/2.00      ( ~ r2_hidden(sK1(sK3,k2_relat_1(sK4)),k2_relat_1(sK4))
% 11.99/2.00      | r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3)
% 11.99/2.00      | ~ r1_tarski(k2_relat_1(sK4),sK3) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_6149]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_33693,plain,
% 11.99/2.00      ( r2_hidden(sK1(sK3,k2_relat_1(sK4)),k2_relat_1(sK4)) != iProver_top
% 11.99/2.00      | r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3) = iProver_top
% 11.99/2.00      | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_33692]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_3,plain,
% 11.99/2.00      ( ~ r2_hidden(sK1(X0,X1),X1)
% 11.99/2.00      | ~ r2_hidden(sK1(X0,X1),X0)
% 11.99/2.00      | X1 = X0 ),
% 11.99/2.00      inference(cnf_transformation,[],[f46]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_6150,plain,
% 11.99/2.00      ( ~ r2_hidden(sK1(sK3,X0),X0)
% 11.99/2.00      | ~ r2_hidden(sK1(sK3,X0),sK3)
% 11.99/2.00      | X0 = sK3 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_3]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_43743,plain,
% 11.99/2.00      ( ~ r2_hidden(sK1(sK3,k2_relat_1(sK4)),k2_relat_1(sK4))
% 11.99/2.00      | ~ r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3)
% 11.99/2.00      | k2_relat_1(sK4) = sK3 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_6150]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_43750,plain,
% 11.99/2.00      ( k2_relat_1(sK4) = sK3
% 11.99/2.00      | r2_hidden(sK1(sK3,k2_relat_1(sK4)),k2_relat_1(sK4)) != iProver_top
% 11.99/2.00      | r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_43743]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_53109,plain,
% 11.99/2.00      ( r2_hidden(sK5(sK1(sK3,k2_relat_1(sK4))),k1_relat_1(sK4)) != iProver_top ),
% 11.99/2.00      inference(global_propositional_subsumption,
% 11.99/2.00                [status(thm)],
% 11.99/2.00                [c_52928,c_28,c_30,c_895,c_903,c_1126,c_3329,c_7789,
% 11.99/2.00                 c_33693,c_43750]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_53115,plain,
% 11.99/2.00      ( sK3 = k1_xboole_0
% 11.99/2.00      | r2_hidden(sK5(sK1(sK3,k2_relat_1(sK4))),sK2) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_3440,c_53109]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_24,negated_conjecture,
% 11.99/2.00      ( ~ r2_hidden(X0,sK3) | r2_hidden(sK5(X0),sK2) ),
% 11.99/2.00      inference(cnf_transformation,[],[f67]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_9362,plain,
% 11.99/2.00      ( ~ r2_hidden(sK1(sK3,X0),sK3) | r2_hidden(sK5(sK1(sK3,X0)),sK2) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_24]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_43745,plain,
% 11.99/2.00      ( ~ r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3)
% 11.99/2.00      | r2_hidden(sK5(sK1(sK3,k2_relat_1(sK4))),sK2) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_9362]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_43746,plain,
% 11.99/2.00      ( r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3) != iProver_top
% 11.99/2.00      | r2_hidden(sK5(sK1(sK3,k2_relat_1(sK4))),sK2) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_43745]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2497,plain,
% 11.99/2.00      ( X0 = X1
% 11.99/2.00      | r2_hidden(sK1(X0,X1),X1) = iProver_top
% 11.99/2.00      | r2_hidden(sK1(X0,X1),X2) = iProver_top
% 11.99/2.00      | r1_tarski(X0,X2) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_667,c_669]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_5,plain,
% 11.99/2.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.99/2.00      inference(cnf_transformation,[],[f70]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_8,plain,
% 11.99/2.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 11.99/2.00      inference(cnf_transformation,[],[f50]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_666,plain,
% 11.99/2.00      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_957,plain,
% 11.99/2.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_5,c_666]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_6289,plain,
% 11.99/2.00      ( X0 = X1
% 11.99/2.00      | r2_hidden(sK1(X1,X0),X0) = iProver_top
% 11.99/2.00      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_2497,c_957]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_6367,plain,
% 11.99/2.00      ( X0 = X1
% 11.99/2.00      | r2_hidden(sK1(X0,X1),X2) = iProver_top
% 11.99/2.00      | r1_tarski(X1,X2) != iProver_top
% 11.99/2.00      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_6289,c_669]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_668,plain,
% 11.99/2.00      ( X0 = X1
% 11.99/2.00      | r2_hidden(sK1(X1,X0),X0) != iProver_top
% 11.99/2.00      | r2_hidden(sK1(X1,X0),X1) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_6370,plain,
% 11.99/2.00      ( X0 = X1
% 11.99/2.00      | r2_hidden(sK1(X0,X1),X0) != iProver_top
% 11.99/2.00      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_6289,c_668]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_6705,plain,
% 11.99/2.00      ( X0 = X1
% 11.99/2.00      | r2_hidden(sK1(X0,X1),X1) = iProver_top
% 11.99/2.00      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_667,c_6370]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_6754,plain,
% 11.99/2.00      ( X0 = X1
% 11.99/2.00      | r2_hidden(sK1(X1,X0),X1) != iProver_top
% 11.99/2.00      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_6705,c_668]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_10142,plain,
% 11.99/2.00      ( X0 = X1
% 11.99/2.00      | r1_tarski(X0,X1) != iProver_top
% 11.99/2.00      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_6367,c_6754]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_42943,plain,
% 11.99/2.00      ( k2_relat_1(X0) = X1
% 11.99/2.00      | v5_relat_1(X0,X1) != iProver_top
% 11.99/2.00      | r1_tarski(X1,k1_xboole_0) != iProver_top
% 11.99/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_664,c_10142]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_43032,plain,
% 11.99/2.00      ( k2_relat_1(sK4) = sK3
% 11.99/2.00      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 11.99/2.00      | v1_relat_1(sK4) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1511,c_42943]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_238,plain,
% 11.99/2.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 11.99/2.00      theory(equality) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_3935,plain,
% 11.99/2.00      ( ~ r1_tarski(X0,X1) | r1_tarski(sK3,X1) | sK3 != X0 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_238]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_3936,plain,
% 11.99/2.00      ( sK3 != X0
% 11.99/2.00      | r1_tarski(X0,X1) != iProver_top
% 11.99/2.00      | r1_tarski(sK3,X1) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_3935]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_3938,plain,
% 11.99/2.00      ( sK3 != k1_xboole_0
% 11.99/2.00      | r1_tarski(sK3,k1_xboole_0) = iProver_top
% 11.99/2.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_3936]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_0,plain,
% 11.99/2.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 11.99/2.00      inference(cnf_transformation,[],[f44]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1,plain,
% 11.99/2.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 11.99/2.00      inference(cnf_transformation,[],[f43]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1090,plain,
% 11.99/2.00      ( r1_tarski(X0,X0) ),
% 11.99/2.00      inference(resolution,[status(thm)],[c_0,c_1]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1091,plain,
% 11.99/2.00      ( r1_tarski(X0,X0) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_1090]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1093,plain,
% 11.99/2.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_1091]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(contradiction,plain,
% 11.99/2.00      ( $false ),
% 11.99/2.00      inference(minisat,
% 11.99/2.00                [status(thm)],
% 11.99/2.00                [c_53115,c_43746,c_43032,c_33693,c_7789,c_3938,c_3329,
% 11.99/2.00                 c_1126,c_1093,c_903,c_895,c_30]) ).
% 11.99/2.00  
% 11.99/2.00  
% 11.99/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.99/2.00  
% 11.99/2.00  ------                               Statistics
% 11.99/2.00  
% 11.99/2.00  ------ Selected
% 11.99/2.00  
% 11.99/2.00  total_time:                             1.456
% 11.99/2.00  
%------------------------------------------------------------------------------
