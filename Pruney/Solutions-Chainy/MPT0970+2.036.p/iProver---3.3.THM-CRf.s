%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:52 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :  181 (2366 expanded)
%              Number of clauses        :  120 ( 865 expanded)
%              Number of leaves         :   19 ( 541 expanded)
%              Depth                    :   28
%              Number of atoms          :  545 (10390 expanded)
%              Number of equality atoms :  268 (3048 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

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
    inference(ennf_transformation,[],[f14])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f28,f40,f39])).

fof(f66,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

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
    inference(nnf_transformation,[],[f26])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f67,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f30,plain,(
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

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
            & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f32])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f69,plain,(
    ! [X3] :
      ( k1_funct_1(sK4,sK5(X3)) = X3
      | ~ r2_hidden(X3,sK3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f70,plain,(
    k2_relset_1(sK2,sK3,sK4) != sK3 ),
    inference(cnf_transformation,[],[f41])).

fof(f68,plain,(
    ! [X3] :
      ( r2_hidden(sK5(X3),sK2)
      | ~ r2_hidden(X3,sK3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_477,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_478,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_766,plain,
    ( k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != sK4
    | sK3 != X1
    | sK2 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_478])).

cnf(c_767,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_766])).

cnf(c_834,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_767])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_522,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_523,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_522])).

cnf(c_1520,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_523])).

cnf(c_1677,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_834,c_1520])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_531,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_532,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_531])).

cnf(c_725,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_532])).

cnf(c_726,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_725])).

cnf(c_935,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1503,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_935])).

cnf(c_1505,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_1585,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_726,c_1503,c_1505])).

cnf(c_1680,plain,
    ( k9_relat_1(sK4,sK2) = k2_relat_1(sK4)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1677,c_1585])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1318,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_695,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_532])).

cnf(c_696,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
    | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_695])).

cnf(c_926,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
    | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_696])).

cnf(c_1300,plain,
    ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4) = iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_926])).

cnf(c_927,plain,
    ( sP2_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_696])).

cnf(c_968,plain,
    ( sP2_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_927])).

cnf(c_969,plain,
    ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4) = iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_926])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_710,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_532])).

cnf(c_711,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
    | r2_hidden(sK1(X0,X1,sK4),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_710])).

cnf(c_923,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_711])).

cnf(c_1504,plain,
    ( ~ sP0_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_923])).

cnf(c_1508,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1504])).

cnf(c_2326,plain,
    ( r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1300,c_968,c_969,c_1503,c_1508])).

cnf(c_2327,plain,
    ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_2326])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_462,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X2)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_26])).

cnf(c_463,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_462])).

cnf(c_1311,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X0)
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_463])).

cnf(c_1673,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1311])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1316,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1842,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1673,c_1316])).

cnf(c_2335,plain,
    ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2327,c_1842])).

cnf(c_3325,plain,
    ( k9_relat_1(sK4,X0) = X1
    | r2_hidden(sK0(X1,k9_relat_1(sK4,X0)),X1) = iProver_top
    | r2_hidden(sK0(X1,k9_relat_1(sK4,X0)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1318,c_2335])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK4,sK5(X0)) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1314,plain,
    ( k1_funct_1(sK4,sK5(X0)) = X0
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3552,plain,
    ( k1_funct_1(sK4,sK5(sK0(X0,k9_relat_1(sK4,X1)))) = sK0(X0,k9_relat_1(sK4,X1))
    | k9_relat_1(sK4,X1) = X0
    | r2_hidden(sK0(X0,k9_relat_1(sK4,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3325,c_1314])).

cnf(c_3629,plain,
    ( k1_funct_1(sK4,sK5(sK0(sK3,k9_relat_1(sK4,X0)))) = sK0(sK3,k9_relat_1(sK4,X0))
    | k9_relat_1(sK4,X0) = sK3 ),
    inference(superposition,[status(thm)],[c_3552,c_1314])).

cnf(c_3761,plain,
    ( k1_funct_1(sK4,sK5(sK0(sK3,k2_relat_1(sK4)))) = sK0(sK3,k9_relat_1(sK4,sK2))
    | k9_relat_1(sK4,sK2) = sK3
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1680,c_3629])).

cnf(c_3760,plain,
    ( k1_funct_1(sK4,sK5(sK0(sK3,k2_relat_1(sK4)))) = sK0(sK3,k9_relat_1(sK4,k1_relat_1(sK4)))
    | k9_relat_1(sK4,k1_relat_1(sK4)) = sK3 ),
    inference(superposition,[status(thm)],[c_1585,c_3629])).

cnf(c_3777,plain,
    ( k1_funct_1(sK4,sK5(sK0(sK3,k2_relat_1(sK4)))) = sK0(sK3,k2_relat_1(sK4))
    | k9_relat_1(sK4,k1_relat_1(sK4)) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_3760,c_1585])).

cnf(c_3778,plain,
    ( k1_funct_1(sK4,sK5(sK0(sK3,k2_relat_1(sK4)))) = sK0(sK3,k2_relat_1(sK4))
    | k2_relat_1(sK4) = sK3 ),
    inference(demodulation,[status(thm)],[c_3777,c_1585])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_513,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_514,plain,
    ( k2_relset_1(X0,X1,sK4) = k2_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_1502,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_514])).

cnf(c_23,negated_conjecture,
    ( k2_relset_1(sK2,sK3,sK4) != sK3 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1557,plain,
    ( k2_relat_1(sK4) != sK3 ),
    inference(demodulation,[status(thm)],[c_1502,c_23])).

cnf(c_3880,plain,
    ( k1_funct_1(sK4,sK5(sK0(sK3,k2_relat_1(sK4)))) = sK0(sK3,k2_relat_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3778,c_1557])).

cnf(c_4053,plain,
    ( k9_relat_1(sK4,sK2) = sK3
    | sK0(sK3,k9_relat_1(sK4,sK2)) = sK0(sK3,k2_relat_1(sK4))
    | sK3 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3761,c_3880])).

cnf(c_4059,plain,
    ( k9_relat_1(sK4,sK2) = sK3
    | sK3 = k1_xboole_0
    | r2_hidden(sK0(sK3,k9_relat_1(sK4,sK2)),k9_relat_1(sK4,sK2)) = iProver_top
    | r2_hidden(sK0(sK3,k2_relat_1(sK4)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4053,c_1318])).

cnf(c_3550,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = X0
    | r2_hidden(sK0(X0,k9_relat_1(sK4,k1_relat_1(sK4))),sK3) = iProver_top
    | r2_hidden(sK0(X0,k2_relat_1(sK4)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1585,c_3325])).

cnf(c_3587,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = X0
    | r2_hidden(sK0(X0,k2_relat_1(sK4)),X0) = iProver_top
    | r2_hidden(sK0(X0,k2_relat_1(sK4)),sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3550,c_1585])).

cnf(c_3588,plain,
    ( k2_relat_1(sK4) = X0
    | r2_hidden(sK0(X0,k2_relat_1(sK4)),X0) = iProver_top
    | r2_hidden(sK0(X0,k2_relat_1(sK4)),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3587,c_1585])).

cnf(c_4002,plain,
    ( k2_relat_1(sK4) = sK3
    | r2_hidden(sK0(sK3,k2_relat_1(sK4)),sK3) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_3588])).

cnf(c_4004,plain,
    ( k2_relat_1(sK4) = sK3
    | r2_hidden(sK0(sK3,k2_relat_1(sK4)),sK3) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4002])).

cnf(c_5168,plain,
    ( r2_hidden(sK0(sK3,k2_relat_1(sK4)),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4059,c_1557,c_4004])).

cnf(c_3326,plain,
    ( k9_relat_1(sK4,X0) = X1
    | r2_hidden(sK0(k9_relat_1(sK4,X0),X1),X1) = iProver_top
    | r2_hidden(sK0(k9_relat_1(sK4,X0),X1),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1318,c_2335])).

cnf(c_4208,plain,
    ( k1_funct_1(sK4,sK5(sK0(k9_relat_1(sK4,X0),X1))) = sK0(k9_relat_1(sK4,X0),X1)
    | k9_relat_1(sK4,X0) = X1
    | r2_hidden(sK0(k9_relat_1(sK4,X0),X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3326,c_1314])).

cnf(c_4433,plain,
    ( k1_funct_1(sK4,sK5(sK0(k9_relat_1(sK4,X0),sK3))) = sK0(k9_relat_1(sK4,X0),sK3)
    | k9_relat_1(sK4,X0) = sK3 ),
    inference(superposition,[status(thm)],[c_4208,c_1314])).

cnf(c_4600,plain,
    ( k1_funct_1(sK4,sK5(sK0(k2_relat_1(sK4),sK3))) = sK0(k9_relat_1(sK4,sK2),sK3)
    | k9_relat_1(sK4,sK2) = sK3
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1680,c_4433])).

cnf(c_3336,plain,
    ( r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1585,c_2335])).

cnf(c_3788,plain,
    ( k2_relat_1(sK4) = X0
    | r2_hidden(sK0(k2_relat_1(sK4),X0),X0) = iProver_top
    | r2_hidden(sK0(k2_relat_1(sK4),X0),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1318,c_3336])).

cnf(c_4113,plain,
    ( k1_funct_1(sK4,sK5(sK0(k2_relat_1(sK4),X0))) = sK0(k2_relat_1(sK4),X0)
    | k2_relat_1(sK4) = X0
    | r2_hidden(sK0(k2_relat_1(sK4),X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3788,c_1314])).

cnf(c_4280,plain,
    ( k1_funct_1(sK4,sK5(sK0(k2_relat_1(sK4),sK3))) = sK0(k2_relat_1(sK4),sK3)
    | k2_relat_1(sK4) = sK3 ),
    inference(superposition,[status(thm)],[c_4113,c_1314])).

cnf(c_4422,plain,
    ( k1_funct_1(sK4,sK5(sK0(k2_relat_1(sK4),sK3))) = sK0(k2_relat_1(sK4),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4280,c_1557])).

cnf(c_4611,plain,
    ( k9_relat_1(sK4,sK2) = sK3
    | sK0(k9_relat_1(sK4,sK2),sK3) = sK0(k2_relat_1(sK4),sK3)
    | sK3 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4600,c_4422])).

cnf(c_25,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(sK5(X0),sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2240,plain,
    ( ~ r2_hidden(sK0(X0,sK3),sK3)
    | r2_hidden(sK5(sK0(X0,sK3)),sK2) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_3447,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(sK4),sK3),sK3)
    | r2_hidden(sK5(sK0(k2_relat_1(sK4),sK3)),sK2) ),
    inference(instantiation,[status(thm)],[c_2240])).

cnf(c_3448,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4),sK3),sK3) != iProver_top
    | r2_hidden(sK5(sK0(k2_relat_1(sK4),sK3)),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3447])).

cnf(c_4122,plain,
    ( k2_relat_1(sK4) = sK3
    | r2_hidden(sK0(k2_relat_1(sK4),sK3),sK3) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_3788])).

cnf(c_4124,plain,
    ( k2_relat_1(sK4) = sK3
    | r2_hidden(sK0(k2_relat_1(sK4),sK3),sK3) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4122])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_334,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_28])).

cnf(c_335,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_334])).

cnf(c_647,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_532,c_335])).

cnf(c_932,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
    | ~ sP5_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP5_iProver_split])],[c_647])).

cnf(c_1309,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
    | sP5_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_932])).

cnf(c_933,plain,
    ( sP5_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_647])).

cnf(c_981,plain,
    ( sP5_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_933])).

cnf(c_982,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
    | sP5_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_932])).

cnf(c_2255,plain,
    ( r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1309,c_981,c_982,c_1503,c_1508])).

cnf(c_2256,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2255])).

cnf(c_4425,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4),sK3),k2_relat_1(sK4)) = iProver_top
    | r2_hidden(sK5(sK0(k2_relat_1(sK4),sK3)),k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4422,c_2256])).

cnf(c_936,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1512,plain,
    ( k2_relset_1(sK2,sK3,sK4) != X0
    | k2_relset_1(sK2,sK3,sK4) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_936])).

cnf(c_1584,plain,
    ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
    | k2_relset_1(sK2,sK3,sK4) = sK3
    | sK3 != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1512])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1658,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
    | ~ r2_hidden(sK0(k2_relat_1(sK4),sK3),sK3)
    | sK3 = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1659,plain,
    ( sK3 = k2_relat_1(sK4)
    | r2_hidden(sK0(k2_relat_1(sK4),sK3),k2_relat_1(sK4)) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK4),sK3),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1658])).

cnf(c_4622,plain,
    ( r2_hidden(sK5(sK0(k2_relat_1(sK4),sK3)),k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4425,c_23,c_1502,c_1557,c_1584,c_1659,c_4124])).

cnf(c_4627,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK5(sK0(k2_relat_1(sK4),sK3)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1677,c_4622])).

cnf(c_4701,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4611,c_1557,c_3448,c_4124,c_4627])).

cnf(c_5172,plain,
    ( r2_hidden(sK0(k1_xboole_0,k2_relat_1(sK4)),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5168,c_4701])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_323,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_13])).

cnf(c_324,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_1312,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_324])).

cnf(c_5174,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5172,c_1312])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:43:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.10/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.00  
% 3.10/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.10/1.00  
% 3.10/1.00  ------  iProver source info
% 3.10/1.00  
% 3.10/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.10/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.10/1.00  git: non_committed_changes: false
% 3.10/1.00  git: last_make_outside_of_git: false
% 3.10/1.00  
% 3.10/1.00  ------ 
% 3.10/1.00  
% 3.10/1.00  ------ Input Options
% 3.10/1.00  
% 3.10/1.00  --out_options                           all
% 3.10/1.00  --tptp_safe_out                         true
% 3.10/1.00  --problem_path                          ""
% 3.10/1.00  --include_path                          ""
% 3.10/1.00  --clausifier                            res/vclausify_rel
% 3.10/1.00  --clausifier_options                    --mode clausify
% 3.10/1.00  --stdin                                 false
% 3.10/1.00  --stats_out                             all
% 3.10/1.00  
% 3.10/1.00  ------ General Options
% 3.10/1.00  
% 3.10/1.00  --fof                                   false
% 3.10/1.00  --time_out_real                         305.
% 3.10/1.00  --time_out_virtual                      -1.
% 3.10/1.00  --symbol_type_check                     false
% 3.10/1.00  --clausify_out                          false
% 3.10/1.00  --sig_cnt_out                           false
% 3.10/1.00  --trig_cnt_out                          false
% 3.10/1.00  --trig_cnt_out_tolerance                1.
% 3.10/1.00  --trig_cnt_out_sk_spl                   false
% 3.10/1.00  --abstr_cl_out                          false
% 3.10/1.00  
% 3.10/1.00  ------ Global Options
% 3.10/1.00  
% 3.10/1.00  --schedule                              default
% 3.10/1.00  --add_important_lit                     false
% 3.10/1.00  --prop_solver_per_cl                    1000
% 3.10/1.00  --min_unsat_core                        false
% 3.10/1.00  --soft_assumptions                      false
% 3.10/1.00  --soft_lemma_size                       3
% 3.10/1.00  --prop_impl_unit_size                   0
% 3.10/1.00  --prop_impl_unit                        []
% 3.10/1.00  --share_sel_clauses                     true
% 3.10/1.00  --reset_solvers                         false
% 3.10/1.00  --bc_imp_inh                            [conj_cone]
% 3.10/1.00  --conj_cone_tolerance                   3.
% 3.10/1.00  --extra_neg_conj                        none
% 3.10/1.00  --large_theory_mode                     true
% 3.10/1.00  --prolific_symb_bound                   200
% 3.10/1.00  --lt_threshold                          2000
% 3.10/1.00  --clause_weak_htbl                      true
% 3.10/1.00  --gc_record_bc_elim                     false
% 3.10/1.00  
% 3.10/1.00  ------ Preprocessing Options
% 3.10/1.00  
% 3.10/1.00  --preprocessing_flag                    true
% 3.10/1.00  --time_out_prep_mult                    0.1
% 3.10/1.00  --splitting_mode                        input
% 3.10/1.00  --splitting_grd                         true
% 3.10/1.00  --splitting_cvd                         false
% 3.10/1.00  --splitting_cvd_svl                     false
% 3.10/1.00  --splitting_nvd                         32
% 3.10/1.00  --sub_typing                            true
% 3.10/1.00  --prep_gs_sim                           true
% 3.10/1.00  --prep_unflatten                        true
% 3.10/1.00  --prep_res_sim                          true
% 3.10/1.00  --prep_upred                            true
% 3.10/1.00  --prep_sem_filter                       exhaustive
% 3.10/1.00  --prep_sem_filter_out                   false
% 3.10/1.00  --pred_elim                             true
% 3.10/1.00  --res_sim_input                         true
% 3.10/1.00  --eq_ax_congr_red                       true
% 3.10/1.00  --pure_diseq_elim                       true
% 3.10/1.00  --brand_transform                       false
% 3.10/1.00  --non_eq_to_eq                          false
% 3.10/1.00  --prep_def_merge                        true
% 3.10/1.00  --prep_def_merge_prop_impl              false
% 3.10/1.00  --prep_def_merge_mbd                    true
% 3.10/1.00  --prep_def_merge_tr_red                 false
% 3.10/1.00  --prep_def_merge_tr_cl                  false
% 3.10/1.00  --smt_preprocessing                     true
% 3.10/1.00  --smt_ac_axioms                         fast
% 3.10/1.00  --preprocessed_out                      false
% 3.10/1.00  --preprocessed_stats                    false
% 3.10/1.00  
% 3.10/1.00  ------ Abstraction refinement Options
% 3.10/1.00  
% 3.10/1.00  --abstr_ref                             []
% 3.10/1.00  --abstr_ref_prep                        false
% 3.10/1.00  --abstr_ref_until_sat                   false
% 3.10/1.00  --abstr_ref_sig_restrict                funpre
% 3.10/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.10/1.00  --abstr_ref_under                       []
% 3.10/1.00  
% 3.10/1.00  ------ SAT Options
% 3.10/1.00  
% 3.10/1.00  --sat_mode                              false
% 3.10/1.00  --sat_fm_restart_options                ""
% 3.10/1.00  --sat_gr_def                            false
% 3.10/1.00  --sat_epr_types                         true
% 3.10/1.00  --sat_non_cyclic_types                  false
% 3.10/1.00  --sat_finite_models                     false
% 3.10/1.00  --sat_fm_lemmas                         false
% 3.10/1.00  --sat_fm_prep                           false
% 3.10/1.00  --sat_fm_uc_incr                        true
% 3.10/1.00  --sat_out_model                         small
% 3.10/1.00  --sat_out_clauses                       false
% 3.10/1.00  
% 3.10/1.00  ------ QBF Options
% 3.10/1.00  
% 3.10/1.00  --qbf_mode                              false
% 3.10/1.00  --qbf_elim_univ                         false
% 3.10/1.00  --qbf_dom_inst                          none
% 3.10/1.00  --qbf_dom_pre_inst                      false
% 3.10/1.00  --qbf_sk_in                             false
% 3.10/1.00  --qbf_pred_elim                         true
% 3.10/1.00  --qbf_split                             512
% 3.10/1.00  
% 3.10/1.00  ------ BMC1 Options
% 3.10/1.00  
% 3.10/1.00  --bmc1_incremental                      false
% 3.10/1.00  --bmc1_axioms                           reachable_all
% 3.10/1.00  --bmc1_min_bound                        0
% 3.10/1.00  --bmc1_max_bound                        -1
% 3.10/1.00  --bmc1_max_bound_default                -1
% 3.10/1.00  --bmc1_symbol_reachability              true
% 3.10/1.00  --bmc1_property_lemmas                  false
% 3.10/1.00  --bmc1_k_induction                      false
% 3.10/1.00  --bmc1_non_equiv_states                 false
% 3.10/1.00  --bmc1_deadlock                         false
% 3.10/1.00  --bmc1_ucm                              false
% 3.10/1.00  --bmc1_add_unsat_core                   none
% 3.10/1.00  --bmc1_unsat_core_children              false
% 3.10/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.10/1.00  --bmc1_out_stat                         full
% 3.10/1.00  --bmc1_ground_init                      false
% 3.10/1.00  --bmc1_pre_inst_next_state              false
% 3.10/1.00  --bmc1_pre_inst_state                   false
% 3.10/1.00  --bmc1_pre_inst_reach_state             false
% 3.10/1.00  --bmc1_out_unsat_core                   false
% 3.10/1.00  --bmc1_aig_witness_out                  false
% 3.10/1.00  --bmc1_verbose                          false
% 3.10/1.00  --bmc1_dump_clauses_tptp                false
% 3.10/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.10/1.00  --bmc1_dump_file                        -
% 3.10/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.10/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.10/1.00  --bmc1_ucm_extend_mode                  1
% 3.10/1.00  --bmc1_ucm_init_mode                    2
% 3.10/1.00  --bmc1_ucm_cone_mode                    none
% 3.10/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.10/1.00  --bmc1_ucm_relax_model                  4
% 3.10/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.10/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.10/1.00  --bmc1_ucm_layered_model                none
% 3.10/1.00  --bmc1_ucm_max_lemma_size               10
% 3.10/1.00  
% 3.10/1.00  ------ AIG Options
% 3.10/1.00  
% 3.10/1.00  --aig_mode                              false
% 3.10/1.00  
% 3.10/1.00  ------ Instantiation Options
% 3.10/1.00  
% 3.10/1.00  --instantiation_flag                    true
% 3.10/1.00  --inst_sos_flag                         false
% 3.10/1.00  --inst_sos_phase                        true
% 3.10/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.10/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.10/1.00  --inst_lit_sel_side                     num_symb
% 3.10/1.00  --inst_solver_per_active                1400
% 3.10/1.00  --inst_solver_calls_frac                1.
% 3.10/1.00  --inst_passive_queue_type               priority_queues
% 3.10/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.10/1.00  --inst_passive_queues_freq              [25;2]
% 3.10/1.00  --inst_dismatching                      true
% 3.10/1.00  --inst_eager_unprocessed_to_passive     true
% 3.10/1.00  --inst_prop_sim_given                   true
% 3.10/1.00  --inst_prop_sim_new                     false
% 3.10/1.00  --inst_subs_new                         false
% 3.10/1.00  --inst_eq_res_simp                      false
% 3.10/1.00  --inst_subs_given                       false
% 3.10/1.00  --inst_orphan_elimination               true
% 3.10/1.00  --inst_learning_loop_flag               true
% 3.10/1.00  --inst_learning_start                   3000
% 3.10/1.00  --inst_learning_factor                  2
% 3.10/1.00  --inst_start_prop_sim_after_learn       3
% 3.10/1.00  --inst_sel_renew                        solver
% 3.10/1.00  --inst_lit_activity_flag                true
% 3.10/1.00  --inst_restr_to_given                   false
% 3.10/1.00  --inst_activity_threshold               500
% 3.10/1.00  --inst_out_proof                        true
% 3.10/1.00  
% 3.10/1.00  ------ Resolution Options
% 3.10/1.00  
% 3.10/1.00  --resolution_flag                       true
% 3.10/1.00  --res_lit_sel                           adaptive
% 3.10/1.00  --res_lit_sel_side                      none
% 3.10/1.00  --res_ordering                          kbo
% 3.10/1.00  --res_to_prop_solver                    active
% 3.10/1.00  --res_prop_simpl_new                    false
% 3.10/1.00  --res_prop_simpl_given                  true
% 3.10/1.00  --res_passive_queue_type                priority_queues
% 3.10/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.10/1.00  --res_passive_queues_freq               [15;5]
% 3.10/1.00  --res_forward_subs                      full
% 3.10/1.00  --res_backward_subs                     full
% 3.10/1.00  --res_forward_subs_resolution           true
% 3.10/1.00  --res_backward_subs_resolution          true
% 3.10/1.00  --res_orphan_elimination                true
% 3.10/1.00  --res_time_limit                        2.
% 3.10/1.00  --res_out_proof                         true
% 3.10/1.00  
% 3.10/1.00  ------ Superposition Options
% 3.10/1.00  
% 3.10/1.00  --superposition_flag                    true
% 3.10/1.00  --sup_passive_queue_type                priority_queues
% 3.10/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.10/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.10/1.00  --demod_completeness_check              fast
% 3.10/1.00  --demod_use_ground                      true
% 3.10/1.00  --sup_to_prop_solver                    passive
% 3.10/1.00  --sup_prop_simpl_new                    true
% 3.10/1.00  --sup_prop_simpl_given                  true
% 3.10/1.00  --sup_fun_splitting                     false
% 3.10/1.00  --sup_smt_interval                      50000
% 3.10/1.00  
% 3.10/1.00  ------ Superposition Simplification Setup
% 3.10/1.00  
% 3.10/1.00  --sup_indices_passive                   []
% 3.10/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.10/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/1.00  --sup_full_bw                           [BwDemod]
% 3.10/1.00  --sup_immed_triv                        [TrivRules]
% 3.10/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.10/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/1.00  --sup_immed_bw_main                     []
% 3.10/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.10/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/1.00  
% 3.10/1.00  ------ Combination Options
% 3.10/1.00  
% 3.10/1.00  --comb_res_mult                         3
% 3.10/1.00  --comb_sup_mult                         2
% 3.10/1.00  --comb_inst_mult                        10
% 3.10/1.00  
% 3.10/1.00  ------ Debug Options
% 3.10/1.00  
% 3.10/1.00  --dbg_backtrace                         false
% 3.10/1.00  --dbg_dump_prop_clauses                 false
% 3.10/1.00  --dbg_dump_prop_clauses_file            -
% 3.10/1.00  --dbg_out_stat                          false
% 3.10/1.00  ------ Parsing...
% 3.10/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.10/1.00  
% 3.10/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.10/1.00  
% 3.10/1.00  ------ Preprocessing... gs_s  sp: 10 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.10/1.00  
% 3.10/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.10/1.00  ------ Proving...
% 3.10/1.00  ------ Problem Properties 
% 3.10/1.00  
% 3.10/1.00  
% 3.10/1.00  clauses                                 31
% 3.10/1.00  conjectures                             3
% 3.10/1.00  EPR                                     6
% 3.10/1.00  Horn                                    23
% 3.10/1.00  unary                                   2
% 3.10/1.00  binary                                  18
% 3.10/1.00  lits                                    74
% 3.10/1.00  lits eq                                 25
% 3.10/1.00  fd_pure                                 0
% 3.10/1.00  fd_pseudo                               0
% 3.10/1.00  fd_cond                                 0
% 3.10/1.00  fd_pseudo_cond                          2
% 3.10/1.00  AC symbols                              0
% 3.10/1.00  
% 3.10/1.00  ------ Schedule dynamic 5 is on 
% 3.10/1.00  
% 3.10/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.10/1.00  
% 3.10/1.00  
% 3.10/1.00  ------ 
% 3.10/1.00  Current options:
% 3.10/1.00  ------ 
% 3.10/1.00  
% 3.10/1.00  ------ Input Options
% 3.10/1.00  
% 3.10/1.00  --out_options                           all
% 3.10/1.00  --tptp_safe_out                         true
% 3.10/1.00  --problem_path                          ""
% 3.10/1.00  --include_path                          ""
% 3.10/1.00  --clausifier                            res/vclausify_rel
% 3.10/1.00  --clausifier_options                    --mode clausify
% 3.10/1.00  --stdin                                 false
% 3.10/1.00  --stats_out                             all
% 3.10/1.00  
% 3.10/1.00  ------ General Options
% 3.10/1.00  
% 3.10/1.00  --fof                                   false
% 3.10/1.00  --time_out_real                         305.
% 3.10/1.00  --time_out_virtual                      -1.
% 3.10/1.00  --symbol_type_check                     false
% 3.10/1.00  --clausify_out                          false
% 3.10/1.00  --sig_cnt_out                           false
% 3.10/1.00  --trig_cnt_out                          false
% 3.10/1.00  --trig_cnt_out_tolerance                1.
% 3.10/1.00  --trig_cnt_out_sk_spl                   false
% 3.10/1.00  --abstr_cl_out                          false
% 3.10/1.00  
% 3.10/1.00  ------ Global Options
% 3.10/1.00  
% 3.10/1.00  --schedule                              default
% 3.10/1.00  --add_important_lit                     false
% 3.10/1.00  --prop_solver_per_cl                    1000
% 3.10/1.00  --min_unsat_core                        false
% 3.10/1.00  --soft_assumptions                      false
% 3.10/1.00  --soft_lemma_size                       3
% 3.10/1.00  --prop_impl_unit_size                   0
% 3.10/1.00  --prop_impl_unit                        []
% 3.10/1.00  --share_sel_clauses                     true
% 3.10/1.00  --reset_solvers                         false
% 3.10/1.00  --bc_imp_inh                            [conj_cone]
% 3.10/1.00  --conj_cone_tolerance                   3.
% 3.10/1.00  --extra_neg_conj                        none
% 3.10/1.00  --large_theory_mode                     true
% 3.10/1.00  --prolific_symb_bound                   200
% 3.10/1.00  --lt_threshold                          2000
% 3.10/1.00  --clause_weak_htbl                      true
% 3.10/1.00  --gc_record_bc_elim                     false
% 3.10/1.00  
% 3.10/1.00  ------ Preprocessing Options
% 3.10/1.00  
% 3.10/1.00  --preprocessing_flag                    true
% 3.10/1.00  --time_out_prep_mult                    0.1
% 3.10/1.00  --splitting_mode                        input
% 3.10/1.00  --splitting_grd                         true
% 3.10/1.00  --splitting_cvd                         false
% 3.10/1.00  --splitting_cvd_svl                     false
% 3.10/1.00  --splitting_nvd                         32
% 3.10/1.00  --sub_typing                            true
% 3.10/1.00  --prep_gs_sim                           true
% 3.10/1.00  --prep_unflatten                        true
% 3.10/1.00  --prep_res_sim                          true
% 3.10/1.00  --prep_upred                            true
% 3.10/1.00  --prep_sem_filter                       exhaustive
% 3.10/1.00  --prep_sem_filter_out                   false
% 3.10/1.00  --pred_elim                             true
% 3.10/1.00  --res_sim_input                         true
% 3.10/1.00  --eq_ax_congr_red                       true
% 3.10/1.00  --pure_diseq_elim                       true
% 3.10/1.00  --brand_transform                       false
% 3.10/1.00  --non_eq_to_eq                          false
% 3.10/1.00  --prep_def_merge                        true
% 3.10/1.00  --prep_def_merge_prop_impl              false
% 3.10/1.00  --prep_def_merge_mbd                    true
% 3.10/1.00  --prep_def_merge_tr_red                 false
% 3.10/1.00  --prep_def_merge_tr_cl                  false
% 3.10/1.00  --smt_preprocessing                     true
% 3.10/1.00  --smt_ac_axioms                         fast
% 3.10/1.00  --preprocessed_out                      false
% 3.10/1.00  --preprocessed_stats                    false
% 3.10/1.00  
% 3.10/1.00  ------ Abstraction refinement Options
% 3.10/1.00  
% 3.10/1.00  --abstr_ref                             []
% 3.10/1.00  --abstr_ref_prep                        false
% 3.10/1.00  --abstr_ref_until_sat                   false
% 3.10/1.00  --abstr_ref_sig_restrict                funpre
% 3.10/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.10/1.00  --abstr_ref_under                       []
% 3.10/1.00  
% 3.10/1.00  ------ SAT Options
% 3.10/1.00  
% 3.10/1.00  --sat_mode                              false
% 3.10/1.00  --sat_fm_restart_options                ""
% 3.10/1.00  --sat_gr_def                            false
% 3.10/1.00  --sat_epr_types                         true
% 3.10/1.00  --sat_non_cyclic_types                  false
% 3.10/1.00  --sat_finite_models                     false
% 3.10/1.00  --sat_fm_lemmas                         false
% 3.10/1.00  --sat_fm_prep                           false
% 3.10/1.00  --sat_fm_uc_incr                        true
% 3.10/1.00  --sat_out_model                         small
% 3.10/1.00  --sat_out_clauses                       false
% 3.10/1.00  
% 3.10/1.00  ------ QBF Options
% 3.10/1.00  
% 3.10/1.00  --qbf_mode                              false
% 3.10/1.00  --qbf_elim_univ                         false
% 3.10/1.00  --qbf_dom_inst                          none
% 3.10/1.00  --qbf_dom_pre_inst                      false
% 3.10/1.00  --qbf_sk_in                             false
% 3.10/1.00  --qbf_pred_elim                         true
% 3.10/1.00  --qbf_split                             512
% 3.10/1.00  
% 3.10/1.00  ------ BMC1 Options
% 3.10/1.00  
% 3.10/1.00  --bmc1_incremental                      false
% 3.10/1.00  --bmc1_axioms                           reachable_all
% 3.10/1.00  --bmc1_min_bound                        0
% 3.10/1.00  --bmc1_max_bound                        -1
% 3.10/1.00  --bmc1_max_bound_default                -1
% 3.10/1.00  --bmc1_symbol_reachability              true
% 3.10/1.00  --bmc1_property_lemmas                  false
% 3.10/1.00  --bmc1_k_induction                      false
% 3.10/1.00  --bmc1_non_equiv_states                 false
% 3.10/1.00  --bmc1_deadlock                         false
% 3.10/1.00  --bmc1_ucm                              false
% 3.10/1.00  --bmc1_add_unsat_core                   none
% 3.10/1.00  --bmc1_unsat_core_children              false
% 3.10/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.10/1.00  --bmc1_out_stat                         full
% 3.10/1.00  --bmc1_ground_init                      false
% 3.10/1.00  --bmc1_pre_inst_next_state              false
% 3.10/1.00  --bmc1_pre_inst_state                   false
% 3.10/1.00  --bmc1_pre_inst_reach_state             false
% 3.10/1.00  --bmc1_out_unsat_core                   false
% 3.10/1.00  --bmc1_aig_witness_out                  false
% 3.10/1.00  --bmc1_verbose                          false
% 3.10/1.00  --bmc1_dump_clauses_tptp                false
% 3.10/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.10/1.00  --bmc1_dump_file                        -
% 3.10/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.10/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.10/1.00  --bmc1_ucm_extend_mode                  1
% 3.10/1.00  --bmc1_ucm_init_mode                    2
% 3.10/1.00  --bmc1_ucm_cone_mode                    none
% 3.10/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.10/1.00  --bmc1_ucm_relax_model                  4
% 3.10/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.10/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.10/1.00  --bmc1_ucm_layered_model                none
% 3.10/1.00  --bmc1_ucm_max_lemma_size               10
% 3.10/1.00  
% 3.10/1.00  ------ AIG Options
% 3.10/1.00  
% 3.10/1.00  --aig_mode                              false
% 3.10/1.00  
% 3.10/1.00  ------ Instantiation Options
% 3.10/1.00  
% 3.10/1.00  --instantiation_flag                    true
% 3.10/1.00  --inst_sos_flag                         false
% 3.10/1.00  --inst_sos_phase                        true
% 3.10/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.10/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.10/1.00  --inst_lit_sel_side                     none
% 3.10/1.00  --inst_solver_per_active                1400
% 3.10/1.00  --inst_solver_calls_frac                1.
% 3.10/1.00  --inst_passive_queue_type               priority_queues
% 3.10/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.10/1.00  --inst_passive_queues_freq              [25;2]
% 3.10/1.00  --inst_dismatching                      true
% 3.10/1.00  --inst_eager_unprocessed_to_passive     true
% 3.10/1.00  --inst_prop_sim_given                   true
% 3.10/1.00  --inst_prop_sim_new                     false
% 3.10/1.00  --inst_subs_new                         false
% 3.10/1.00  --inst_eq_res_simp                      false
% 3.10/1.00  --inst_subs_given                       false
% 3.10/1.00  --inst_orphan_elimination               true
% 3.10/1.00  --inst_learning_loop_flag               true
% 3.10/1.00  --inst_learning_start                   3000
% 3.10/1.00  --inst_learning_factor                  2
% 3.10/1.00  --inst_start_prop_sim_after_learn       3
% 3.10/1.00  --inst_sel_renew                        solver
% 3.10/1.00  --inst_lit_activity_flag                true
% 3.10/1.00  --inst_restr_to_given                   false
% 3.10/1.00  --inst_activity_threshold               500
% 3.10/1.00  --inst_out_proof                        true
% 3.10/1.00  
% 3.10/1.00  ------ Resolution Options
% 3.10/1.00  
% 3.10/1.00  --resolution_flag                       false
% 3.10/1.00  --res_lit_sel                           adaptive
% 3.10/1.00  --res_lit_sel_side                      none
% 3.10/1.00  --res_ordering                          kbo
% 3.10/1.00  --res_to_prop_solver                    active
% 3.10/1.00  --res_prop_simpl_new                    false
% 3.10/1.00  --res_prop_simpl_given                  true
% 3.10/1.00  --res_passive_queue_type                priority_queues
% 3.10/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.10/1.00  --res_passive_queues_freq               [15;5]
% 3.10/1.00  --res_forward_subs                      full
% 3.10/1.00  --res_backward_subs                     full
% 3.10/1.00  --res_forward_subs_resolution           true
% 3.10/1.00  --res_backward_subs_resolution          true
% 3.10/1.00  --res_orphan_elimination                true
% 3.10/1.00  --res_time_limit                        2.
% 3.10/1.00  --res_out_proof                         true
% 3.10/1.00  
% 3.10/1.00  ------ Superposition Options
% 3.10/1.00  
% 3.10/1.00  --superposition_flag                    true
% 3.10/1.00  --sup_passive_queue_type                priority_queues
% 3.10/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.10/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.10/1.00  --demod_completeness_check              fast
% 3.10/1.00  --demod_use_ground                      true
% 3.10/1.00  --sup_to_prop_solver                    passive
% 3.10/1.00  --sup_prop_simpl_new                    true
% 3.10/1.00  --sup_prop_simpl_given                  true
% 3.10/1.00  --sup_fun_splitting                     false
% 3.10/1.00  --sup_smt_interval                      50000
% 3.10/1.00  
% 3.10/1.00  ------ Superposition Simplification Setup
% 3.10/1.00  
% 3.10/1.00  --sup_indices_passive                   []
% 3.10/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.10/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/1.00  --sup_full_bw                           [BwDemod]
% 3.10/1.00  --sup_immed_triv                        [TrivRules]
% 3.10/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.10/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/1.00  --sup_immed_bw_main                     []
% 3.10/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.10/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/1.00  
% 3.10/1.00  ------ Combination Options
% 3.10/1.00  
% 3.10/1.00  --comb_res_mult                         3
% 3.10/1.00  --comb_sup_mult                         2
% 3.10/1.00  --comb_inst_mult                        10
% 3.10/1.00  
% 3.10/1.00  ------ Debug Options
% 3.10/1.00  
% 3.10/1.00  --dbg_backtrace                         false
% 3.10/1.00  --dbg_dump_prop_clauses                 false
% 3.10/1.00  --dbg_dump_prop_clauses_file            -
% 3.10/1.00  --dbg_out_stat                          false
% 3.10/1.00  
% 3.10/1.00  
% 3.10/1.00  
% 3.10/1.00  
% 3.10/1.00  ------ Proving...
% 3.10/1.00  
% 3.10/1.00  
% 3.10/1.00  % SZS status Theorem for theBenchmark.p
% 3.10/1.00  
% 3.10/1.00   Resolution empty clause
% 3.10/1.00  
% 3.10/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.10/1.00  
% 3.10/1.00  fof(f13,conjecture,(
% 3.10/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 3.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f14,negated_conjecture,(
% 3.10/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 3.10/1.00    inference(negated_conjecture,[],[f13])).
% 3.10/1.00  
% 3.10/1.00  fof(f27,plain,(
% 3.10/1.00    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.10/1.00    inference(ennf_transformation,[],[f14])).
% 3.10/1.00  
% 3.10/1.00  fof(f28,plain,(
% 3.10/1.00    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.10/1.00    inference(flattening,[],[f27])).
% 3.10/1.00  
% 3.10/1.00  fof(f40,plain,(
% 3.10/1.00    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK5(X3)) = X3 & r2_hidden(sK5(X3),X0)))) )),
% 3.10/1.00    introduced(choice_axiom,[])).
% 3.10/1.00  
% 3.10/1.00  fof(f39,plain,(
% 3.10/1.00    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK2,sK3,sK4) != sK3 & ! [X3] : (? [X4] : (k1_funct_1(sK4,X4) = X3 & r2_hidden(X4,sK2)) | ~r2_hidden(X3,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 3.10/1.00    introduced(choice_axiom,[])).
% 3.10/1.00  
% 3.10/1.00  fof(f41,plain,(
% 3.10/1.00    k2_relset_1(sK2,sK3,sK4) != sK3 & ! [X3] : ((k1_funct_1(sK4,sK5(X3)) = X3 & r2_hidden(sK5(X3),sK2)) | ~r2_hidden(X3,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 3.10/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f28,f40,f39])).
% 3.10/1.00  
% 3.10/1.00  fof(f66,plain,(
% 3.10/1.00    v1_funct_2(sK4,sK2,sK3)),
% 3.10/1.00    inference(cnf_transformation,[],[f41])).
% 3.10/1.00  
% 3.10/1.00  fof(f12,axiom,(
% 3.10/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f25,plain,(
% 3.10/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/1.00    inference(ennf_transformation,[],[f12])).
% 3.10/1.00  
% 3.10/1.00  fof(f26,plain,(
% 3.10/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/1.00    inference(flattening,[],[f25])).
% 3.10/1.00  
% 3.10/1.00  fof(f38,plain,(
% 3.10/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/1.00    inference(nnf_transformation,[],[f26])).
% 3.10/1.00  
% 3.10/1.00  fof(f59,plain,(
% 3.10/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.10/1.00    inference(cnf_transformation,[],[f38])).
% 3.10/1.00  
% 3.10/1.00  fof(f67,plain,(
% 3.10/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.10/1.00    inference(cnf_transformation,[],[f41])).
% 3.10/1.00  
% 3.10/1.00  fof(f10,axiom,(
% 3.10/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f23,plain,(
% 3.10/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/1.00    inference(ennf_transformation,[],[f10])).
% 3.10/1.00  
% 3.10/1.00  fof(f57,plain,(
% 3.10/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.10/1.00    inference(cnf_transformation,[],[f23])).
% 3.10/1.00  
% 3.10/1.00  fof(f6,axiom,(
% 3.10/1.00    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 3.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f18,plain,(
% 3.10/1.00    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 3.10/1.00    inference(ennf_transformation,[],[f6])).
% 3.10/1.00  
% 3.10/1.00  fof(f53,plain,(
% 3.10/1.00    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f18])).
% 3.10/1.00  
% 3.10/1.00  fof(f9,axiom,(
% 3.10/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f22,plain,(
% 3.10/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/1.00    inference(ennf_transformation,[],[f9])).
% 3.10/1.00  
% 3.10/1.00  fof(f56,plain,(
% 3.10/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.10/1.00    inference(cnf_transformation,[],[f22])).
% 3.10/1.00  
% 3.10/1.00  fof(f1,axiom,(
% 3.10/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 3.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f15,plain,(
% 3.10/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 3.10/1.00    inference(ennf_transformation,[],[f1])).
% 3.10/1.00  
% 3.10/1.00  fof(f29,plain,(
% 3.10/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 3.10/1.00    inference(nnf_transformation,[],[f15])).
% 3.10/1.00  
% 3.10/1.00  fof(f30,plain,(
% 3.10/1.00    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 3.10/1.00    introduced(choice_axiom,[])).
% 3.10/1.00  
% 3.10/1.00  fof(f31,plain,(
% 3.10/1.00    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 3.10/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 3.10/1.00  
% 3.10/1.00  fof(f42,plain,(
% 3.10/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f31])).
% 3.10/1.00  
% 3.10/1.00  fof(f5,axiom,(
% 3.10/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f17,plain,(
% 3.10/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.10/1.00    inference(ennf_transformation,[],[f5])).
% 3.10/1.00  
% 3.10/1.00  fof(f34,plain,(
% 3.10/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.10/1.00    inference(nnf_transformation,[],[f17])).
% 3.10/1.00  
% 3.10/1.00  fof(f35,plain,(
% 3.10/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.10/1.00    inference(rectify,[],[f34])).
% 3.10/1.00  
% 3.10/1.00  fof(f36,plain,(
% 3.10/1.00    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 3.10/1.00    introduced(choice_axiom,[])).
% 3.10/1.00  
% 3.10/1.00  fof(f37,plain,(
% 3.10/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.10/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 3.10/1.00  
% 3.10/1.00  fof(f50,plain,(
% 3.10/1.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f37])).
% 3.10/1.00  
% 3.10/1.00  fof(f51,plain,(
% 3.10/1.00    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f37])).
% 3.10/1.00  
% 3.10/1.00  fof(f4,axiom,(
% 3.10/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f16,plain,(
% 3.10/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.10/1.00    inference(ennf_transformation,[],[f4])).
% 3.10/1.00  
% 3.10/1.00  fof(f48,plain,(
% 3.10/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.10/1.00    inference(cnf_transformation,[],[f16])).
% 3.10/1.00  
% 3.10/1.00  fof(f3,axiom,(
% 3.10/1.00    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 3.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f32,plain,(
% 3.10/1.00    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.10/1.00    inference(nnf_transformation,[],[f3])).
% 3.10/1.00  
% 3.10/1.00  fof(f33,plain,(
% 3.10/1.00    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.10/1.00    inference(flattening,[],[f32])).
% 3.10/1.00  
% 3.10/1.00  fof(f46,plain,(
% 3.10/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.10/1.00    inference(cnf_transformation,[],[f33])).
% 3.10/1.00  
% 3.10/1.00  fof(f69,plain,(
% 3.10/1.00    ( ! [X3] : (k1_funct_1(sK4,sK5(X3)) = X3 | ~r2_hidden(X3,sK3)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f41])).
% 3.10/1.00  
% 3.10/1.00  fof(f11,axiom,(
% 3.10/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f24,plain,(
% 3.10/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/1.00    inference(ennf_transformation,[],[f11])).
% 3.10/1.00  
% 3.10/1.00  fof(f58,plain,(
% 3.10/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.10/1.00    inference(cnf_transformation,[],[f24])).
% 3.10/1.00  
% 3.10/1.00  fof(f70,plain,(
% 3.10/1.00    k2_relset_1(sK2,sK3,sK4) != sK3),
% 3.10/1.00    inference(cnf_transformation,[],[f41])).
% 3.10/1.00  
% 3.10/1.00  fof(f68,plain,(
% 3.10/1.00    ( ! [X3] : (r2_hidden(sK5(X3),sK2) | ~r2_hidden(X3,sK3)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f41])).
% 3.10/1.00  
% 3.10/1.00  fof(f7,axiom,(
% 3.10/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 3.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f19,plain,(
% 3.10/1.00    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.10/1.00    inference(ennf_transformation,[],[f7])).
% 3.10/1.00  
% 3.10/1.00  fof(f20,plain,(
% 3.10/1.00    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.10/1.00    inference(flattening,[],[f19])).
% 3.10/1.00  
% 3.10/1.00  fof(f54,plain,(
% 3.10/1.00    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f20])).
% 3.10/1.00  
% 3.10/1.00  fof(f65,plain,(
% 3.10/1.00    v1_funct_1(sK4)),
% 3.10/1.00    inference(cnf_transformation,[],[f41])).
% 3.10/1.00  
% 3.10/1.00  fof(f43,plain,(
% 3.10/1.00    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f31])).
% 3.10/1.00  
% 3.10/1.00  fof(f2,axiom,(
% 3.10/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f44,plain,(
% 3.10/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f2])).
% 3.10/1.00  
% 3.10/1.00  fof(f8,axiom,(
% 3.10/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f21,plain,(
% 3.10/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.10/1.00    inference(ennf_transformation,[],[f8])).
% 3.10/1.00  
% 3.10/1.00  fof(f55,plain,(
% 3.10/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f21])).
% 3.10/1.00  
% 3.10/1.00  cnf(c_27,negated_conjecture,
% 3.10/1.00      ( v1_funct_2(sK4,sK2,sK3) ),
% 3.10/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_22,plain,
% 3.10/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.10/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.10/1.00      | k1_xboole_0 = X2 ),
% 3.10/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_26,negated_conjecture,
% 3.10/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.10/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_477,plain,
% 3.10/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.10/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 3.10/1.00      | sK4 != X0
% 3.10/1.00      | k1_xboole_0 = X2 ),
% 3.10/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_478,plain,
% 3.10/1.00      ( ~ v1_funct_2(sK4,X0,X1)
% 3.10/1.00      | k1_relset_1(X0,X1,sK4) = X0
% 3.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 3.10/1.00      | k1_xboole_0 = X1 ),
% 3.10/1.00      inference(unflattening,[status(thm)],[c_477]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_766,plain,
% 3.10/1.00      ( k1_relset_1(X0,X1,sK4) = X0
% 3.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 3.10/1.00      | sK4 != sK4
% 3.10/1.00      | sK3 != X1
% 3.10/1.00      | sK2 != X0
% 3.10/1.00      | k1_xboole_0 = X1 ),
% 3.10/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_478]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_767,plain,
% 3.10/1.00      ( k1_relset_1(sK2,sK3,sK4) = sK2
% 3.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 3.10/1.00      | k1_xboole_0 = sK3 ),
% 3.10/1.00      inference(unflattening,[status(thm)],[c_766]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_834,plain,
% 3.10/1.00      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 3.10/1.00      inference(equality_resolution_simp,[status(thm)],[c_767]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_15,plain,
% 3.10/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.10/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_522,plain,
% 3.10/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 3.10/1.00      | sK4 != X2 ),
% 3.10/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_26]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_523,plain,
% 3.10/1.00      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 3.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 3.10/1.00      inference(unflattening,[status(thm)],[c_522]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1520,plain,
% 3.10/1.00      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 3.10/1.00      inference(equality_resolution,[status(thm)],[c_523]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1677,plain,
% 3.10/1.00      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 3.10/1.00      inference(demodulation,[status(thm)],[c_834,c_1520]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_11,plain,
% 3.10/1.00      ( ~ v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 3.10/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_14,plain,
% 3.10/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.10/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_531,plain,
% 3.10/1.00      ( v1_relat_1(X0)
% 3.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 3.10/1.00      | sK4 != X0 ),
% 3.10/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_532,plain,
% 3.10/1.00      ( v1_relat_1(sK4)
% 3.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 3.10/1.00      inference(unflattening,[status(thm)],[c_531]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_725,plain,
% 3.10/1.00      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 3.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 3.10/1.00      | sK4 != X0 ),
% 3.10/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_532]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_726,plain,
% 3.10/1.00      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4)
% 3.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 3.10/1.00      inference(unflattening,[status(thm)],[c_725]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_935,plain,( X0 = X0 ),theory(equality) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1503,plain,
% 3.10/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 3.10/1.00      inference(instantiation,[status(thm)],[c_935]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1505,plain,
% 3.10/1.00      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4)
% 3.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 3.10/1.00      inference(instantiation,[status(thm)],[c_726]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1585,plain,
% 3.10/1.00      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
% 3.10/1.00      inference(global_propositional_subsumption,
% 3.10/1.00                [status(thm)],
% 3.10/1.00                [c_726,c_1503,c_1505]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1680,plain,
% 3.10/1.00      ( k9_relat_1(sK4,sK2) = k2_relat_1(sK4) | sK3 = k1_xboole_0 ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_1677,c_1585]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1,plain,
% 3.10/1.00      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 3.10/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1318,plain,
% 3.10/1.00      ( X0 = X1
% 3.10/1.00      | r2_hidden(sK0(X1,X0),X0) = iProver_top
% 3.10/1.00      | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_9,plain,
% 3.10/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.10/1.00      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 3.10/1.00      | ~ v1_relat_1(X1) ),
% 3.10/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_695,plain,
% 3.10/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.10/1.00      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 3.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 3.10/1.00      | sK4 != X1 ),
% 3.10/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_532]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_696,plain,
% 3.10/1.00      ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
% 3.10/1.00      | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4)
% 3.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 3.10/1.00      inference(unflattening,[status(thm)],[c_695]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_926,plain,
% 3.10/1.00      ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
% 3.10/1.00      | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4)
% 3.10/1.00      | ~ sP2_iProver_split ),
% 3.10/1.00      inference(splitting,
% 3.10/1.00                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 3.10/1.00                [c_696]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1300,plain,
% 3.10/1.00      ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 3.10/1.00      | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4) = iProver_top
% 3.10/1.00      | sP2_iProver_split != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_926]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_927,plain,
% 3.10/1.00      ( sP2_iProver_split | sP0_iProver_split ),
% 3.10/1.00      inference(splitting,
% 3.10/1.00                [splitting(split),new_symbols(definition,[])],
% 3.10/1.00                [c_696]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_968,plain,
% 3.10/1.00      ( sP2_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_927]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_969,plain,
% 3.10/1.00      ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 3.10/1.00      | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4) = iProver_top
% 3.10/1.00      | sP2_iProver_split != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_926]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_8,plain,
% 3.10/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.10/1.00      | r2_hidden(sK1(X0,X2,X1),X2)
% 3.10/1.00      | ~ v1_relat_1(X1) ),
% 3.10/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_710,plain,
% 3.10/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.10/1.00      | r2_hidden(sK1(X0,X2,X1),X2)
% 3.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 3.10/1.00      | sK4 != X1 ),
% 3.10/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_532]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_711,plain,
% 3.10/1.00      ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
% 3.10/1.00      | r2_hidden(sK1(X0,X1,sK4),X1)
% 3.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 3.10/1.00      inference(unflattening,[status(thm)],[c_710]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_923,plain,
% 3.10/1.00      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 3.10/1.00      | ~ sP0_iProver_split ),
% 3.10/1.00      inference(splitting,
% 3.10/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.10/1.00                [c_711]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1504,plain,
% 3.10/1.00      ( ~ sP0_iProver_split
% 3.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 3.10/1.00      inference(instantiation,[status(thm)],[c_923]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1508,plain,
% 3.10/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 3.10/1.00      | sP0_iProver_split != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_1504]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2326,plain,
% 3.10/1.00      ( r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4) = iProver_top
% 3.10/1.00      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
% 3.10/1.00      inference(global_propositional_subsumption,
% 3.10/1.00                [status(thm)],
% 3.10/1.00                [c_1300,c_968,c_969,c_1503,c_1508]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2327,plain,
% 3.10/1.00      ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 3.10/1.00      | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4) = iProver_top ),
% 3.10/1.00      inference(renaming,[status(thm)],[c_2326]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_6,plain,
% 3.10/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.10/1.00      | ~ r2_hidden(X2,X0)
% 3.10/1.00      | r2_hidden(X2,X1) ),
% 3.10/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_462,plain,
% 3.10/1.00      ( ~ r2_hidden(X0,X1)
% 3.10/1.00      | r2_hidden(X0,X2)
% 3.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X2)
% 3.10/1.00      | sK4 != X1 ),
% 3.10/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_26]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_463,plain,
% 3.10/1.00      ( r2_hidden(X0,X1)
% 3.10/1.00      | ~ r2_hidden(X0,sK4)
% 3.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X1) ),
% 3.10/1.00      inference(unflattening,[status(thm)],[c_462]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1311,plain,
% 3.10/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X0)
% 3.10/1.00      | r2_hidden(X1,X0) = iProver_top
% 3.10/1.00      | r2_hidden(X1,sK4) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_463]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1673,plain,
% 3.10/1.00      ( r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
% 3.10/1.00      | r2_hidden(X0,sK4) != iProver_top ),
% 3.10/1.00      inference(equality_resolution,[status(thm)],[c_1311]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_4,plain,
% 3.10/1.00      ( r2_hidden(X0,X1) | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.10/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1316,plain,
% 3.10/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.10/1.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1842,plain,
% 3.10/1.00      ( r2_hidden(X0,sK3) = iProver_top
% 3.10/1.00      | r2_hidden(k4_tarski(X1,X0),sK4) != iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_1673,c_1316]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2335,plain,
% 3.10/1.00      ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 3.10/1.00      | r2_hidden(X0,sK3) = iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_2327,c_1842]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_3325,plain,
% 3.10/1.00      ( k9_relat_1(sK4,X0) = X1
% 3.10/1.00      | r2_hidden(sK0(X1,k9_relat_1(sK4,X0)),X1) = iProver_top
% 3.10/1.00      | r2_hidden(sK0(X1,k9_relat_1(sK4,X0)),sK3) = iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_1318,c_2335]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_24,negated_conjecture,
% 3.10/1.00      ( ~ r2_hidden(X0,sK3) | k1_funct_1(sK4,sK5(X0)) = X0 ),
% 3.10/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1314,plain,
% 3.10/1.00      ( k1_funct_1(sK4,sK5(X0)) = X0 | r2_hidden(X0,sK3) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_3552,plain,
% 3.10/1.00      ( k1_funct_1(sK4,sK5(sK0(X0,k9_relat_1(sK4,X1)))) = sK0(X0,k9_relat_1(sK4,X1))
% 3.10/1.00      | k9_relat_1(sK4,X1) = X0
% 3.10/1.00      | r2_hidden(sK0(X0,k9_relat_1(sK4,X1)),X0) = iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_3325,c_1314]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_3629,plain,
% 3.10/1.00      ( k1_funct_1(sK4,sK5(sK0(sK3,k9_relat_1(sK4,X0)))) = sK0(sK3,k9_relat_1(sK4,X0))
% 3.10/1.00      | k9_relat_1(sK4,X0) = sK3 ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_3552,c_1314]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_3761,plain,
% 3.10/1.00      ( k1_funct_1(sK4,sK5(sK0(sK3,k2_relat_1(sK4)))) = sK0(sK3,k9_relat_1(sK4,sK2))
% 3.10/1.00      | k9_relat_1(sK4,sK2) = sK3
% 3.10/1.00      | sK3 = k1_xboole_0 ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_1680,c_3629]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_3760,plain,
% 3.10/1.00      ( k1_funct_1(sK4,sK5(sK0(sK3,k2_relat_1(sK4)))) = sK0(sK3,k9_relat_1(sK4,k1_relat_1(sK4)))
% 3.10/1.00      | k9_relat_1(sK4,k1_relat_1(sK4)) = sK3 ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_1585,c_3629]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_3777,plain,
% 3.10/1.00      ( k1_funct_1(sK4,sK5(sK0(sK3,k2_relat_1(sK4)))) = sK0(sK3,k2_relat_1(sK4))
% 3.10/1.00      | k9_relat_1(sK4,k1_relat_1(sK4)) = sK3 ),
% 3.10/1.00      inference(light_normalisation,[status(thm)],[c_3760,c_1585]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_3778,plain,
% 3.10/1.00      ( k1_funct_1(sK4,sK5(sK0(sK3,k2_relat_1(sK4)))) = sK0(sK3,k2_relat_1(sK4))
% 3.10/1.00      | k2_relat_1(sK4) = sK3 ),
% 3.10/1.00      inference(demodulation,[status(thm)],[c_3777,c_1585]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_16,plain,
% 3.10/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.10/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_513,plain,
% 3.10/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 3.10/1.00      | sK4 != X2 ),
% 3.10/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_26]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_514,plain,
% 3.10/1.00      ( k2_relset_1(X0,X1,sK4) = k2_relat_1(sK4)
% 3.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 3.10/1.00      inference(unflattening,[status(thm)],[c_513]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1502,plain,
% 3.10/1.00      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 3.10/1.00      inference(equality_resolution,[status(thm)],[c_514]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_23,negated_conjecture,
% 3.10/1.00      ( k2_relset_1(sK2,sK3,sK4) != sK3 ),
% 3.10/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1557,plain,
% 3.10/1.00      ( k2_relat_1(sK4) != sK3 ),
% 3.10/1.00      inference(demodulation,[status(thm)],[c_1502,c_23]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_3880,plain,
% 3.10/1.00      ( k1_funct_1(sK4,sK5(sK0(sK3,k2_relat_1(sK4)))) = sK0(sK3,k2_relat_1(sK4)) ),
% 3.10/1.00      inference(global_propositional_subsumption,[status(thm)],[c_3778,c_1557]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_4053,plain,
% 3.10/1.00      ( k9_relat_1(sK4,sK2) = sK3
% 3.10/1.00      | sK0(sK3,k9_relat_1(sK4,sK2)) = sK0(sK3,k2_relat_1(sK4))
% 3.10/1.00      | sK3 = k1_xboole_0 ),
% 3.10/1.00      inference(light_normalisation,[status(thm)],[c_3761,c_3880]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_4059,plain,
% 3.10/1.00      ( k9_relat_1(sK4,sK2) = sK3
% 3.10/1.00      | sK3 = k1_xboole_0
% 3.10/1.00      | r2_hidden(sK0(sK3,k9_relat_1(sK4,sK2)),k9_relat_1(sK4,sK2)) = iProver_top
% 3.10/1.00      | r2_hidden(sK0(sK3,k2_relat_1(sK4)),sK3) = iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_4053,c_1318]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_3550,plain,
% 3.10/1.00      ( k9_relat_1(sK4,k1_relat_1(sK4)) = X0
% 3.10/1.00      | r2_hidden(sK0(X0,k9_relat_1(sK4,k1_relat_1(sK4))),sK3) = iProver_top
% 3.10/1.00      | r2_hidden(sK0(X0,k2_relat_1(sK4)),X0) = iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_1585,c_3325]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_3587,plain,
% 3.10/1.00      ( k9_relat_1(sK4,k1_relat_1(sK4)) = X0
% 3.10/1.00      | r2_hidden(sK0(X0,k2_relat_1(sK4)),X0) = iProver_top
% 3.10/1.00      | r2_hidden(sK0(X0,k2_relat_1(sK4)),sK3) = iProver_top ),
% 3.10/1.00      inference(light_normalisation,[status(thm)],[c_3550,c_1585]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_3588,plain,
% 3.10/1.00      ( k2_relat_1(sK4) = X0
% 3.10/1.00      | r2_hidden(sK0(X0,k2_relat_1(sK4)),X0) = iProver_top
% 3.10/1.00      | r2_hidden(sK0(X0,k2_relat_1(sK4)),sK3) = iProver_top ),
% 3.10/1.00      inference(demodulation,[status(thm)],[c_3587,c_1585]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_4002,plain,
% 3.10/1.00      ( k2_relat_1(sK4) = sK3
% 3.10/1.00      | r2_hidden(sK0(sK3,k2_relat_1(sK4)),sK3) = iProver_top
% 3.10/1.00      | iProver_top != iProver_top ),
% 3.10/1.00      inference(equality_factoring,[status(thm)],[c_3588]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_4004,plain,
% 3.10/1.00      ( k2_relat_1(sK4) = sK3
% 3.10/1.00      | r2_hidden(sK0(sK3,k2_relat_1(sK4)),sK3) = iProver_top ),
% 3.10/1.00      inference(equality_resolution_simp,[status(thm)],[c_4002]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5168,plain,
% 3.10/1.00      ( r2_hidden(sK0(sK3,k2_relat_1(sK4)),sK3) = iProver_top ),
% 3.10/1.00      inference(global_propositional_subsumption,
% 3.10/1.00                [status(thm)],
% 3.10/1.00                [c_4059,c_1557,c_4004]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_3326,plain,
% 3.10/1.00      ( k9_relat_1(sK4,X0) = X1
% 3.10/1.00      | r2_hidden(sK0(k9_relat_1(sK4,X0),X1),X1) = iProver_top
% 3.10/1.00      | r2_hidden(sK0(k9_relat_1(sK4,X0),X1),sK3) = iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_1318,c_2335]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_4208,plain,
% 3.10/1.00      ( k1_funct_1(sK4,sK5(sK0(k9_relat_1(sK4,X0),X1))) = sK0(k9_relat_1(sK4,X0),X1)
% 3.10/1.00      | k9_relat_1(sK4,X0) = X1
% 3.10/1.00      | r2_hidden(sK0(k9_relat_1(sK4,X0),X1),X1) = iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_3326,c_1314]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_4433,plain,
% 3.10/1.00      ( k1_funct_1(sK4,sK5(sK0(k9_relat_1(sK4,X0),sK3))) = sK0(k9_relat_1(sK4,X0),sK3)
% 3.10/1.00      | k9_relat_1(sK4,X0) = sK3 ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_4208,c_1314]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_4600,plain,
% 3.10/1.00      ( k1_funct_1(sK4,sK5(sK0(k2_relat_1(sK4),sK3))) = sK0(k9_relat_1(sK4,sK2),sK3)
% 3.10/1.00      | k9_relat_1(sK4,sK2) = sK3
% 3.10/1.00      | sK3 = k1_xboole_0 ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_1680,c_4433]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_3336,plain,
% 3.10/1.00      ( r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
% 3.10/1.00      | r2_hidden(X0,sK3) = iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_1585,c_2335]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_3788,plain,
% 3.10/1.00      ( k2_relat_1(sK4) = X0
% 3.10/1.00      | r2_hidden(sK0(k2_relat_1(sK4),X0),X0) = iProver_top
% 3.10/1.00      | r2_hidden(sK0(k2_relat_1(sK4),X0),sK3) = iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_1318,c_3336]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_4113,plain,
% 3.10/1.00      ( k1_funct_1(sK4,sK5(sK0(k2_relat_1(sK4),X0))) = sK0(k2_relat_1(sK4),X0)
% 3.10/1.00      | k2_relat_1(sK4) = X0
% 3.10/1.00      | r2_hidden(sK0(k2_relat_1(sK4),X0),X0) = iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_3788,c_1314]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_4280,plain,
% 3.10/1.00      ( k1_funct_1(sK4,sK5(sK0(k2_relat_1(sK4),sK3))) = sK0(k2_relat_1(sK4),sK3)
% 3.10/1.00      | k2_relat_1(sK4) = sK3 ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_4113,c_1314]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_4422,plain,
% 3.10/1.00      ( k1_funct_1(sK4,sK5(sK0(k2_relat_1(sK4),sK3))) = sK0(k2_relat_1(sK4),sK3) ),
% 3.10/1.00      inference(global_propositional_subsumption,[status(thm)],[c_4280,c_1557]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_4611,plain,
% 3.10/1.00      ( k9_relat_1(sK4,sK2) = sK3
% 3.10/1.00      | sK0(k9_relat_1(sK4,sK2),sK3) = sK0(k2_relat_1(sK4),sK3)
% 3.10/1.00      | sK3 = k1_xboole_0 ),
% 3.10/1.00      inference(light_normalisation,[status(thm)],[c_4600,c_4422]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_25,negated_conjecture,
% 3.10/1.00      ( ~ r2_hidden(X0,sK3) | r2_hidden(sK5(X0),sK2) ),
% 3.10/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2240,plain,
% 3.10/1.00      ( ~ r2_hidden(sK0(X0,sK3),sK3) | r2_hidden(sK5(sK0(X0,sK3)),sK2) ),
% 3.10/1.00      inference(instantiation,[status(thm)],[c_25]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_3447,plain,
% 3.10/1.00      ( ~ r2_hidden(sK0(k2_relat_1(sK4),sK3),sK3)
% 3.10/1.00      | r2_hidden(sK5(sK0(k2_relat_1(sK4),sK3)),sK2) ),
% 3.10/1.00      inference(instantiation,[status(thm)],[c_2240]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_3448,plain,
% 3.10/1.00      ( r2_hidden(sK0(k2_relat_1(sK4),sK3),sK3) != iProver_top
% 3.10/1.00      | r2_hidden(sK5(sK0(k2_relat_1(sK4),sK3)),sK2) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_3447]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_4122,plain,
% 3.10/1.00      ( k2_relat_1(sK4) = sK3
% 3.10/1.00      | r2_hidden(sK0(k2_relat_1(sK4),sK3),sK3) = iProver_top
% 3.10/1.00      | iProver_top != iProver_top ),
% 3.10/1.00      inference(equality_factoring,[status(thm)],[c_3788]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_4124,plain,
% 3.10/1.00      ( k2_relat_1(sK4) = sK3
% 3.10/1.00      | r2_hidden(sK0(k2_relat_1(sK4),sK3),sK3) = iProver_top ),
% 3.10/1.00      inference(equality_resolution_simp,[status(thm)],[c_4122]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_12,plain,
% 3.10/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.10/1.00      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.10/1.00      | ~ v1_funct_1(X1)
% 3.10/1.00      | ~ v1_relat_1(X1) ),
% 3.10/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_28,negated_conjecture,
% 3.10/1.00      ( v1_funct_1(sK4) ),
% 3.10/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_334,plain,
% 3.10/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.10/1.00      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.10/1.00      | ~ v1_relat_1(X1)
% 3.10/1.00      | sK4 != X1 ),
% 3.10/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_28]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_335,plain,
% 3.10/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 3.10/1.00      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
% 3.10/1.00      | ~ v1_relat_1(sK4) ),
% 3.10/1.00      inference(unflattening,[status(thm)],[c_334]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_647,plain,
% 3.10/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 3.10/1.00      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
% 3.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 3.10/1.00      inference(resolution,[status(thm)],[c_532,c_335]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_932,plain,
% 3.10/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 3.10/1.00      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
% 3.10/1.00      | ~ sP5_iProver_split ),
% 3.10/1.00      inference(splitting,
% 3.10/1.00                [splitting(split),new_symbols(definition,[sP5_iProver_split])],
% 3.10/1.00                [c_647]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1309,plain,
% 3.10/1.00      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.10/1.00      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
% 3.10/1.00      | sP5_iProver_split != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_932]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_933,plain,
% 3.10/1.00      ( sP5_iProver_split | sP0_iProver_split ),
% 3.10/1.00      inference(splitting,
% 3.10/1.00                [splitting(split),new_symbols(definition,[])],
% 3.10/1.00                [c_647]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_981,plain,
% 3.10/1.00      ( sP5_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_933]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_982,plain,
% 3.10/1.00      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.10/1.00      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
% 3.10/1.00      | sP5_iProver_split != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_932]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2255,plain,
% 3.10/1.00      ( r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
% 3.10/1.00      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 3.10/1.00      inference(global_propositional_subsumption,
% 3.10/1.00                [status(thm)],
% 3.10/1.00                [c_1309,c_981,c_982,c_1503,c_1508]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2256,plain,
% 3.10/1.00      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.10/1.00      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
% 3.10/1.00      inference(renaming,[status(thm)],[c_2255]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_4425,plain,
% 3.10/1.00      ( r2_hidden(sK0(k2_relat_1(sK4),sK3),k2_relat_1(sK4)) = iProver_top
% 3.10/1.00      | r2_hidden(sK5(sK0(k2_relat_1(sK4),sK3)),k1_relat_1(sK4)) != iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_4422,c_2256]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_936,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1512,plain,
% 3.10/1.00      ( k2_relset_1(sK2,sK3,sK4) != X0
% 3.10/1.00      | k2_relset_1(sK2,sK3,sK4) = sK3
% 3.10/1.00      | sK3 != X0 ),
% 3.10/1.00      inference(instantiation,[status(thm)],[c_936]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1584,plain,
% 3.10/1.00      ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
% 3.10/1.00      | k2_relset_1(sK2,sK3,sK4) = sK3
% 3.10/1.00      | sK3 != k2_relat_1(sK4) ),
% 3.10/1.00      inference(instantiation,[status(thm)],[c_1512]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_0,plain,
% 3.10/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | ~ r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 3.10/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1658,plain,
% 3.10/1.00      ( ~ r2_hidden(sK0(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
% 3.10/1.00      | ~ r2_hidden(sK0(k2_relat_1(sK4),sK3),sK3)
% 3.10/1.00      | sK3 = k2_relat_1(sK4) ),
% 3.10/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1659,plain,
% 3.10/1.00      ( sK3 = k2_relat_1(sK4)
% 3.10/1.00      | r2_hidden(sK0(k2_relat_1(sK4),sK3),k2_relat_1(sK4)) != iProver_top
% 3.10/1.00      | r2_hidden(sK0(k2_relat_1(sK4),sK3),sK3) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_1658]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_4622,plain,
% 3.10/1.00      ( r2_hidden(sK5(sK0(k2_relat_1(sK4),sK3)),k1_relat_1(sK4)) != iProver_top ),
% 3.10/1.00      inference(global_propositional_subsumption,
% 3.10/1.00                [status(thm)],
% 3.10/1.00                [c_4425,c_23,c_1502,c_1557,c_1584,c_1659,c_4124]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_4627,plain,
% 3.10/1.00      ( sK3 = k1_xboole_0
% 3.10/1.00      | r2_hidden(sK5(sK0(k2_relat_1(sK4),sK3)),sK2) != iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_1677,c_4622]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_4701,plain,
% 3.10/1.00      ( sK3 = k1_xboole_0 ),
% 3.10/1.00      inference(global_propositional_subsumption,
% 3.10/1.00                [status(thm)],
% 3.10/1.00                [c_4611,c_1557,c_3448,c_4124,c_4627]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5172,plain,
% 3.10/1.00      ( r2_hidden(sK0(k1_xboole_0,k2_relat_1(sK4)),k1_xboole_0) = iProver_top ),
% 3.10/1.00      inference(light_normalisation,[status(thm)],[c_5168,c_4701]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2,plain,
% 3.10/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.10/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_13,plain,
% 3.10/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.10/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_323,plain,
% 3.10/1.00      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 3.10/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_13]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_324,plain,
% 3.10/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.10/1.00      inference(unflattening,[status(thm)],[c_323]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1312,plain,
% 3.10/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_324]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5174,plain,
% 3.10/1.00      ( $false ),
% 3.10/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_5172,c_1312]) ).
% 3.10/1.00  
% 3.10/1.00  
% 3.10/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.10/1.00  
% 3.10/1.00  ------                               Statistics
% 3.10/1.00  
% 3.10/1.00  ------ General
% 3.10/1.00  
% 3.10/1.00  abstr_ref_over_cycles:                  0
% 3.10/1.00  abstr_ref_under_cycles:                 0
% 3.10/1.00  gc_basic_clause_elim:                   0
% 3.10/1.00  forced_gc_time:                         0
% 3.10/1.00  parsing_time:                           0.019
% 3.10/1.00  unif_index_cands_time:                  0.
% 3.10/1.00  unif_index_add_time:                    0.
% 3.10/1.00  orderings_time:                         0.
% 3.10/1.00  out_proof_time:                         0.013
% 3.10/1.00  total_time:                             0.207
% 3.10/1.00  num_of_symbols:                         59
% 3.10/1.00  num_of_terms:                           5587
% 3.10/1.00  
% 3.10/1.00  ------ Preprocessing
% 3.10/1.00  
% 3.10/1.00  num_of_splits:                          10
% 3.10/1.00  num_of_split_atoms:                     6
% 3.10/1.00  num_of_reused_defs:                     4
% 3.10/1.00  num_eq_ax_congr_red:                    26
% 3.10/1.00  num_of_sem_filtered_clauses:            1
% 3.10/1.00  num_of_subtypes:                        0
% 3.10/1.00  monotx_restored_types:                  0
% 3.10/1.00  sat_num_of_epr_types:                   0
% 3.10/1.00  sat_num_of_non_cyclic_types:            0
% 3.10/1.00  sat_guarded_non_collapsed_types:        0
% 3.10/1.00  num_pure_diseq_elim:                    0
% 3.10/1.00  simp_replaced_by:                       0
% 3.10/1.00  res_preprocessed:                       131
% 3.10/1.00  prep_upred:                             0
% 3.10/1.00  prep_unflattend:                        39
% 3.10/1.00  smt_new_axioms:                         0
% 3.10/1.00  pred_elim_cands:                        1
% 3.10/1.00  pred_elim:                              5
% 3.10/1.00  pred_elim_cl:                           8
% 3.10/1.00  pred_elim_cycles:                       8
% 3.10/1.00  merged_defs:                            0
% 3.10/1.00  merged_defs_ncl:                        0
% 3.10/1.00  bin_hyper_res:                          0
% 3.10/1.00  prep_cycles:                            4
% 3.10/1.00  pred_elim_time:                         0.01
% 3.10/1.00  splitting_time:                         0.
% 3.10/1.00  sem_filter_time:                        0.
% 3.10/1.00  monotx_time:                            0.
% 3.10/1.00  subtype_inf_time:                       0.
% 3.10/1.00  
% 3.10/1.00  ------ Problem properties
% 3.10/1.00  
% 3.10/1.00  clauses:                                31
% 3.10/1.00  conjectures:                            3
% 3.10/1.00  epr:                                    6
% 3.10/1.00  horn:                                   23
% 3.10/1.00  ground:                                 9
% 3.10/1.00  unary:                                  2
% 3.10/1.00  binary:                                 18
% 3.10/1.00  lits:                                   74
% 3.10/1.00  lits_eq:                                25
% 3.10/1.00  fd_pure:                                0
% 3.10/1.00  fd_pseudo:                              0
% 3.10/1.00  fd_cond:                                0
% 3.10/1.00  fd_pseudo_cond:                         2
% 3.10/1.00  ac_symbols:                             0
% 3.10/1.00  
% 3.10/1.00  ------ Propositional Solver
% 3.10/1.00  
% 3.10/1.00  prop_solver_calls:                      28
% 3.10/1.00  prop_fast_solver_calls:                 967
% 3.10/1.00  smt_solver_calls:                       0
% 3.10/1.00  smt_fast_solver_calls:                  0
% 3.10/1.00  prop_num_of_clauses:                    1869
% 3.10/1.00  prop_preprocess_simplified:             5382
% 3.10/1.00  prop_fo_subsumed:                       24
% 3.10/1.00  prop_solver_time:                       0.
% 3.10/1.00  smt_solver_time:                        0.
% 3.10/1.00  smt_fast_solver_time:                   0.
% 3.10/1.00  prop_fast_solver_time:                  0.
% 3.10/1.00  prop_unsat_core_time:                   0.
% 3.10/1.00  
% 3.10/1.00  ------ QBF
% 3.10/1.00  
% 3.10/1.00  qbf_q_res:                              0
% 3.10/1.00  qbf_num_tautologies:                    0
% 3.10/1.00  qbf_prep_cycles:                        0
% 3.10/1.00  
% 3.10/1.00  ------ BMC1
% 3.10/1.00  
% 3.10/1.00  bmc1_current_bound:                     -1
% 3.10/1.00  bmc1_last_solved_bound:                 -1
% 3.10/1.00  bmc1_unsat_core_size:                   -1
% 3.10/1.00  bmc1_unsat_core_parents_size:           -1
% 3.10/1.00  bmc1_merge_next_fun:                    0
% 3.10/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.10/1.00  
% 3.10/1.00  ------ Instantiation
% 3.10/1.00  
% 3.10/1.00  inst_num_of_clauses:                    534
% 3.10/1.00  inst_num_in_passive:                    92
% 3.10/1.00  inst_num_in_active:                     260
% 3.10/1.00  inst_num_in_unprocessed:                183
% 3.10/1.00  inst_num_of_loops:                      370
% 3.10/1.00  inst_num_of_learning_restarts:          0
% 3.10/1.00  inst_num_moves_active_passive:          106
% 3.10/1.00  inst_lit_activity:                      0
% 3.10/1.00  inst_lit_activity_moves:                0
% 3.10/1.00  inst_num_tautologies:                   0
% 3.10/1.00  inst_num_prop_implied:                  0
% 3.10/1.00  inst_num_existing_simplified:           0
% 3.10/1.00  inst_num_eq_res_simplified:             0
% 3.10/1.00  inst_num_child_elim:                    0
% 3.10/1.00  inst_num_of_dismatching_blockings:      88
% 3.10/1.00  inst_num_of_non_proper_insts:           380
% 3.10/1.00  inst_num_of_duplicates:                 0
% 3.10/1.00  inst_inst_num_from_inst_to_res:         0
% 3.10/1.00  inst_dismatching_checking_time:         0.
% 3.10/1.00  
% 3.10/1.00  ------ Resolution
% 3.10/1.00  
% 3.10/1.00  res_num_of_clauses:                     0
% 3.10/1.00  res_num_in_passive:                     0
% 3.10/1.00  res_num_in_active:                      0
% 3.10/1.00  res_num_of_loops:                       135
% 3.10/1.00  res_forward_subset_subsumed:            41
% 3.10/1.00  res_backward_subset_subsumed:           2
% 3.10/1.00  res_forward_subsumed:                   0
% 3.10/1.00  res_backward_subsumed:                  0
% 3.10/1.00  res_forward_subsumption_resolution:     0
% 3.10/1.00  res_backward_subsumption_resolution:    0
% 3.10/1.00  res_clause_to_clause_subsumption:       335
% 3.10/1.00  res_orphan_elimination:                 0
% 3.10/1.00  res_tautology_del:                      27
% 3.10/1.00  res_num_eq_res_simplified:              1
% 3.10/1.00  res_num_sel_changes:                    0
% 3.10/1.00  res_moves_from_active_to_pass:          0
% 3.10/1.00  
% 3.10/1.00  ------ Superposition
% 3.10/1.00  
% 3.10/1.00  sup_time_total:                         0.
% 3.10/1.00  sup_time_generating:                    0.
% 3.10/1.00  sup_time_sim_full:                      0.
% 3.10/1.00  sup_time_sim_immed:                     0.
% 3.10/1.00  
% 3.10/1.00  sup_num_of_clauses:                     120
% 3.10/1.00  sup_num_in_active:                      33
% 3.10/1.00  sup_num_in_passive:                     87
% 3.10/1.00  sup_num_of_loops:                       72
% 3.10/1.00  sup_fw_superposition:                   76
% 3.10/1.00  sup_bw_superposition:                   115
% 3.10/1.00  sup_immediate_simplified:               34
% 3.10/1.00  sup_given_eliminated:                   0
% 3.10/1.00  comparisons_done:                       0
% 3.10/1.00  comparisons_avoided:                    59
% 3.10/1.00  
% 3.10/1.00  ------ Simplifications
% 3.10/1.00  
% 3.10/1.00  
% 3.10/1.00  sim_fw_subset_subsumed:                 7
% 3.10/1.00  sim_bw_subset_subsumed:                 8
% 3.10/1.00  sim_fw_subsumed:                        15
% 3.10/1.00  sim_bw_subsumed:                        2
% 3.10/1.00  sim_fw_subsumption_res:                 1
% 3.10/1.00  sim_bw_subsumption_res:                 0
% 3.10/1.00  sim_tautology_del:                      4
% 3.10/1.00  sim_eq_tautology_del:                   24
% 3.10/1.00  sim_eq_res_simp:                        5
% 3.10/1.00  sim_fw_demodulated:                     9
% 3.10/1.00  sim_bw_demodulated:                     38
% 3.10/1.00  sim_light_normalised:                   15
% 3.10/1.00  sim_joinable_taut:                      0
% 3.10/1.00  sim_joinable_simp:                      0
% 3.10/1.00  sim_ac_normalised:                      0
% 3.10/1.00  sim_smt_subsumption:                    0
% 3.10/1.00  
%------------------------------------------------------------------------------
