%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:56 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  251 (436624 expanded)
%              Number of clauses        :  185 (137463 expanded)
%              Number of leaves         :   17 (84996 expanded)
%              Depth                    :   53
%              Number of atoms          :  870 (2994122 expanded)
%              Number of equality atoms :  476 (924117 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
        <=> ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
            | ~ r2_hidden(X5,X0)
            | ~ r2_hidden(X4,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(rectify,[],[f37])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( sK4 != sK5
        & k1_funct_1(X1,sK4) = k1_funct_1(X1,sK5)
        & r2_hidden(sK5,X0)
        & r2_hidden(sK4,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( ( ? [X2,X3] :
              ( X2 != X3
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | ~ v2_funct_1(X1) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X0) )
          | v2_funct_1(X1) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ? [X3,X2] :
            ( X2 != X3
            & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3)
            & r2_hidden(X3,sK2)
            & r2_hidden(X2,sK2) )
        | ~ v2_funct_1(sK3) )
      & ( ! [X5,X4] :
            ( X4 = X5
            | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
            | ~ r2_hidden(X5,sK2)
            | ~ r2_hidden(X4,sK2) )
        | v2_funct_1(sK3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v1_funct_2(sK3,sK2,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( ( sK4 != sK5
        & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
        & r2_hidden(sK5,sK2)
        & r2_hidden(sK4,sK2) )
      | ~ v2_funct_1(sK3) )
    & ( ! [X4,X5] :
          ( X4 = X5
          | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
          | ~ r2_hidden(X5,sK2)
          | ~ r2_hidden(X4,sK2) )
      | v2_funct_1(sK3) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK3,sK2,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f38,f40,f39])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK0(X0) != sK1(X0)
        & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
        & r2_hidden(sK1(X0),k1_relat_1(X0))
        & r2_hidden(sK0(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK0(X0) != sK1(X0)
            & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
            & r2_hidden(sK1(X0),k1_relat_1(X0))
            & r2_hidden(sK0(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f34])).

fof(f55,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK0(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f57,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f25])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f68,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK2)
      | v2_funct_1(sK3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f58,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | sK0(X0) != sK1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK1(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f67,plain,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,
    ( sK4 != sK5
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f54,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2605,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2611,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3952,plain,
    ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2605,c_2611])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2612,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4315,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3952,c_2612])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4759,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4315,c_30])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2615,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4764,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4759,c_2615])).

cnf(c_15,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_395,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_27])).

cnf(c_396,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_2600,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_396])).

cnf(c_28,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_50,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_52,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_50])).

cnf(c_2924,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3003,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | r1_tarski(sK3,k2_zfmisc_1(sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_2924])).

cnf(c_3004,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(sK2,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3003])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_214,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_215,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_214])).

cnf(c_271,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_215])).

cnf(c_2879,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_271])).

cnf(c_3078,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK2,sK2))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK2))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2879])).

cnf(c_3080,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK2,sK2)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK2,sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3078])).

cnf(c_11,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3355,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3356,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3355])).

cnf(c_3465,plain,
    ( v2_funct_1(sK3) = iProver_top
    | r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2600,c_28,c_30,c_52,c_3004,c_3080,c_3356])).

cnf(c_3466,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3465])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_268,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_215])).

cnf(c_2604,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_268])).

cnf(c_3588,plain,
    ( r2_hidden(sK0(sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3466,c_2604])).

cnf(c_5096,plain,
    ( r2_hidden(sK0(sK3),sK2) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4764,c_3588])).

cnf(c_6113,plain,
    ( r2_hidden(sK0(sK3),X0) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5096,c_2604])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_82,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1955,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_4667,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,X1)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1955])).

cnf(c_7205,plain,
    ( r1_tarski(sK2,X0)
    | ~ r1_tarski(k1_xboole_0,X0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4667])).

cnf(c_7209,plain,
    ( sK2 != k1_xboole_0
    | r1_tarski(sK2,X0) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7205])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_421,plain,
    ( v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_27])).

cnf(c_422,plain,
    ( v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_2598,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_422])).

cnf(c_56,plain,
    ( k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_58,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_3472,plain,
    ( v2_funct_1(sK3) = iProver_top
    | k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2598,c_28,c_30,c_58,c_3004,c_3080,c_3356])).

cnf(c_3473,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3472])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_366,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
    | sK2 != X2
    | sK2 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_367,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ r2_hidden(X0,sK2)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_371,plain,
    ( ~ r2_hidden(X0,sK2)
    | ~ v2_funct_1(sK3)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_367,c_27,c_25])).

cnf(c_1951,plain,
    ( ~ v2_funct_1(sK3)
    | sP1_iProver_split
    | k1_xboole_0 = sK2 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_371])).

cnf(c_2601,plain,
    ( k1_xboole_0 = sK2
    | v2_funct_1(sK3) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1951])).

cnf(c_3478,plain,
    ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sK2 = k1_xboole_0
    | sP1_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_3473,c_2601])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2607,plain,
    ( r2_hidden(sK4,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1950,plain,
    ( ~ r2_hidden(X0,sK2)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_371])).

cnf(c_2602,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | r2_hidden(X0,sK2) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1950])).

cnf(c_3117,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | v2_funct_1(sK3) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2607,c_2602])).

cnf(c_3479,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3473,c_3117])).

cnf(c_4865,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3478,c_3479])).

cnf(c_21,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2609,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3482,plain,
    ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_3473,c_2609])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(X1,sK2)
    | v2_funct_1(sK3)
    | X1 = X0
    | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2606,plain,
    ( X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
    | r2_hidden(X1,sK2) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4181,plain,
    ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
    | sK1(sK3) = X0
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(sK1(sK3),sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3482,c_2606])).

cnf(c_4300,plain,
    ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
    | sK1(sK3) = sK0(sK3)
    | r2_hidden(sK1(sK3),sK2) != iProver_top
    | r2_hidden(sK0(sK3),sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4181])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK1(X0) != sK0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_434,plain,
    ( v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK1(X0) != sK0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_435,plain,
    ( v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK1(sK3) != sK0(sK3) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_561,plain,
    ( ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
    | sK1(sK3) != sK0(sK3) ),
    inference(resolution,[status(thm)],[c_435,c_21])).

cnf(c_14,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_408,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_27])).

cnf(c_409,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_2599,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_409])).

cnf(c_3589,plain,
    ( r2_hidden(sK1(sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2599,c_2604])).

cnf(c_5219,plain,
    ( v2_funct_1(sK3) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | r2_hidden(sK1(sK3),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3589,c_30,c_3004,c_3080,c_3356])).

cnf(c_5220,plain,
    ( r2_hidden(sK1(sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_5219])).

cnf(c_5229,plain,
    ( r2_hidden(sK1(sK3),sK2) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4764,c_5220])).

cnf(c_5241,plain,
    ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4300,c_25,c_561,c_3003,c_3078,c_3355,c_5096,c_5229])).

cnf(c_5251,plain,
    ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_5241,c_2609])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2608,plain,
    ( r2_hidden(sK5,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3116,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
    | v2_funct_1(sK3) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2608,c_2602])).

cnf(c_3480,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3473,c_3116])).

cnf(c_5405,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sP1_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_5251,c_3480])).

cnf(c_6000,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3478,c_5405])).

cnf(c_7672,plain,
    ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sK2 = k1_xboole_0
    | sK5 = sK4 ),
    inference(superposition,[status(thm)],[c_4865,c_6000])).

cnf(c_20,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | sK4 != sK5 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_664,plain,
    ( ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_422,c_20])).

cnf(c_8374,plain,
    ( sK2 = k1_xboole_0
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7672,c_25,c_664,c_3003,c_3078,c_3355])).

cnf(c_8375,plain,
    ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_8374])).

cnf(c_8383,plain,
    ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
    | sK1(sK3) = X0
    | sK2 = k1_xboole_0
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(sK1(sK3),sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_8375,c_2606])).

cnf(c_8510,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | sK2 = k1_xboole_0
    | sK1(sK3) = X0
    | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8383,c_5229])).

cnf(c_8511,plain,
    ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
    | sK1(sK3) = X0
    | sK2 = k1_xboole_0
    | r2_hidden(X0,sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_8510])).

cnf(c_8523,plain,
    ( sK1(sK3) = sK0(sK3)
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(sK3),sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_8511])).

cnf(c_59,plain,
    ( sK1(X0) != sK0(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_61,plain,
    ( sK1(sK3) != sK0(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_59])).

cnf(c_8534,plain,
    ( sK2 = k1_xboole_0
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8523,c_28,c_30,c_61,c_3004,c_3080,c_3356,c_5096])).

cnf(c_9076,plain,
    ( r2_hidden(sK0(sK3),X0) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6113,c_82,c_7209,c_8534])).

cnf(c_8541,plain,
    ( sK2 = k1_xboole_0
    | sP1_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_8534,c_2601])).

cnf(c_6965,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK1(sK3))) = sK1(sK3)
    | v2_funct_1(sK3) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_5229,c_2602])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_447,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | X2 = X0
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_448,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
    inference(unflattening,[status(thm)],[c_447])).

cnf(c_1949,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_448])).

cnf(c_2595,plain,
    ( v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1949])).

cnf(c_7054,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK1(sK3))) = sK1(sK3)
    | v1_relat_1(sK3) != iProver_top
    | sP1_iProver_split != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_6965,c_2595])).

cnf(c_7096,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK1(sK3))) = sK1(sK3)
    | sP1_iProver_split != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7054,c_30,c_3004,c_3080,c_3356])).

cnf(c_8689,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK1(sK3))) = sK1(sK3)
    | sK2 = k1_xboole_0
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_8541,c_7096])).

cnf(c_573,plain,
    ( ~ v1_relat_1(sK3)
    | sK1(sK3) != sK0(sK3)
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_435,c_20])).

cnf(c_755,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_409,c_20])).

cnf(c_756,plain,
    ( sK5 != sK4
    | r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_755])).

cnf(c_846,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_396,c_20])).

cnf(c_847,plain,
    ( sK5 != sK4
    | r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_846])).

cnf(c_1948,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_448])).

cnf(c_2596,plain,
    ( X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1948])).

cnf(c_8382,plain,
    ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
    | sK1(sK3) = X0
    | sK2 = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK1(sK3),k1_relat_1(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_8375,c_2596])).

cnf(c_8543,plain,
    ( sK2 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_8534,c_2595])).

cnf(c_8832,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | sK2 = k1_xboole_0
    | sK1(sK3) = X0
    | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8382,c_30,c_3004,c_3080,c_3356,c_8543])).

cnf(c_8833,plain,
    ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
    | sK1(sK3) = X0
    | sK2 = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK1(sK3),k1_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8832])).

cnf(c_8845,plain,
    ( sK1(sK3) = sK0(sK3)
    | sK2 = k1_xboole_0
    | r2_hidden(sK1(sK3),k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK0(sK3),k1_relat_1(sK3)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_8833])).

cnf(c_5407,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
    | v2_funct_1(sK3) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_5251,c_3116])).

cnf(c_8540,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
    | sK2 = k1_xboole_0
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_8534,c_5407])).

cnf(c_8568,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
    | sK2 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8540,c_8541])).

cnf(c_8542,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | sK2 = k1_xboole_0
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_8534,c_3117])).

cnf(c_8560,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | sK2 = k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_8541,c_8542])).

cnf(c_9333,plain,
    ( sK2 = k1_xboole_0
    | sK5 = sK4 ),
    inference(superposition,[status(thm)],[c_8568,c_8560])).

cnf(c_9405,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8689,c_25,c_30,c_573,c_756,c_847,c_3003,c_3004,c_3078,c_3080,c_3355,c_3356,c_8845,c_9333])).

cnf(c_9434,plain,
    ( r2_hidden(sK5,k1_xboole_0) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9405,c_2608])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2618,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2614,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4454,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2618,c_2614])).

cnf(c_9744,plain,
    ( m1_subset_1(sK5,X0) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9434,c_4454])).

cnf(c_10566,plain,
    ( k1_relset_1(X0,X1,sK5) = k1_relat_1(sK5)
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9744,c_2611])).

cnf(c_11204,plain,
    ( k1_relset_1(X0,X1,sK5) = k1_relat_1(sK5)
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3)) ),
    inference(superposition,[status(thm)],[c_3473,c_10566])).

cnf(c_11545,plain,
    ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | m1_subset_1(k1_relat_1(sK5),k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_11204,c_2612])).

cnf(c_628,plain,
    ( r2_hidden(sK4,sK2)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3)) ),
    inference(resolution,[status(thm)],[c_422,c_23])).

cnf(c_640,plain,
    ( r2_hidden(sK5,sK2)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3)) ),
    inference(resolution,[status(thm)],[c_422,c_22])).

cnf(c_5426,plain,
    ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4)
    | sK5 = X0
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(sK5,sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5251,c_2606])).

cnf(c_5461,plain,
    ( sK5 = sK4
    | r2_hidden(sK5,sK2) != iProver_top
    | r2_hidden(sK4,sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5426])).

cnf(c_5470,plain,
    ( ~ r2_hidden(sK5,sK2)
    | ~ r2_hidden(sK4,sK2)
    | v2_funct_1(sK3)
    | sK5 = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5461])).

cnf(c_9435,plain,
    ( r2_hidden(sK4,k1_xboole_0) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9405,c_2607])).

cnf(c_9758,plain,
    ( m1_subset_1(sK4,X0) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9435,c_4454])).

cnf(c_10619,plain,
    ( r1_tarski(sK4,X0) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9758,c_2615])).

cnf(c_10564,plain,
    ( r1_tarski(sK5,X0) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9744,c_2615])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2621,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_10938,plain,
    ( sK5 = X0
    | r1_tarski(X0,sK5) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10564,c_2621])).

cnf(c_11993,plain,
    ( sK5 = sK4
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10619,c_10938])).

cnf(c_12008,plain,
    ( ~ v2_funct_1(sK3)
    | sK5 = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11993])).

cnf(c_13626,plain,
    ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11545,c_25,c_628,c_640,c_664,c_3003,c_3078,c_3355,c_5470,c_12008])).

cnf(c_9433,plain,
    ( X0 = X1
    | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0)
    | r2_hidden(X1,k1_xboole_0) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9405,c_2606])).

cnf(c_13667,plain,
    ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
    | sK1(sK3) = X0
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(sK1(sK3),k1_xboole_0) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_13626,c_9433])).

cnf(c_1981,plain,
    ( v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1949])).

cnf(c_9414,plain,
    ( r2_hidden(sK1(sK3),k1_xboole_0) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9405,c_5229])).

cnf(c_13669,plain,
    ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
    | sK1(sK3) = X0
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK1(sK3),k1_relat_1(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_13626,c_2596])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2620,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5228,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2620,c_5220])).

cnf(c_13719,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | sK1(sK3) = X0
    | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
    | sP0_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13669,c_30,c_756,c_3004,c_3080,c_3356,c_5228,c_11993])).

cnf(c_13720,plain,
    ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
    | sK1(sK3) = X0
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(renaming,[status(thm)],[c_13719])).

cnf(c_13730,plain,
    ( sK1(sK3) = sK0(sK3)
    | r2_hidden(sK0(sK3),k1_relat_1(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_13720])).

cnf(c_13813,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | sK1(sK3) = X0
    | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13667,c_25,c_30,c_573,c_847,c_1981,c_3003,c_3004,c_3078,c_3080,c_3355,c_3356,c_9414,c_11993,c_13730])).

cnf(c_13814,plain,
    ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
    | sK1(sK3) = X0
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_13813])).

cnf(c_13819,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | sK1(sK3) = X0
    | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13814,c_25,c_30,c_573,c_847,c_1981,c_3003,c_3004,c_3078,c_3080,c_3355,c_3356,c_9414,c_11993,c_13667,c_13730])).

cnf(c_13820,plain,
    ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
    | sK1(sK3) = X0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_13819])).

cnf(c_13829,plain,
    ( sK1(sK3) = sK0(sK3)
    | r2_hidden(sK0(sK3),k1_xboole_0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_13820])).

cnf(c_13836,plain,
    ( r2_hidden(sK0(sK3),k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13829,c_28,c_25,c_30,c_61,c_573,c_847,c_1981,c_3003,c_3004,c_3078,c_3080,c_3355,c_3356,c_11993,c_13730])).

cnf(c_13841,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_9076,c_13836])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13841,c_13730,c_11993,c_3356,c_3355,c_3080,c_3078,c_3004,c_3003,c_1981,c_847,c_573,c_30,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n014.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 10:11:52 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 3.06/0.91  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/0.91  
% 3.06/0.91  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.06/0.91  
% 3.06/0.91  ------  iProver source info
% 3.06/0.91  
% 3.06/0.91  git: date: 2020-06-30 10:37:57 +0100
% 3.06/0.91  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.06/0.91  git: non_committed_changes: false
% 3.06/0.91  git: last_make_outside_of_git: false
% 3.06/0.91  
% 3.06/0.91  ------ 
% 3.06/0.91  
% 3.06/0.91  ------ Input Options
% 3.06/0.91  
% 3.06/0.91  --out_options                           all
% 3.06/0.91  --tptp_safe_out                         true
% 3.06/0.91  --problem_path                          ""
% 3.06/0.91  --include_path                          ""
% 3.06/0.91  --clausifier                            res/vclausify_rel
% 3.06/0.91  --clausifier_options                    --mode clausify
% 3.06/0.91  --stdin                                 false
% 3.06/0.91  --stats_out                             all
% 3.06/0.91  
% 3.06/0.91  ------ General Options
% 3.06/0.91  
% 3.06/0.91  --fof                                   false
% 3.06/0.91  --time_out_real                         305.
% 3.06/0.91  --time_out_virtual                      -1.
% 3.06/0.91  --symbol_type_check                     false
% 3.06/0.91  --clausify_out                          false
% 3.06/0.91  --sig_cnt_out                           false
% 3.06/0.91  --trig_cnt_out                          false
% 3.06/0.91  --trig_cnt_out_tolerance                1.
% 3.06/0.91  --trig_cnt_out_sk_spl                   false
% 3.06/0.91  --abstr_cl_out                          false
% 3.06/0.91  
% 3.06/0.91  ------ Global Options
% 3.06/0.91  
% 3.06/0.91  --schedule                              default
% 3.06/0.91  --add_important_lit                     false
% 3.06/0.91  --prop_solver_per_cl                    1000
% 3.06/0.91  --min_unsat_core                        false
% 3.06/0.91  --soft_assumptions                      false
% 3.06/0.91  --soft_lemma_size                       3
% 3.06/0.91  --prop_impl_unit_size                   0
% 3.06/0.91  --prop_impl_unit                        []
% 3.06/0.91  --share_sel_clauses                     true
% 3.06/0.91  --reset_solvers                         false
% 3.06/0.91  --bc_imp_inh                            [conj_cone]
% 3.06/0.91  --conj_cone_tolerance                   3.
% 3.06/0.91  --extra_neg_conj                        none
% 3.06/0.91  --large_theory_mode                     true
% 3.06/0.91  --prolific_symb_bound                   200
% 3.06/0.91  --lt_threshold                          2000
% 3.06/0.91  --clause_weak_htbl                      true
% 3.06/0.91  --gc_record_bc_elim                     false
% 3.06/0.91  
% 3.06/0.91  ------ Preprocessing Options
% 3.06/0.91  
% 3.06/0.91  --preprocessing_flag                    true
% 3.06/0.91  --time_out_prep_mult                    0.1
% 3.06/0.91  --splitting_mode                        input
% 3.06/0.91  --splitting_grd                         true
% 3.06/0.91  --splitting_cvd                         false
% 3.06/0.91  --splitting_cvd_svl                     false
% 3.06/0.91  --splitting_nvd                         32
% 3.06/0.91  --sub_typing                            true
% 3.06/0.91  --prep_gs_sim                           true
% 3.06/0.91  --prep_unflatten                        true
% 3.06/0.91  --prep_res_sim                          true
% 3.06/0.91  --prep_upred                            true
% 3.06/0.91  --prep_sem_filter                       exhaustive
% 3.06/0.91  --prep_sem_filter_out                   false
% 3.06/0.91  --pred_elim                             true
% 3.06/0.91  --res_sim_input                         true
% 3.06/0.91  --eq_ax_congr_red                       true
% 3.06/0.91  --pure_diseq_elim                       true
% 3.06/0.91  --brand_transform                       false
% 3.06/0.91  --non_eq_to_eq                          false
% 3.06/0.91  --prep_def_merge                        true
% 3.06/0.91  --prep_def_merge_prop_impl              false
% 3.06/0.91  --prep_def_merge_mbd                    true
% 3.06/0.91  --prep_def_merge_tr_red                 false
% 3.06/0.91  --prep_def_merge_tr_cl                  false
% 3.06/0.91  --smt_preprocessing                     true
% 3.06/0.91  --smt_ac_axioms                         fast
% 3.06/0.91  --preprocessed_out                      false
% 3.06/0.91  --preprocessed_stats                    false
% 3.06/0.91  
% 3.06/0.91  ------ Abstraction refinement Options
% 3.06/0.91  
% 3.06/0.91  --abstr_ref                             []
% 3.06/0.91  --abstr_ref_prep                        false
% 3.06/0.91  --abstr_ref_until_sat                   false
% 3.06/0.91  --abstr_ref_sig_restrict                funpre
% 3.06/0.91  --abstr_ref_af_restrict_to_split_sk     false
% 3.06/0.91  --abstr_ref_under                       []
% 3.06/0.91  
% 3.06/0.91  ------ SAT Options
% 3.06/0.91  
% 3.06/0.91  --sat_mode                              false
% 3.06/0.91  --sat_fm_restart_options                ""
% 3.06/0.91  --sat_gr_def                            false
% 3.06/0.91  --sat_epr_types                         true
% 3.06/0.91  --sat_non_cyclic_types                  false
% 3.06/0.91  --sat_finite_models                     false
% 3.06/0.91  --sat_fm_lemmas                         false
% 3.06/0.91  --sat_fm_prep                           false
% 3.06/0.91  --sat_fm_uc_incr                        true
% 3.06/0.91  --sat_out_model                         small
% 3.06/0.91  --sat_out_clauses                       false
% 3.06/0.91  
% 3.06/0.91  ------ QBF Options
% 3.06/0.91  
% 3.06/0.91  --qbf_mode                              false
% 3.06/0.91  --qbf_elim_univ                         false
% 3.06/0.91  --qbf_dom_inst                          none
% 3.06/0.91  --qbf_dom_pre_inst                      false
% 3.06/0.91  --qbf_sk_in                             false
% 3.06/0.91  --qbf_pred_elim                         true
% 3.06/0.91  --qbf_split                             512
% 3.06/0.91  
% 3.06/0.91  ------ BMC1 Options
% 3.06/0.91  
% 3.06/0.91  --bmc1_incremental                      false
% 3.06/0.91  --bmc1_axioms                           reachable_all
% 3.06/0.91  --bmc1_min_bound                        0
% 3.06/0.91  --bmc1_max_bound                        -1
% 3.06/0.91  --bmc1_max_bound_default                -1
% 3.06/0.91  --bmc1_symbol_reachability              true
% 3.06/0.91  --bmc1_property_lemmas                  false
% 3.06/0.91  --bmc1_k_induction                      false
% 3.06/0.91  --bmc1_non_equiv_states                 false
% 3.06/0.91  --bmc1_deadlock                         false
% 3.06/0.91  --bmc1_ucm                              false
% 3.06/0.91  --bmc1_add_unsat_core                   none
% 3.06/0.91  --bmc1_unsat_core_children              false
% 3.06/0.91  --bmc1_unsat_core_extrapolate_axioms    false
% 3.06/0.91  --bmc1_out_stat                         full
% 3.06/0.91  --bmc1_ground_init                      false
% 3.06/0.91  --bmc1_pre_inst_next_state              false
% 3.06/0.91  --bmc1_pre_inst_state                   false
% 3.06/0.91  --bmc1_pre_inst_reach_state             false
% 3.06/0.91  --bmc1_out_unsat_core                   false
% 3.06/0.91  --bmc1_aig_witness_out                  false
% 3.06/0.91  --bmc1_verbose                          false
% 3.06/0.91  --bmc1_dump_clauses_tptp                false
% 3.06/0.91  --bmc1_dump_unsat_core_tptp             false
% 3.06/0.91  --bmc1_dump_file                        -
% 3.06/0.91  --bmc1_ucm_expand_uc_limit              128
% 3.06/0.91  --bmc1_ucm_n_expand_iterations          6
% 3.06/0.91  --bmc1_ucm_extend_mode                  1
% 3.06/0.91  --bmc1_ucm_init_mode                    2
% 3.06/0.91  --bmc1_ucm_cone_mode                    none
% 3.06/0.91  --bmc1_ucm_reduced_relation_type        0
% 3.06/0.91  --bmc1_ucm_relax_model                  4
% 3.06/0.91  --bmc1_ucm_full_tr_after_sat            true
% 3.06/0.91  --bmc1_ucm_expand_neg_assumptions       false
% 3.06/0.91  --bmc1_ucm_layered_model                none
% 3.06/0.92  --bmc1_ucm_max_lemma_size               10
% 3.06/0.92  
% 3.06/0.92  ------ AIG Options
% 3.06/0.92  
% 3.06/0.92  --aig_mode                              false
% 3.06/0.92  
% 3.06/0.92  ------ Instantiation Options
% 3.06/0.92  
% 3.06/0.92  --instantiation_flag                    true
% 3.06/0.92  --inst_sos_flag                         false
% 3.06/0.92  --inst_sos_phase                        true
% 3.06/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.06/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.06/0.92  --inst_lit_sel_side                     num_symb
% 3.06/0.92  --inst_solver_per_active                1400
% 3.06/0.92  --inst_solver_calls_frac                1.
% 3.06/0.92  --inst_passive_queue_type               priority_queues
% 3.06/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.06/0.92  --inst_passive_queues_freq              [25;2]
% 3.06/0.92  --inst_dismatching                      true
% 3.06/0.92  --inst_eager_unprocessed_to_passive     true
% 3.06/0.92  --inst_prop_sim_given                   true
% 3.06/0.92  --inst_prop_sim_new                     false
% 3.06/0.92  --inst_subs_new                         false
% 3.06/0.92  --inst_eq_res_simp                      false
% 3.06/0.92  --inst_subs_given                       false
% 3.06/0.92  --inst_orphan_elimination               true
% 3.06/0.92  --inst_learning_loop_flag               true
% 3.06/0.92  --inst_learning_start                   3000
% 3.06/0.92  --inst_learning_factor                  2
% 3.06/0.92  --inst_start_prop_sim_after_learn       3
% 3.06/0.92  --inst_sel_renew                        solver
% 3.06/0.92  --inst_lit_activity_flag                true
% 3.06/0.92  --inst_restr_to_given                   false
% 3.06/0.92  --inst_activity_threshold               500
% 3.06/0.92  --inst_out_proof                        true
% 3.06/0.92  
% 3.06/0.92  ------ Resolution Options
% 3.06/0.92  
% 3.06/0.92  --resolution_flag                       true
% 3.06/0.92  --res_lit_sel                           adaptive
% 3.06/0.92  --res_lit_sel_side                      none
% 3.06/0.92  --res_ordering                          kbo
% 3.06/0.92  --res_to_prop_solver                    active
% 3.06/0.92  --res_prop_simpl_new                    false
% 3.06/0.92  --res_prop_simpl_given                  true
% 3.06/0.92  --res_passive_queue_type                priority_queues
% 3.06/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.06/0.92  --res_passive_queues_freq               [15;5]
% 3.06/0.92  --res_forward_subs                      full
% 3.06/0.92  --res_backward_subs                     full
% 3.06/0.92  --res_forward_subs_resolution           true
% 3.06/0.92  --res_backward_subs_resolution          true
% 3.06/0.92  --res_orphan_elimination                true
% 3.06/0.92  --res_time_limit                        2.
% 3.06/0.92  --res_out_proof                         true
% 3.06/0.92  
% 3.06/0.92  ------ Superposition Options
% 3.06/0.92  
% 3.06/0.92  --superposition_flag                    true
% 3.06/0.92  --sup_passive_queue_type                priority_queues
% 3.06/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.06/0.92  --sup_passive_queues_freq               [8;1;4]
% 3.06/0.92  --demod_completeness_check              fast
% 3.06/0.92  --demod_use_ground                      true
% 3.06/0.92  --sup_to_prop_solver                    passive
% 3.06/0.92  --sup_prop_simpl_new                    true
% 3.06/0.92  --sup_prop_simpl_given                  true
% 3.06/0.92  --sup_fun_splitting                     false
% 3.06/0.92  --sup_smt_interval                      50000
% 3.06/0.92  
% 3.06/0.92  ------ Superposition Simplification Setup
% 3.06/0.92  
% 3.06/0.92  --sup_indices_passive                   []
% 3.06/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 3.06/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/0.92  --sup_full_bw                           [BwDemod]
% 3.06/0.92  --sup_immed_triv                        [TrivRules]
% 3.06/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/0.92  --sup_immed_bw_main                     []
% 3.06/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 3.06/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/0.92  
% 3.06/0.92  ------ Combination Options
% 3.06/0.92  
% 3.06/0.92  --comb_res_mult                         3
% 3.06/0.92  --comb_sup_mult                         2
% 3.06/0.92  --comb_inst_mult                        10
% 3.06/0.92  
% 3.06/0.92  ------ Debug Options
% 3.06/0.92  
% 3.06/0.92  --dbg_backtrace                         false
% 3.06/0.92  --dbg_dump_prop_clauses                 false
% 3.06/0.92  --dbg_dump_prop_clauses_file            -
% 3.06/0.92  --dbg_out_stat                          false
% 3.06/0.92  ------ Parsing...
% 3.06/0.92  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.06/0.92  
% 3.06/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.06/0.92  
% 3.06/0.92  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.06/0.92  
% 3.06/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.06/0.92  ------ Proving...
% 3.06/0.92  ------ Problem Properties 
% 3.06/0.92  
% 3.06/0.92  
% 3.06/0.92  clauses                                 27
% 3.06/0.92  conjectures                             6
% 3.06/0.92  EPR                                     11
% 3.06/0.92  Horn                                    22
% 3.06/0.92  unary                                   5
% 3.06/0.92  binary                                  9
% 3.06/0.92  lits                                    66
% 3.06/0.92  lits eq                                 12
% 3.06/0.92  fd_pure                                 0
% 3.06/0.92  fd_pseudo                               0
% 3.06/0.92  fd_cond                                 0
% 3.06/0.92  fd_pseudo_cond                          3
% 3.06/0.92  AC symbols                              0
% 3.06/0.92  
% 3.06/0.92  ------ Schedule dynamic 5 is on 
% 3.06/0.92  
% 3.06/0.92  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.06/0.92  
% 3.06/0.92  
% 3.06/0.92  ------ 
% 3.06/0.92  Current options:
% 3.06/0.92  ------ 
% 3.06/0.92  
% 3.06/0.92  ------ Input Options
% 3.06/0.92  
% 3.06/0.92  --out_options                           all
% 3.06/0.92  --tptp_safe_out                         true
% 3.06/0.92  --problem_path                          ""
% 3.06/0.92  --include_path                          ""
% 3.06/0.92  --clausifier                            res/vclausify_rel
% 3.06/0.92  --clausifier_options                    --mode clausify
% 3.06/0.92  --stdin                                 false
% 3.06/0.92  --stats_out                             all
% 3.06/0.92  
% 3.06/0.92  ------ General Options
% 3.06/0.92  
% 3.06/0.92  --fof                                   false
% 3.06/0.92  --time_out_real                         305.
% 3.06/0.92  --time_out_virtual                      -1.
% 3.06/0.92  --symbol_type_check                     false
% 3.06/0.92  --clausify_out                          false
% 3.06/0.92  --sig_cnt_out                           false
% 3.06/0.92  --trig_cnt_out                          false
% 3.06/0.92  --trig_cnt_out_tolerance                1.
% 3.06/0.92  --trig_cnt_out_sk_spl                   false
% 3.06/0.92  --abstr_cl_out                          false
% 3.06/0.92  
% 3.06/0.92  ------ Global Options
% 3.06/0.92  
% 3.06/0.92  --schedule                              default
% 3.06/0.92  --add_important_lit                     false
% 3.06/0.92  --prop_solver_per_cl                    1000
% 3.06/0.92  --min_unsat_core                        false
% 3.06/0.92  --soft_assumptions                      false
% 3.06/0.92  --soft_lemma_size                       3
% 3.06/0.92  --prop_impl_unit_size                   0
% 3.06/0.92  --prop_impl_unit                        []
% 3.06/0.92  --share_sel_clauses                     true
% 3.06/0.92  --reset_solvers                         false
% 3.06/0.92  --bc_imp_inh                            [conj_cone]
% 3.06/0.92  --conj_cone_tolerance                   3.
% 3.06/0.92  --extra_neg_conj                        none
% 3.06/0.92  --large_theory_mode                     true
% 3.06/0.92  --prolific_symb_bound                   200
% 3.06/0.92  --lt_threshold                          2000
% 3.06/0.92  --clause_weak_htbl                      true
% 3.06/0.92  --gc_record_bc_elim                     false
% 3.06/0.92  
% 3.06/0.92  ------ Preprocessing Options
% 3.06/0.92  
% 3.06/0.92  --preprocessing_flag                    true
% 3.06/0.92  --time_out_prep_mult                    0.1
% 3.06/0.92  --splitting_mode                        input
% 3.06/0.92  --splitting_grd                         true
% 3.06/0.92  --splitting_cvd                         false
% 3.06/0.92  --splitting_cvd_svl                     false
% 3.06/0.92  --splitting_nvd                         32
% 3.06/0.92  --sub_typing                            true
% 3.06/0.92  --prep_gs_sim                           true
% 3.06/0.92  --prep_unflatten                        true
% 3.06/0.92  --prep_res_sim                          true
% 3.06/0.92  --prep_upred                            true
% 3.06/0.92  --prep_sem_filter                       exhaustive
% 3.06/0.92  --prep_sem_filter_out                   false
% 3.06/0.92  --pred_elim                             true
% 3.06/0.92  --res_sim_input                         true
% 3.06/0.92  --eq_ax_congr_red                       true
% 3.06/0.92  --pure_diseq_elim                       true
% 3.06/0.92  --brand_transform                       false
% 3.06/0.92  --non_eq_to_eq                          false
% 3.06/0.92  --prep_def_merge                        true
% 3.06/0.92  --prep_def_merge_prop_impl              false
% 3.06/0.92  --prep_def_merge_mbd                    true
% 3.06/0.92  --prep_def_merge_tr_red                 false
% 3.06/0.92  --prep_def_merge_tr_cl                  false
% 3.06/0.92  --smt_preprocessing                     true
% 3.06/0.92  --smt_ac_axioms                         fast
% 3.06/0.92  --preprocessed_out                      false
% 3.06/0.92  --preprocessed_stats                    false
% 3.06/0.92  
% 3.06/0.92  ------ Abstraction refinement Options
% 3.06/0.92  
% 3.06/0.92  --abstr_ref                             []
% 3.06/0.92  --abstr_ref_prep                        false
% 3.06/0.92  --abstr_ref_until_sat                   false
% 3.06/0.92  --abstr_ref_sig_restrict                funpre
% 3.06/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 3.06/0.92  --abstr_ref_under                       []
% 3.06/0.92  
% 3.06/0.92  ------ SAT Options
% 3.06/0.92  
% 3.06/0.92  --sat_mode                              false
% 3.06/0.92  --sat_fm_restart_options                ""
% 3.06/0.92  --sat_gr_def                            false
% 3.06/0.92  --sat_epr_types                         true
% 3.06/0.92  --sat_non_cyclic_types                  false
% 3.06/0.92  --sat_finite_models                     false
% 3.06/0.92  --sat_fm_lemmas                         false
% 3.06/0.92  --sat_fm_prep                           false
% 3.06/0.92  --sat_fm_uc_incr                        true
% 3.06/0.92  --sat_out_model                         small
% 3.06/0.92  --sat_out_clauses                       false
% 3.06/0.92  
% 3.06/0.92  ------ QBF Options
% 3.06/0.92  
% 3.06/0.92  --qbf_mode                              false
% 3.06/0.92  --qbf_elim_univ                         false
% 3.06/0.92  --qbf_dom_inst                          none
% 3.06/0.92  --qbf_dom_pre_inst                      false
% 3.06/0.92  --qbf_sk_in                             false
% 3.06/0.92  --qbf_pred_elim                         true
% 3.06/0.92  --qbf_split                             512
% 3.06/0.92  
% 3.06/0.92  ------ BMC1 Options
% 3.06/0.92  
% 3.06/0.92  --bmc1_incremental                      false
% 3.06/0.92  --bmc1_axioms                           reachable_all
% 3.06/0.92  --bmc1_min_bound                        0
% 3.06/0.92  --bmc1_max_bound                        -1
% 3.06/0.92  --bmc1_max_bound_default                -1
% 3.06/0.92  --bmc1_symbol_reachability              true
% 3.06/0.92  --bmc1_property_lemmas                  false
% 3.06/0.92  --bmc1_k_induction                      false
% 3.06/0.92  --bmc1_non_equiv_states                 false
% 3.06/0.92  --bmc1_deadlock                         false
% 3.06/0.92  --bmc1_ucm                              false
% 3.06/0.92  --bmc1_add_unsat_core                   none
% 3.06/0.92  --bmc1_unsat_core_children              false
% 3.06/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 3.06/0.92  --bmc1_out_stat                         full
% 3.06/0.92  --bmc1_ground_init                      false
% 3.06/0.92  --bmc1_pre_inst_next_state              false
% 3.06/0.92  --bmc1_pre_inst_state                   false
% 3.06/0.92  --bmc1_pre_inst_reach_state             false
% 3.06/0.92  --bmc1_out_unsat_core                   false
% 3.06/0.92  --bmc1_aig_witness_out                  false
% 3.06/0.92  --bmc1_verbose                          false
% 3.06/0.92  --bmc1_dump_clauses_tptp                false
% 3.06/0.92  --bmc1_dump_unsat_core_tptp             false
% 3.06/0.92  --bmc1_dump_file                        -
% 3.06/0.92  --bmc1_ucm_expand_uc_limit              128
% 3.06/0.92  --bmc1_ucm_n_expand_iterations          6
% 3.06/0.92  --bmc1_ucm_extend_mode                  1
% 3.06/0.92  --bmc1_ucm_init_mode                    2
% 3.06/0.92  --bmc1_ucm_cone_mode                    none
% 3.06/0.92  --bmc1_ucm_reduced_relation_type        0
% 3.06/0.92  --bmc1_ucm_relax_model                  4
% 3.06/0.92  --bmc1_ucm_full_tr_after_sat            true
% 3.06/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 3.06/0.92  --bmc1_ucm_layered_model                none
% 3.06/0.92  --bmc1_ucm_max_lemma_size               10
% 3.06/0.92  
% 3.06/0.92  ------ AIG Options
% 3.06/0.92  
% 3.06/0.92  --aig_mode                              false
% 3.06/0.92  
% 3.06/0.92  ------ Instantiation Options
% 3.06/0.92  
% 3.06/0.92  --instantiation_flag                    true
% 3.06/0.92  --inst_sos_flag                         false
% 3.06/0.92  --inst_sos_phase                        true
% 3.06/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.06/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.06/0.92  --inst_lit_sel_side                     none
% 3.06/0.92  --inst_solver_per_active                1400
% 3.06/0.92  --inst_solver_calls_frac                1.
% 3.06/0.92  --inst_passive_queue_type               priority_queues
% 3.06/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.06/0.92  --inst_passive_queues_freq              [25;2]
% 3.06/0.92  --inst_dismatching                      true
% 3.06/0.92  --inst_eager_unprocessed_to_passive     true
% 3.06/0.92  --inst_prop_sim_given                   true
% 3.06/0.92  --inst_prop_sim_new                     false
% 3.06/0.92  --inst_subs_new                         false
% 3.06/0.92  --inst_eq_res_simp                      false
% 3.06/0.92  --inst_subs_given                       false
% 3.06/0.92  --inst_orphan_elimination               true
% 3.06/0.92  --inst_learning_loop_flag               true
% 3.06/0.92  --inst_learning_start                   3000
% 3.06/0.92  --inst_learning_factor                  2
% 3.06/0.92  --inst_start_prop_sim_after_learn       3
% 3.06/0.92  --inst_sel_renew                        solver
% 3.06/0.92  --inst_lit_activity_flag                true
% 3.06/0.92  --inst_restr_to_given                   false
% 3.06/0.92  --inst_activity_threshold               500
% 3.06/0.92  --inst_out_proof                        true
% 3.06/0.92  
% 3.06/0.92  ------ Resolution Options
% 3.06/0.92  
% 3.06/0.92  --resolution_flag                       false
% 3.06/0.92  --res_lit_sel                           adaptive
% 3.06/0.92  --res_lit_sel_side                      none
% 3.06/0.92  --res_ordering                          kbo
% 3.06/0.92  --res_to_prop_solver                    active
% 3.06/0.92  --res_prop_simpl_new                    false
% 3.06/0.92  --res_prop_simpl_given                  true
% 3.06/0.92  --res_passive_queue_type                priority_queues
% 3.06/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.06/0.92  --res_passive_queues_freq               [15;5]
% 3.06/0.92  --res_forward_subs                      full
% 3.06/0.92  --res_backward_subs                     full
% 3.06/0.92  --res_forward_subs_resolution           true
% 3.06/0.92  --res_backward_subs_resolution          true
% 3.06/0.92  --res_orphan_elimination                true
% 3.06/0.92  --res_time_limit                        2.
% 3.06/0.92  --res_out_proof                         true
% 3.06/0.92  
% 3.06/0.92  ------ Superposition Options
% 3.06/0.92  
% 3.06/0.92  --superposition_flag                    true
% 3.06/0.92  --sup_passive_queue_type                priority_queues
% 3.06/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.06/0.92  --sup_passive_queues_freq               [8;1;4]
% 3.06/0.92  --demod_completeness_check              fast
% 3.06/0.92  --demod_use_ground                      true
% 3.06/0.92  --sup_to_prop_solver                    passive
% 3.06/0.92  --sup_prop_simpl_new                    true
% 3.06/0.92  --sup_prop_simpl_given                  true
% 3.06/0.92  --sup_fun_splitting                     false
% 3.06/0.92  --sup_smt_interval                      50000
% 3.06/0.92  
% 3.06/0.92  ------ Superposition Simplification Setup
% 3.06/0.92  
% 3.06/0.92  --sup_indices_passive                   []
% 3.06/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 3.06/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/0.92  --sup_full_bw                           [BwDemod]
% 3.06/0.92  --sup_immed_triv                        [TrivRules]
% 3.06/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/0.92  --sup_immed_bw_main                     []
% 3.06/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 3.06/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/0.92  
% 3.06/0.92  ------ Combination Options
% 3.06/0.92  
% 3.06/0.92  --comb_res_mult                         3
% 3.06/0.92  --comb_sup_mult                         2
% 3.06/0.92  --comb_inst_mult                        10
% 3.06/0.92  
% 3.06/0.92  ------ Debug Options
% 3.06/0.92  
% 3.06/0.92  --dbg_backtrace                         false
% 3.06/0.92  --dbg_dump_prop_clauses                 false
% 3.06/0.92  --dbg_dump_prop_clauses_file            -
% 3.06/0.92  --dbg_out_stat                          false
% 3.06/0.92  
% 3.06/0.92  
% 3.06/0.92  
% 3.06/0.92  
% 3.06/0.92  ------ Proving...
% 3.06/0.92  
% 3.06/0.92  
% 3.06/0.92  % SZS status Theorem for theBenchmark.p
% 3.06/0.92  
% 3.06/0.92  % SZS output start CNFRefutation for theBenchmark.p
% 3.06/0.92  
% 3.06/0.92  fof(f14,conjecture,(
% 3.06/0.92    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 3.06/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/0.92  
% 3.06/0.92  fof(f15,negated_conjecture,(
% 3.06/0.92    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 3.06/0.92    inference(negated_conjecture,[],[f14])).
% 3.06/0.92  
% 3.06/0.92  fof(f27,plain,(
% 3.06/0.92    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.06/0.92    inference(ennf_transformation,[],[f15])).
% 3.06/0.92  
% 3.06/0.92  fof(f28,plain,(
% 3.06/0.92    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.06/0.92    inference(flattening,[],[f27])).
% 3.06/0.92  
% 3.06/0.92  fof(f36,plain,(
% 3.06/0.92    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.06/0.92    inference(nnf_transformation,[],[f28])).
% 3.06/0.92  
% 3.06/0.92  fof(f37,plain,(
% 3.06/0.92    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.06/0.92    inference(flattening,[],[f36])).
% 3.06/0.92  
% 3.06/0.92  fof(f38,plain,(
% 3.06/0.92    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.06/0.92    inference(rectify,[],[f37])).
% 3.06/0.92  
% 3.06/0.92  fof(f40,plain,(
% 3.06/0.92    ( ! [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (sK4 != sK5 & k1_funct_1(X1,sK4) = k1_funct_1(X1,sK5) & r2_hidden(sK5,X0) & r2_hidden(sK4,X0))) )),
% 3.06/0.92    introduced(choice_axiom,[])).
% 3.06/0.92  
% 3.06/0.92  fof(f39,plain,(
% 3.06/0.92    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3) & r2_hidden(X3,sK2) & r2_hidden(X2,sK2)) | ~v2_funct_1(sK3)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 3.06/0.92    introduced(choice_axiom,[])).
% 3.06/0.92  
% 3.06/0.92  fof(f41,plain,(
% 3.06/0.92    ((sK4 != sK5 & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) & r2_hidden(sK5,sK2) & r2_hidden(sK4,sK2)) | ~v2_funct_1(sK3)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 3.06/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f38,f40,f39])).
% 3.06/0.92  
% 3.06/0.92  fof(f64,plain,(
% 3.06/0.92    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 3.06/0.92    inference(cnf_transformation,[],[f41])).
% 3.06/0.92  
% 3.06/0.92  fof(f12,axiom,(
% 3.06/0.92    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.06/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/0.92  
% 3.06/0.92  fof(f24,plain,(
% 3.06/0.92    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/0.92    inference(ennf_transformation,[],[f12])).
% 3.06/0.92  
% 3.06/0.92  fof(f60,plain,(
% 3.06/0.92    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/0.92    inference(cnf_transformation,[],[f24])).
% 3.06/0.92  
% 3.06/0.92  fof(f11,axiom,(
% 3.06/0.92    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.06/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/0.92  
% 3.06/0.92  fof(f23,plain,(
% 3.06/0.92    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/0.92    inference(ennf_transformation,[],[f11])).
% 3.06/0.92  
% 3.06/0.92  fof(f59,plain,(
% 3.06/0.92    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/0.92    inference(cnf_transformation,[],[f23])).
% 3.06/0.92  
% 3.06/0.92  fof(f6,axiom,(
% 3.06/0.92    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.06/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/0.92  
% 3.06/0.92  fof(f31,plain,(
% 3.06/0.92    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.06/0.92    inference(nnf_transformation,[],[f6])).
% 3.06/0.92  
% 3.06/0.92  fof(f49,plain,(
% 3.06/0.92    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.06/0.92    inference(cnf_transformation,[],[f31])).
% 3.06/0.92  
% 3.06/0.92  fof(f10,axiom,(
% 3.06/0.92    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 3.06/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/0.92  
% 3.06/0.92  fof(f21,plain,(
% 3.06/0.92    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.06/0.92    inference(ennf_transformation,[],[f10])).
% 3.06/0.92  
% 3.06/0.92  fof(f22,plain,(
% 3.06/0.92    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.06/0.92    inference(flattening,[],[f21])).
% 3.06/0.92  
% 3.06/0.92  fof(f32,plain,(
% 3.06/0.92    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.06/0.92    inference(nnf_transformation,[],[f22])).
% 3.06/0.92  
% 3.06/0.92  fof(f33,plain,(
% 3.06/0.92    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.06/0.92    inference(rectify,[],[f32])).
% 3.06/0.92  
% 3.06/0.92  fof(f34,plain,(
% 3.06/0.92    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0))))),
% 3.06/0.92    introduced(choice_axiom,[])).
% 3.06/0.92  
% 3.06/0.92  fof(f35,plain,(
% 3.06/0.92    ! [X0] : (((v2_funct_1(X0) | (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.06/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f34])).
% 3.06/0.92  
% 3.06/0.92  fof(f55,plain,(
% 3.06/0.92    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK0(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.06/0.92    inference(cnf_transformation,[],[f35])).
% 3.06/0.92  
% 3.06/0.92  fof(f62,plain,(
% 3.06/0.92    v1_funct_1(sK3)),
% 3.06/0.92    inference(cnf_transformation,[],[f41])).
% 3.06/0.92  
% 3.06/0.92  fof(f8,axiom,(
% 3.06/0.92    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.06/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/0.92  
% 3.06/0.92  fof(f20,plain,(
% 3.06/0.92    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.06/0.92    inference(ennf_transformation,[],[f8])).
% 3.06/0.92  
% 3.06/0.92  fof(f52,plain,(
% 3.06/0.92    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.06/0.92    inference(cnf_transformation,[],[f20])).
% 3.06/0.92  
% 3.06/0.92  fof(f50,plain,(
% 3.06/0.92    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.06/0.92    inference(cnf_transformation,[],[f31])).
% 3.06/0.92  
% 3.06/0.92  fof(f9,axiom,(
% 3.06/0.92    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.06/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/0.92  
% 3.06/0.92  fof(f53,plain,(
% 3.06/0.92    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.06/0.92    inference(cnf_transformation,[],[f9])).
% 3.06/0.92  
% 3.06/0.92  fof(f3,axiom,(
% 3.06/0.92    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.06/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/0.92  
% 3.06/0.92  fof(f16,plain,(
% 3.06/0.92    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.06/0.92    inference(ennf_transformation,[],[f3])).
% 3.06/0.92  
% 3.06/0.92  fof(f46,plain,(
% 3.06/0.92    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.06/0.92    inference(cnf_transformation,[],[f16])).
% 3.06/0.92  
% 3.06/0.92  fof(f2,axiom,(
% 3.06/0.92    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.06/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/0.92  
% 3.06/0.92  fof(f45,plain,(
% 3.06/0.92    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.06/0.92    inference(cnf_transformation,[],[f2])).
% 3.06/0.92  
% 3.06/0.92  fof(f57,plain,(
% 3.06/0.92    ( ! [X0] : (v2_funct_1(X0) | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.06/0.92    inference(cnf_transformation,[],[f35])).
% 3.06/0.92  
% 3.06/0.92  fof(f13,axiom,(
% 3.06/0.92    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 3.06/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/0.92  
% 3.06/0.92  fof(f25,plain,(
% 3.06/0.92    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.06/0.92    inference(ennf_transformation,[],[f13])).
% 3.06/0.92  
% 3.06/0.92  fof(f26,plain,(
% 3.06/0.92    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.06/0.92    inference(flattening,[],[f25])).
% 3.06/0.92  
% 3.06/0.92  fof(f61,plain,(
% 3.06/0.92    ( ! [X2,X0,X3,X1] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.06/0.92    inference(cnf_transformation,[],[f26])).
% 3.06/0.92  
% 3.06/0.92  fof(f63,plain,(
% 3.06/0.92    v1_funct_2(sK3,sK2,sK2)),
% 3.06/0.92    inference(cnf_transformation,[],[f41])).
% 3.06/0.92  
% 3.06/0.92  fof(f66,plain,(
% 3.06/0.92    r2_hidden(sK4,sK2) | ~v2_funct_1(sK3)),
% 3.06/0.92    inference(cnf_transformation,[],[f41])).
% 3.06/0.92  
% 3.06/0.92  fof(f68,plain,(
% 3.06/0.92    k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) | ~v2_funct_1(sK3)),
% 3.06/0.92    inference(cnf_transformation,[],[f41])).
% 3.06/0.92  
% 3.06/0.92  fof(f65,plain,(
% 3.06/0.92    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2) | v2_funct_1(sK3)) )),
% 3.06/0.92    inference(cnf_transformation,[],[f41])).
% 3.06/0.92  
% 3.06/0.92  fof(f58,plain,(
% 3.06/0.92    ( ! [X0] : (v2_funct_1(X0) | sK0(X0) != sK1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.06/0.92    inference(cnf_transformation,[],[f35])).
% 3.06/0.92  
% 3.06/0.92  fof(f56,plain,(
% 3.06/0.92    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK1(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.06/0.92    inference(cnf_transformation,[],[f35])).
% 3.06/0.92  
% 3.06/0.92  fof(f67,plain,(
% 3.06/0.92    r2_hidden(sK5,sK2) | ~v2_funct_1(sK3)),
% 3.06/0.92    inference(cnf_transformation,[],[f41])).
% 3.06/0.92  
% 3.06/0.92  fof(f69,plain,(
% 3.06/0.92    sK4 != sK5 | ~v2_funct_1(sK3)),
% 3.06/0.92    inference(cnf_transformation,[],[f41])).
% 3.06/0.92  
% 3.06/0.92  fof(f54,plain,(
% 3.06/0.92    ( ! [X4,X0,X3] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.06/0.92    inference(cnf_transformation,[],[f35])).
% 3.06/0.92  
% 3.06/0.92  fof(f4,axiom,(
% 3.06/0.92    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.06/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/0.92  
% 3.06/0.92  fof(f47,plain,(
% 3.06/0.92    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.06/0.92    inference(cnf_transformation,[],[f4])).
% 3.06/0.92  
% 3.06/0.92  fof(f7,axiom,(
% 3.06/0.92    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.06/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/0.92  
% 3.06/0.92  fof(f18,plain,(
% 3.06/0.92    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.06/0.92    inference(ennf_transformation,[],[f7])).
% 3.06/0.92  
% 3.06/0.92  fof(f19,plain,(
% 3.06/0.92    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.06/0.92    inference(flattening,[],[f18])).
% 3.06/0.92  
% 3.06/0.92  fof(f51,plain,(
% 3.06/0.92    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.06/0.92    inference(cnf_transformation,[],[f19])).
% 3.06/0.92  
% 3.06/0.92  fof(f1,axiom,(
% 3.06/0.92    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.06/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/0.92  
% 3.06/0.92  fof(f29,plain,(
% 3.06/0.92    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.06/0.92    inference(nnf_transformation,[],[f1])).
% 3.06/0.92  
% 3.06/0.92  fof(f30,plain,(
% 3.06/0.92    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.06/0.92    inference(flattening,[],[f29])).
% 3.06/0.92  
% 3.06/0.92  fof(f44,plain,(
% 3.06/0.92    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.06/0.92    inference(cnf_transformation,[],[f30])).
% 3.06/0.92  
% 3.06/0.92  fof(f42,plain,(
% 3.06/0.92    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.06/0.92    inference(cnf_transformation,[],[f30])).
% 3.06/0.92  
% 3.06/0.92  fof(f71,plain,(
% 3.06/0.92    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.06/0.92    inference(equality_resolution,[],[f42])).
% 3.06/0.92  
% 3.06/0.92  cnf(c_25,negated_conjecture,
% 3.06/0.92      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 3.06/0.92      inference(cnf_transformation,[],[f64]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_2605,plain,
% 3.06/0.92      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_18,plain,
% 3.06/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/0.92      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.06/0.92      inference(cnf_transformation,[],[f60]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_2611,plain,
% 3.06/0.92      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.06/0.92      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_3952,plain,
% 3.06/0.92      ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_2605,c_2611]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_17,plain,
% 3.06/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/0.92      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.06/0.92      inference(cnf_transformation,[],[f59]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_2612,plain,
% 3.06/0.92      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.06/0.92      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_4315,plain,
% 3.06/0.92      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
% 3.06/0.92      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_3952,c_2612]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_30,plain,
% 3.06/0.92      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_4759,plain,
% 3.06/0.92      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top ),
% 3.06/0.92      inference(global_propositional_subsumption,
% 3.06/0.92                [status(thm)],
% 3.06/0.92                [c_4315,c_30]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_8,plain,
% 3.06/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.06/0.92      inference(cnf_transformation,[],[f49]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_2615,plain,
% 3.06/0.92      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.06/0.92      | r1_tarski(X0,X1) = iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_4764,plain,
% 3.06/0.92      ( r1_tarski(k1_relat_1(sK3),sK2) = iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_4759,c_2615]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_15,plain,
% 3.06/0.92      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 3.06/0.92      | ~ v1_funct_1(X0)
% 3.06/0.92      | v2_funct_1(X0)
% 3.06/0.92      | ~ v1_relat_1(X0) ),
% 3.06/0.92      inference(cnf_transformation,[],[f55]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_27,negated_conjecture,
% 3.06/0.92      ( v1_funct_1(sK3) ),
% 3.06/0.92      inference(cnf_transformation,[],[f62]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_395,plain,
% 3.06/0.92      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 3.06/0.92      | v2_funct_1(X0)
% 3.06/0.92      | ~ v1_relat_1(X0)
% 3.06/0.92      | sK3 != X0 ),
% 3.06/0.92      inference(resolution_lifted,[status(thm)],[c_15,c_27]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_396,plain,
% 3.06/0.92      ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 3.06/0.92      | v2_funct_1(sK3)
% 3.06/0.92      | ~ v1_relat_1(sK3) ),
% 3.06/0.92      inference(unflattening,[status(thm)],[c_395]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_2600,plain,
% 3.06/0.92      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top
% 3.06/0.92      | v1_relat_1(sK3) != iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_396]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_28,plain,
% 3.06/0.92      ( v1_funct_1(sK3) = iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_50,plain,
% 3.06/0.92      ( r2_hidden(sK0(X0),k1_relat_1(X0)) = iProver_top
% 3.06/0.92      | v1_funct_1(X0) != iProver_top
% 3.06/0.92      | v2_funct_1(X0) = iProver_top
% 3.06/0.92      | v1_relat_1(X0) != iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_52,plain,
% 3.06/0.92      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 3.06/0.92      | v1_funct_1(sK3) != iProver_top
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top
% 3.06/0.92      | v1_relat_1(sK3) != iProver_top ),
% 3.06/0.92      inference(instantiation,[status(thm)],[c_50]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_2924,plain,
% 3.06/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/0.92      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 3.06/0.92      inference(instantiation,[status(thm)],[c_8]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_3003,plain,
% 3.06/0.92      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 3.06/0.92      | r1_tarski(sK3,k2_zfmisc_1(sK2,sK2)) ),
% 3.06/0.92      inference(instantiation,[status(thm)],[c_2924]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_3004,plain,
% 3.06/0.92      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 3.06/0.92      | r1_tarski(sK3,k2_zfmisc_1(sK2,sK2)) = iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_3003]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_10,plain,
% 3.06/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.06/0.92      | ~ v1_relat_1(X1)
% 3.06/0.92      | v1_relat_1(X0) ),
% 3.06/0.92      inference(cnf_transformation,[],[f52]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_7,plain,
% 3.06/0.92      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.06/0.92      inference(cnf_transformation,[],[f50]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_214,plain,
% 3.06/0.92      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.06/0.92      inference(prop_impl,[status(thm)],[c_7]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_215,plain,
% 3.06/0.92      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.06/0.92      inference(renaming,[status(thm)],[c_214]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_271,plain,
% 3.06/0.92      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.06/0.92      inference(bin_hyper_res,[status(thm)],[c_10,c_215]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_2879,plain,
% 3.06/0.92      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 3.06/0.92      | v1_relat_1(X0)
% 3.06/0.92      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.06/0.92      inference(instantiation,[status(thm)],[c_271]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_3078,plain,
% 3.06/0.92      ( ~ r1_tarski(sK3,k2_zfmisc_1(sK2,sK2))
% 3.06/0.92      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK2))
% 3.06/0.92      | v1_relat_1(sK3) ),
% 3.06/0.92      inference(instantiation,[status(thm)],[c_2879]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_3080,plain,
% 3.06/0.92      ( r1_tarski(sK3,k2_zfmisc_1(sK2,sK2)) != iProver_top
% 3.06/0.92      | v1_relat_1(k2_zfmisc_1(sK2,sK2)) != iProver_top
% 3.06/0.92      | v1_relat_1(sK3) = iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_3078]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_11,plain,
% 3.06/0.92      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.06/0.92      inference(cnf_transformation,[],[f53]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_3355,plain,
% 3.06/0.92      ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) ),
% 3.06/0.92      inference(instantiation,[status(thm)],[c_11]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_3356,plain,
% 3.06/0.92      ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) = iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_3355]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_3465,plain,
% 3.06/0.92      ( v2_funct_1(sK3) = iProver_top
% 3.06/0.92      | r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top ),
% 3.06/0.92      inference(global_propositional_subsumption,
% 3.06/0.92                [status(thm)],
% 3.06/0.92                [c_2600,c_28,c_30,c_52,c_3004,c_3080,c_3356]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_3466,plain,
% 3.06/0.92      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top ),
% 3.06/0.92      inference(renaming,[status(thm)],[c_3465]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_4,plain,
% 3.06/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.06/0.92      | ~ r2_hidden(X2,X0)
% 3.06/0.92      | r2_hidden(X2,X1) ),
% 3.06/0.92      inference(cnf_transformation,[],[f46]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_268,plain,
% 3.06/0.92      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.06/0.92      inference(bin_hyper_res,[status(thm)],[c_4,c_215]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_2604,plain,
% 3.06/0.92      ( r2_hidden(X0,X1) != iProver_top
% 3.06/0.92      | r2_hidden(X0,X2) = iProver_top
% 3.06/0.92      | r1_tarski(X1,X2) != iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_268]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_3588,plain,
% 3.06/0.92      ( r2_hidden(sK0(sK3),X0) = iProver_top
% 3.06/0.92      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_3466,c_2604]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_5096,plain,
% 3.06/0.92      ( r2_hidden(sK0(sK3),sK2) = iProver_top
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_4764,c_3588]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_6113,plain,
% 3.06/0.92      ( r2_hidden(sK0(sK3),X0) = iProver_top
% 3.06/0.92      | r1_tarski(sK2,X0) != iProver_top
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_5096,c_2604]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_3,plain,
% 3.06/0.92      ( r1_tarski(k1_xboole_0,X0) ),
% 3.06/0.92      inference(cnf_transformation,[],[f45]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_82,plain,
% 3.06/0.92      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_1955,plain,
% 3.06/0.92      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 3.06/0.92      theory(equality) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_4667,plain,
% 3.06/0.92      ( ~ r1_tarski(X0,X1) | r1_tarski(sK2,X1) | sK2 != X0 ),
% 3.06/0.92      inference(instantiation,[status(thm)],[c_1955]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_7205,plain,
% 3.06/0.92      ( r1_tarski(sK2,X0)
% 3.06/0.92      | ~ r1_tarski(k1_xboole_0,X0)
% 3.06/0.92      | sK2 != k1_xboole_0 ),
% 3.06/0.92      inference(instantiation,[status(thm)],[c_4667]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_7209,plain,
% 3.06/0.92      ( sK2 != k1_xboole_0
% 3.06/0.92      | r1_tarski(sK2,X0) = iProver_top
% 3.06/0.92      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_7205]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_13,plain,
% 3.06/0.92      ( ~ v1_funct_1(X0)
% 3.06/0.92      | v2_funct_1(X0)
% 3.06/0.92      | ~ v1_relat_1(X0)
% 3.06/0.92      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
% 3.06/0.92      inference(cnf_transformation,[],[f57]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_421,plain,
% 3.06/0.92      ( v2_funct_1(X0)
% 3.06/0.92      | ~ v1_relat_1(X0)
% 3.06/0.92      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
% 3.06/0.92      | sK3 != X0 ),
% 3.06/0.92      inference(resolution_lifted,[status(thm)],[c_13,c_27]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_422,plain,
% 3.06/0.92      ( v2_funct_1(sK3)
% 3.06/0.92      | ~ v1_relat_1(sK3)
% 3.06/0.92      | k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
% 3.06/0.92      inference(unflattening,[status(thm)],[c_421]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_2598,plain,
% 3.06/0.92      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top
% 3.06/0.92      | v1_relat_1(sK3) != iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_422]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_56,plain,
% 3.06/0.92      ( k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
% 3.06/0.92      | v1_funct_1(X0) != iProver_top
% 3.06/0.92      | v2_funct_1(X0) = iProver_top
% 3.06/0.92      | v1_relat_1(X0) != iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_58,plain,
% 3.06/0.92      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
% 3.06/0.92      | v1_funct_1(sK3) != iProver_top
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top
% 3.06/0.92      | v1_relat_1(sK3) != iProver_top ),
% 3.06/0.92      inference(instantiation,[status(thm)],[c_56]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_3472,plain,
% 3.06/0.92      ( v2_funct_1(sK3) = iProver_top
% 3.06/0.92      | k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
% 3.06/0.92      inference(global_propositional_subsumption,
% 3.06/0.92                [status(thm)],
% 3.06/0.92                [c_2598,c_28,c_30,c_58,c_3004,c_3080,c_3356]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_3473,plain,
% 3.06/0.92      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top ),
% 3.06/0.92      inference(renaming,[status(thm)],[c_3472]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_19,plain,
% 3.06/0.92      ( ~ v1_funct_2(X0,X1,X2)
% 3.06/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/0.92      | ~ r2_hidden(X3,X1)
% 3.06/0.92      | ~ v1_funct_1(X0)
% 3.06/0.92      | ~ v2_funct_1(X0)
% 3.06/0.92      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
% 3.06/0.92      | k1_xboole_0 = X2 ),
% 3.06/0.92      inference(cnf_transformation,[],[f61]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_26,negated_conjecture,
% 3.06/0.92      ( v1_funct_2(sK3,sK2,sK2) ),
% 3.06/0.92      inference(cnf_transformation,[],[f63]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_366,plain,
% 3.06/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/0.92      | ~ r2_hidden(X3,X1)
% 3.06/0.92      | ~ v1_funct_1(X0)
% 3.06/0.92      | ~ v2_funct_1(X0)
% 3.06/0.92      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
% 3.06/0.92      | sK2 != X2
% 3.06/0.92      | sK2 != X1
% 3.06/0.92      | sK3 != X0
% 3.06/0.92      | k1_xboole_0 = X2 ),
% 3.06/0.92      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_367,plain,
% 3.06/0.92      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 3.06/0.92      | ~ r2_hidden(X0,sK2)
% 3.06/0.92      | ~ v1_funct_1(sK3)
% 3.06/0.92      | ~ v2_funct_1(sK3)
% 3.06/0.92      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 3.06/0.92      | k1_xboole_0 = sK2 ),
% 3.06/0.92      inference(unflattening,[status(thm)],[c_366]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_371,plain,
% 3.06/0.92      ( ~ r2_hidden(X0,sK2)
% 3.06/0.92      | ~ v2_funct_1(sK3)
% 3.06/0.92      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 3.06/0.92      | k1_xboole_0 = sK2 ),
% 3.06/0.92      inference(global_propositional_subsumption,
% 3.06/0.92                [status(thm)],
% 3.06/0.92                [c_367,c_27,c_25]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_1951,plain,
% 3.06/0.92      ( ~ v2_funct_1(sK3) | sP1_iProver_split | k1_xboole_0 = sK2 ),
% 3.06/0.92      inference(splitting,
% 3.06/0.92                [splitting(split),new_symbols(definition,[])],
% 3.06/0.92                [c_371]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_2601,plain,
% 3.06/0.92      ( k1_xboole_0 = sK2
% 3.06/0.92      | v2_funct_1(sK3) != iProver_top
% 3.06/0.92      | sP1_iProver_split = iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_1951]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_3478,plain,
% 3.06/0.92      ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 3.06/0.92      | sK2 = k1_xboole_0
% 3.06/0.92      | sP1_iProver_split = iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_3473,c_2601]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_23,negated_conjecture,
% 3.06/0.92      ( r2_hidden(sK4,sK2) | ~ v2_funct_1(sK3) ),
% 3.06/0.92      inference(cnf_transformation,[],[f66]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_2607,plain,
% 3.06/0.92      ( r2_hidden(sK4,sK2) = iProver_top
% 3.06/0.92      | v2_funct_1(sK3) != iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_1950,plain,
% 3.06/0.92      ( ~ r2_hidden(X0,sK2)
% 3.06/0.92      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 3.06/0.92      | ~ sP1_iProver_split ),
% 3.06/0.92      inference(splitting,
% 3.06/0.92                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 3.06/0.92                [c_371]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_2602,plain,
% 3.06/0.92      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 3.06/0.92      | r2_hidden(X0,sK2) != iProver_top
% 3.06/0.92      | sP1_iProver_split != iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_1950]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_3117,plain,
% 3.06/0.92      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 3.06/0.92      | v2_funct_1(sK3) != iProver_top
% 3.06/0.92      | sP1_iProver_split != iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_2607,c_2602]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_3479,plain,
% 3.06/0.92      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 3.06/0.92      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 3.06/0.92      | sP1_iProver_split != iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_3473,c_3117]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_4865,plain,
% 3.06/0.92      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 3.06/0.92      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 3.06/0.92      | sK2 = k1_xboole_0 ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_3478,c_3479]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_21,negated_conjecture,
% 3.06/0.92      ( ~ v2_funct_1(sK3) | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
% 3.06/0.92      inference(cnf_transformation,[],[f68]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_2609,plain,
% 3.06/0.92      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
% 3.06/0.92      | v2_funct_1(sK3) != iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_3482,plain,
% 3.06/0.92      ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 3.06/0.92      | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_3473,c_2609]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_24,negated_conjecture,
% 3.06/0.92      ( ~ r2_hidden(X0,sK2)
% 3.06/0.92      | ~ r2_hidden(X1,sK2)
% 3.06/0.92      | v2_funct_1(sK3)
% 3.06/0.92      | X1 = X0
% 3.06/0.92      | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
% 3.06/0.92      inference(cnf_transformation,[],[f65]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_2606,plain,
% 3.06/0.92      ( X0 = X1
% 3.06/0.92      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
% 3.06/0.92      | r2_hidden(X1,sK2) != iProver_top
% 3.06/0.92      | r2_hidden(X0,sK2) != iProver_top
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_4181,plain,
% 3.06/0.92      ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
% 3.06/0.92      | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
% 3.06/0.92      | sK1(sK3) = X0
% 3.06/0.92      | r2_hidden(X0,sK2) != iProver_top
% 3.06/0.92      | r2_hidden(sK1(sK3),sK2) != iProver_top
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_3482,c_2606]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_4300,plain,
% 3.06/0.92      ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
% 3.06/0.92      | sK1(sK3) = sK0(sK3)
% 3.06/0.92      | r2_hidden(sK1(sK3),sK2) != iProver_top
% 3.06/0.92      | r2_hidden(sK0(sK3),sK2) != iProver_top
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top ),
% 3.06/0.92      inference(equality_resolution,[status(thm)],[c_4181]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_12,plain,
% 3.06/0.92      ( ~ v1_funct_1(X0)
% 3.06/0.92      | v2_funct_1(X0)
% 3.06/0.92      | ~ v1_relat_1(X0)
% 3.06/0.92      | sK1(X0) != sK0(X0) ),
% 3.06/0.92      inference(cnf_transformation,[],[f58]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_434,plain,
% 3.06/0.92      ( v2_funct_1(X0)
% 3.06/0.92      | ~ v1_relat_1(X0)
% 3.06/0.92      | sK1(X0) != sK0(X0)
% 3.06/0.92      | sK3 != X0 ),
% 3.06/0.92      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_435,plain,
% 3.06/0.92      ( v2_funct_1(sK3) | ~ v1_relat_1(sK3) | sK1(sK3) != sK0(sK3) ),
% 3.06/0.92      inference(unflattening,[status(thm)],[c_434]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_561,plain,
% 3.06/0.92      ( ~ v1_relat_1(sK3)
% 3.06/0.92      | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
% 3.06/0.92      | sK1(sK3) != sK0(sK3) ),
% 3.06/0.92      inference(resolution,[status(thm)],[c_435,c_21]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_14,plain,
% 3.06/0.92      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 3.06/0.92      | ~ v1_funct_1(X0)
% 3.06/0.92      | v2_funct_1(X0)
% 3.06/0.92      | ~ v1_relat_1(X0) ),
% 3.06/0.92      inference(cnf_transformation,[],[f56]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_408,plain,
% 3.06/0.92      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 3.06/0.92      | v2_funct_1(X0)
% 3.06/0.92      | ~ v1_relat_1(X0)
% 3.06/0.92      | sK3 != X0 ),
% 3.06/0.92      inference(resolution_lifted,[status(thm)],[c_14,c_27]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_409,plain,
% 3.06/0.92      ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 3.06/0.92      | v2_funct_1(sK3)
% 3.06/0.92      | ~ v1_relat_1(sK3) ),
% 3.06/0.92      inference(unflattening,[status(thm)],[c_408]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_2599,plain,
% 3.06/0.92      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top
% 3.06/0.92      | v1_relat_1(sK3) != iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_409]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_3589,plain,
% 3.06/0.92      ( r2_hidden(sK1(sK3),X0) = iProver_top
% 3.06/0.92      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top
% 3.06/0.92      | v1_relat_1(sK3) != iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_2599,c_2604]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_5219,plain,
% 3.06/0.92      ( v2_funct_1(sK3) = iProver_top
% 3.06/0.92      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 3.06/0.92      | r2_hidden(sK1(sK3),X0) = iProver_top ),
% 3.06/0.92      inference(global_propositional_subsumption,
% 3.06/0.92                [status(thm)],
% 3.06/0.92                [c_3589,c_30,c_3004,c_3080,c_3356]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_5220,plain,
% 3.06/0.92      ( r2_hidden(sK1(sK3),X0) = iProver_top
% 3.06/0.92      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top ),
% 3.06/0.92      inference(renaming,[status(thm)],[c_5219]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_5229,plain,
% 3.06/0.92      ( r2_hidden(sK1(sK3),sK2) = iProver_top
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_4764,c_5220]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_5241,plain,
% 3.06/0.92      ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top ),
% 3.06/0.92      inference(global_propositional_subsumption,
% 3.06/0.92                [status(thm)],
% 3.06/0.92                [c_4300,c_25,c_561,c_3003,c_3078,c_3355,c_5096,c_5229]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_5251,plain,
% 3.06/0.92      ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_5241,c_2609]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_22,negated_conjecture,
% 3.06/0.92      ( r2_hidden(sK5,sK2) | ~ v2_funct_1(sK3) ),
% 3.06/0.92      inference(cnf_transformation,[],[f67]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_2608,plain,
% 3.06/0.92      ( r2_hidden(sK5,sK2) = iProver_top
% 3.06/0.92      | v2_funct_1(sK3) != iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_3116,plain,
% 3.06/0.92      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
% 3.06/0.92      | v2_funct_1(sK3) != iProver_top
% 3.06/0.92      | sP1_iProver_split != iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_2608,c_2602]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_3480,plain,
% 3.06/0.92      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
% 3.06/0.92      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 3.06/0.92      | sP1_iProver_split != iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_3473,c_3116]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_5405,plain,
% 3.06/0.92      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
% 3.06/0.92      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 3.06/0.92      | sP1_iProver_split != iProver_top ),
% 3.06/0.92      inference(demodulation,[status(thm)],[c_5251,c_3480]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_6000,plain,
% 3.06/0.92      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
% 3.06/0.92      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 3.06/0.92      | sK2 = k1_xboole_0 ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_3478,c_5405]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_7672,plain,
% 3.06/0.92      ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 3.06/0.92      | sK2 = k1_xboole_0
% 3.06/0.92      | sK5 = sK4 ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_4865,c_6000]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_20,negated_conjecture,
% 3.06/0.92      ( ~ v2_funct_1(sK3) | sK4 != sK5 ),
% 3.06/0.92      inference(cnf_transformation,[],[f69]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_664,plain,
% 3.06/0.92      ( ~ v1_relat_1(sK3)
% 3.06/0.92      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 3.06/0.92      | sK5 != sK4 ),
% 3.06/0.92      inference(resolution,[status(thm)],[c_422,c_20]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_8374,plain,
% 3.06/0.92      ( sK2 = k1_xboole_0
% 3.06/0.92      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3)) ),
% 3.06/0.92      inference(global_propositional_subsumption,
% 3.06/0.92                [status(thm)],
% 3.06/0.92                [c_7672,c_25,c_664,c_3003,c_3078,c_3355]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_8375,plain,
% 3.06/0.92      ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 3.06/0.92      | sK2 = k1_xboole_0 ),
% 3.06/0.92      inference(renaming,[status(thm)],[c_8374]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_8383,plain,
% 3.06/0.92      ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
% 3.06/0.92      | sK1(sK3) = X0
% 3.06/0.92      | sK2 = k1_xboole_0
% 3.06/0.92      | r2_hidden(X0,sK2) != iProver_top
% 3.06/0.92      | r2_hidden(sK1(sK3),sK2) != iProver_top
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_8375,c_2606]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_8510,plain,
% 3.06/0.92      ( r2_hidden(X0,sK2) != iProver_top
% 3.06/0.92      | sK2 = k1_xboole_0
% 3.06/0.92      | sK1(sK3) = X0
% 3.06/0.92      | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top ),
% 3.06/0.92      inference(global_propositional_subsumption,
% 3.06/0.92                [status(thm)],
% 3.06/0.92                [c_8383,c_5229]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_8511,plain,
% 3.06/0.92      ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
% 3.06/0.92      | sK1(sK3) = X0
% 3.06/0.92      | sK2 = k1_xboole_0
% 3.06/0.92      | r2_hidden(X0,sK2) != iProver_top
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top ),
% 3.06/0.92      inference(renaming,[status(thm)],[c_8510]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_8523,plain,
% 3.06/0.92      ( sK1(sK3) = sK0(sK3)
% 3.06/0.92      | sK2 = k1_xboole_0
% 3.06/0.92      | r2_hidden(sK0(sK3),sK2) != iProver_top
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top ),
% 3.06/0.92      inference(equality_resolution,[status(thm)],[c_8511]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_59,plain,
% 3.06/0.92      ( sK1(X0) != sK0(X0)
% 3.06/0.92      | v1_funct_1(X0) != iProver_top
% 3.06/0.92      | v2_funct_1(X0) = iProver_top
% 3.06/0.92      | v1_relat_1(X0) != iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_61,plain,
% 3.06/0.92      ( sK1(sK3) != sK0(sK3)
% 3.06/0.92      | v1_funct_1(sK3) != iProver_top
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top
% 3.06/0.92      | v1_relat_1(sK3) != iProver_top ),
% 3.06/0.92      inference(instantiation,[status(thm)],[c_59]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_8534,plain,
% 3.06/0.92      ( sK2 = k1_xboole_0 | v2_funct_1(sK3) = iProver_top ),
% 3.06/0.92      inference(global_propositional_subsumption,
% 3.06/0.92                [status(thm)],
% 3.06/0.92                [c_8523,c_28,c_30,c_61,c_3004,c_3080,c_3356,c_5096]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_9076,plain,
% 3.06/0.92      ( r2_hidden(sK0(sK3),X0) = iProver_top
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top ),
% 3.06/0.92      inference(global_propositional_subsumption,
% 3.06/0.92                [status(thm)],
% 3.06/0.92                [c_6113,c_82,c_7209,c_8534]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_8541,plain,
% 3.06/0.92      ( sK2 = k1_xboole_0 | sP1_iProver_split = iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_8534,c_2601]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_6965,plain,
% 3.06/0.92      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK1(sK3))) = sK1(sK3)
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top
% 3.06/0.92      | sP1_iProver_split != iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_5229,c_2602]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_16,plain,
% 3.06/0.92      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.06/0.92      | ~ r2_hidden(X2,k1_relat_1(X1))
% 3.06/0.92      | ~ v1_funct_1(X1)
% 3.06/0.92      | ~ v2_funct_1(X1)
% 3.06/0.92      | ~ v1_relat_1(X1)
% 3.06/0.92      | X0 = X2
% 3.06/0.92      | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
% 3.06/0.92      inference(cnf_transformation,[],[f54]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_447,plain,
% 3.06/0.92      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.06/0.92      | ~ r2_hidden(X2,k1_relat_1(X1))
% 3.06/0.92      | ~ v2_funct_1(X1)
% 3.06/0.92      | ~ v1_relat_1(X1)
% 3.06/0.92      | X2 = X0
% 3.06/0.92      | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
% 3.06/0.92      | sK3 != X1 ),
% 3.06/0.92      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_448,plain,
% 3.06/0.92      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 3.06/0.92      | ~ r2_hidden(X1,k1_relat_1(sK3))
% 3.06/0.92      | ~ v2_funct_1(sK3)
% 3.06/0.92      | ~ v1_relat_1(sK3)
% 3.06/0.92      | X0 = X1
% 3.06/0.92      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
% 3.06/0.92      inference(unflattening,[status(thm)],[c_447]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_1949,plain,
% 3.06/0.92      ( ~ v2_funct_1(sK3) | ~ v1_relat_1(sK3) | sP0_iProver_split ),
% 3.06/0.92      inference(splitting,
% 3.06/0.92                [splitting(split),new_symbols(definition,[])],
% 3.06/0.92                [c_448]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_2595,plain,
% 3.06/0.92      ( v2_funct_1(sK3) != iProver_top
% 3.06/0.92      | v1_relat_1(sK3) != iProver_top
% 3.06/0.92      | sP0_iProver_split = iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_1949]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_7054,plain,
% 3.06/0.92      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK1(sK3))) = sK1(sK3)
% 3.06/0.92      | v1_relat_1(sK3) != iProver_top
% 3.06/0.92      | sP1_iProver_split != iProver_top
% 3.06/0.92      | sP0_iProver_split = iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_6965,c_2595]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_7096,plain,
% 3.06/0.92      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK1(sK3))) = sK1(sK3)
% 3.06/0.92      | sP1_iProver_split != iProver_top
% 3.06/0.92      | sP0_iProver_split = iProver_top ),
% 3.06/0.92      inference(global_propositional_subsumption,
% 3.06/0.92                [status(thm)],
% 3.06/0.92                [c_7054,c_30,c_3004,c_3080,c_3356]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_8689,plain,
% 3.06/0.92      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK1(sK3))) = sK1(sK3)
% 3.06/0.92      | sK2 = k1_xboole_0
% 3.06/0.92      | sP0_iProver_split = iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_8541,c_7096]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_573,plain,
% 3.06/0.92      ( ~ v1_relat_1(sK3) | sK1(sK3) != sK0(sK3) | sK5 != sK4 ),
% 3.06/0.92      inference(resolution,[status(thm)],[c_435,c_20]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_755,plain,
% 3.06/0.92      ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 3.06/0.92      | ~ v1_relat_1(sK3)
% 3.06/0.92      | sK5 != sK4 ),
% 3.06/0.92      inference(resolution,[status(thm)],[c_409,c_20]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_756,plain,
% 3.06/0.92      ( sK5 != sK4
% 3.06/0.92      | r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
% 3.06/0.92      | v1_relat_1(sK3) != iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_755]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_846,plain,
% 3.06/0.92      ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 3.06/0.92      | ~ v1_relat_1(sK3)
% 3.06/0.92      | sK5 != sK4 ),
% 3.06/0.92      inference(resolution,[status(thm)],[c_396,c_20]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_847,plain,
% 3.06/0.92      ( sK5 != sK4
% 3.06/0.92      | r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 3.06/0.92      | v1_relat_1(sK3) != iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_846]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_1948,plain,
% 3.06/0.92      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 3.06/0.92      | ~ r2_hidden(X1,k1_relat_1(sK3))
% 3.06/0.92      | X0 = X1
% 3.06/0.92      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
% 3.06/0.92      | ~ sP0_iProver_split ),
% 3.06/0.92      inference(splitting,
% 3.06/0.92                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.06/0.92                [c_448]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_2596,plain,
% 3.06/0.92      ( X0 = X1
% 3.06/0.92      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
% 3.06/0.92      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 3.06/0.92      | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top
% 3.06/0.92      | sP0_iProver_split != iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_1948]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_8382,plain,
% 3.06/0.92      ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
% 3.06/0.92      | sK1(sK3) = X0
% 3.06/0.92      | sK2 = k1_xboole_0
% 3.06/0.92      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 3.06/0.92      | r2_hidden(sK1(sK3),k1_relat_1(sK3)) != iProver_top
% 3.06/0.92      | sP0_iProver_split != iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_8375,c_2596]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_8543,plain,
% 3.06/0.92      ( sK2 = k1_xboole_0
% 3.06/0.92      | v1_relat_1(sK3) != iProver_top
% 3.06/0.92      | sP0_iProver_split = iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_8534,c_2595]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_8832,plain,
% 3.06/0.92      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) != iProver_top
% 3.06/0.92      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 3.06/0.92      | sK2 = k1_xboole_0
% 3.06/0.92      | sK1(sK3) = X0
% 3.06/0.92      | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0) ),
% 3.06/0.92      inference(global_propositional_subsumption,
% 3.06/0.92                [status(thm)],
% 3.06/0.92                [c_8382,c_30,c_3004,c_3080,c_3356,c_8543]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_8833,plain,
% 3.06/0.92      ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
% 3.06/0.92      | sK1(sK3) = X0
% 3.06/0.92      | sK2 = k1_xboole_0
% 3.06/0.92      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 3.06/0.92      | r2_hidden(sK1(sK3),k1_relat_1(sK3)) != iProver_top ),
% 3.06/0.92      inference(renaming,[status(thm)],[c_8832]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_8845,plain,
% 3.06/0.92      ( sK1(sK3) = sK0(sK3)
% 3.06/0.92      | sK2 = k1_xboole_0
% 3.06/0.92      | r2_hidden(sK1(sK3),k1_relat_1(sK3)) != iProver_top
% 3.06/0.92      | r2_hidden(sK0(sK3),k1_relat_1(sK3)) != iProver_top ),
% 3.06/0.92      inference(equality_resolution,[status(thm)],[c_8833]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_5407,plain,
% 3.06/0.92      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
% 3.06/0.92      | v2_funct_1(sK3) != iProver_top
% 3.06/0.92      | sP1_iProver_split != iProver_top ),
% 3.06/0.92      inference(demodulation,[status(thm)],[c_5251,c_3116]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_8540,plain,
% 3.06/0.92      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
% 3.06/0.92      | sK2 = k1_xboole_0
% 3.06/0.92      | sP1_iProver_split != iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_8534,c_5407]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_8568,plain,
% 3.06/0.92      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
% 3.06/0.92      | sK2 = k1_xboole_0 ),
% 3.06/0.92      inference(forward_subsumption_resolution,
% 3.06/0.92                [status(thm)],
% 3.06/0.92                [c_8540,c_8541]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_8542,plain,
% 3.06/0.92      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 3.06/0.92      | sK2 = k1_xboole_0
% 3.06/0.92      | sP1_iProver_split != iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_8534,c_3117]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_8560,plain,
% 3.06/0.92      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 3.06/0.92      | sK2 = k1_xboole_0 ),
% 3.06/0.92      inference(backward_subsumption_resolution,
% 3.06/0.92                [status(thm)],
% 3.06/0.92                [c_8541,c_8542]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_9333,plain,
% 3.06/0.92      ( sK2 = k1_xboole_0 | sK5 = sK4 ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_8568,c_8560]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_9405,plain,
% 3.06/0.92      ( sK2 = k1_xboole_0 ),
% 3.06/0.92      inference(global_propositional_subsumption,
% 3.06/0.92                [status(thm)],
% 3.06/0.92                [c_8689,c_25,c_30,c_573,c_756,c_847,c_3003,c_3004,c_3078,
% 3.06/0.92                 c_3080,c_3355,c_3356,c_8845,c_9333]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_9434,plain,
% 3.06/0.92      ( r2_hidden(sK5,k1_xboole_0) = iProver_top
% 3.06/0.92      | v2_funct_1(sK3) != iProver_top ),
% 3.06/0.92      inference(demodulation,[status(thm)],[c_9405,c_2608]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_5,plain,
% 3.06/0.92      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.06/0.92      inference(cnf_transformation,[],[f47]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_2618,plain,
% 3.06/0.92      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_9,plain,
% 3.06/0.92      ( m1_subset_1(X0,X1)
% 3.06/0.92      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.06/0.92      | ~ r2_hidden(X0,X2) ),
% 3.06/0.92      inference(cnf_transformation,[],[f51]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_2614,plain,
% 3.06/0.92      ( m1_subset_1(X0,X1) = iProver_top
% 3.06/0.92      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.06/0.92      | r2_hidden(X0,X2) != iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_4454,plain,
% 3.06/0.92      ( m1_subset_1(X0,X1) = iProver_top
% 3.06/0.92      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_2618,c_2614]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_9744,plain,
% 3.06/0.92      ( m1_subset_1(sK5,X0) = iProver_top
% 3.06/0.92      | v2_funct_1(sK3) != iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_9434,c_4454]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_10566,plain,
% 3.06/0.92      ( k1_relset_1(X0,X1,sK5) = k1_relat_1(sK5)
% 3.06/0.92      | v2_funct_1(sK3) != iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_9744,c_2611]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_11204,plain,
% 3.06/0.92      ( k1_relset_1(X0,X1,sK5) = k1_relat_1(sK5)
% 3.06/0.92      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3)) ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_3473,c_10566]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_11545,plain,
% 3.06/0.92      ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 3.06/0.92      | m1_subset_1(k1_relat_1(sK5),k1_zfmisc_1(X0)) = iProver_top
% 3.06/0.92      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_11204,c_2612]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_628,plain,
% 3.06/0.92      ( r2_hidden(sK4,sK2)
% 3.06/0.92      | ~ v1_relat_1(sK3)
% 3.06/0.92      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3)) ),
% 3.06/0.92      inference(resolution,[status(thm)],[c_422,c_23]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_640,plain,
% 3.06/0.92      ( r2_hidden(sK5,sK2)
% 3.06/0.92      | ~ v1_relat_1(sK3)
% 3.06/0.92      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3)) ),
% 3.06/0.92      inference(resolution,[status(thm)],[c_422,c_22]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_5426,plain,
% 3.06/0.92      ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4)
% 3.06/0.92      | sK5 = X0
% 3.06/0.92      | r2_hidden(X0,sK2) != iProver_top
% 3.06/0.92      | r2_hidden(sK5,sK2) != iProver_top
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_5251,c_2606]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_5461,plain,
% 3.06/0.92      ( sK5 = sK4
% 3.06/0.92      | r2_hidden(sK5,sK2) != iProver_top
% 3.06/0.92      | r2_hidden(sK4,sK2) != iProver_top
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top ),
% 3.06/0.92      inference(equality_resolution,[status(thm)],[c_5426]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_5470,plain,
% 3.06/0.92      ( ~ r2_hidden(sK5,sK2)
% 3.06/0.92      | ~ r2_hidden(sK4,sK2)
% 3.06/0.92      | v2_funct_1(sK3)
% 3.06/0.92      | sK5 = sK4 ),
% 3.06/0.92      inference(predicate_to_equality_rev,[status(thm)],[c_5461]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_9435,plain,
% 3.06/0.92      ( r2_hidden(sK4,k1_xboole_0) = iProver_top
% 3.06/0.92      | v2_funct_1(sK3) != iProver_top ),
% 3.06/0.92      inference(demodulation,[status(thm)],[c_9405,c_2607]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_9758,plain,
% 3.06/0.92      ( m1_subset_1(sK4,X0) = iProver_top
% 3.06/0.92      | v2_funct_1(sK3) != iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_9435,c_4454]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_10619,plain,
% 3.06/0.92      ( r1_tarski(sK4,X0) = iProver_top
% 3.06/0.92      | v2_funct_1(sK3) != iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_9758,c_2615]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_10564,plain,
% 3.06/0.92      ( r1_tarski(sK5,X0) = iProver_top
% 3.06/0.92      | v2_funct_1(sK3) != iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_9744,c_2615]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_0,plain,
% 3.06/0.92      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.06/0.92      inference(cnf_transformation,[],[f44]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_2621,plain,
% 3.06/0.92      ( X0 = X1
% 3.06/0.92      | r1_tarski(X0,X1) != iProver_top
% 3.06/0.92      | r1_tarski(X1,X0) != iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_10938,plain,
% 3.06/0.92      ( sK5 = X0
% 3.06/0.92      | r1_tarski(X0,sK5) != iProver_top
% 3.06/0.92      | v2_funct_1(sK3) != iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_10564,c_2621]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_11993,plain,
% 3.06/0.92      ( sK5 = sK4 | v2_funct_1(sK3) != iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_10619,c_10938]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_12008,plain,
% 3.06/0.92      ( ~ v2_funct_1(sK3) | sK5 = sK4 ),
% 3.06/0.92      inference(predicate_to_equality_rev,[status(thm)],[c_11993]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_13626,plain,
% 3.06/0.92      ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3)) ),
% 3.06/0.92      inference(global_propositional_subsumption,
% 3.06/0.92                [status(thm)],
% 3.06/0.92                [c_11545,c_25,c_628,c_640,c_664,c_3003,c_3078,c_3355,
% 3.06/0.92                 c_5470,c_12008]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_9433,plain,
% 3.06/0.92      ( X0 = X1
% 3.06/0.92      | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0)
% 3.06/0.92      | r2_hidden(X1,k1_xboole_0) != iProver_top
% 3.06/0.92      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top ),
% 3.06/0.92      inference(demodulation,[status(thm)],[c_9405,c_2606]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_13667,plain,
% 3.06/0.92      ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
% 3.06/0.92      | sK1(sK3) = X0
% 3.06/0.92      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.06/0.92      | r2_hidden(sK1(sK3),k1_xboole_0) != iProver_top
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_13626,c_9433]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_1981,plain,
% 3.06/0.92      ( v2_funct_1(sK3) != iProver_top
% 3.06/0.92      | v1_relat_1(sK3) != iProver_top
% 3.06/0.92      | sP0_iProver_split = iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_1949]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_9414,plain,
% 3.06/0.92      ( r2_hidden(sK1(sK3),k1_xboole_0) = iProver_top
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top ),
% 3.06/0.92      inference(demodulation,[status(thm)],[c_9405,c_5229]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_13669,plain,
% 3.06/0.92      ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
% 3.06/0.92      | sK1(sK3) = X0
% 3.06/0.92      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 3.06/0.92      | r2_hidden(sK1(sK3),k1_relat_1(sK3)) != iProver_top
% 3.06/0.92      | sP0_iProver_split != iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_13626,c_2596]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_2,plain,
% 3.06/0.92      ( r1_tarski(X0,X0) ),
% 3.06/0.92      inference(cnf_transformation,[],[f71]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_2620,plain,
% 3.06/0.92      ( r1_tarski(X0,X0) = iProver_top ),
% 3.06/0.92      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_5228,plain,
% 3.06/0.92      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_2620,c_5220]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_13719,plain,
% 3.06/0.92      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 3.06/0.92      | sK1(sK3) = X0
% 3.06/0.92      | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
% 3.06/0.92      | sP0_iProver_split != iProver_top ),
% 3.06/0.92      inference(global_propositional_subsumption,
% 3.06/0.92                [status(thm)],
% 3.06/0.92                [c_13669,c_30,c_756,c_3004,c_3080,c_3356,c_5228,c_11993]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_13720,plain,
% 3.06/0.92      ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
% 3.06/0.92      | sK1(sK3) = X0
% 3.06/0.92      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 3.06/0.92      | sP0_iProver_split != iProver_top ),
% 3.06/0.92      inference(renaming,[status(thm)],[c_13719]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_13730,plain,
% 3.06/0.92      ( sK1(sK3) = sK0(sK3)
% 3.06/0.92      | r2_hidden(sK0(sK3),k1_relat_1(sK3)) != iProver_top
% 3.06/0.92      | sP0_iProver_split != iProver_top ),
% 3.06/0.92      inference(equality_resolution,[status(thm)],[c_13720]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_13813,plain,
% 3.06/0.92      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.06/0.92      | sK1(sK3) = X0
% 3.06/0.92      | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top ),
% 3.06/0.92      inference(global_propositional_subsumption,
% 3.06/0.92                [status(thm)],
% 3.06/0.92                [c_13667,c_25,c_30,c_573,c_847,c_1981,c_3003,c_3004,
% 3.06/0.92                 c_3078,c_3080,c_3355,c_3356,c_9414,c_11993,c_13730]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_13814,plain,
% 3.06/0.92      ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
% 3.06/0.92      | sK1(sK3) = X0
% 3.06/0.92      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.06/0.92      | v2_funct_1(sK3) = iProver_top ),
% 3.06/0.92      inference(renaming,[status(thm)],[c_13813]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_13819,plain,
% 3.06/0.92      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.06/0.92      | sK1(sK3) = X0
% 3.06/0.92      | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0) ),
% 3.06/0.92      inference(global_propositional_subsumption,
% 3.06/0.92                [status(thm)],
% 3.06/0.92                [c_13814,c_25,c_30,c_573,c_847,c_1981,c_3003,c_3004,
% 3.06/0.92                 c_3078,c_3080,c_3355,c_3356,c_9414,c_11993,c_13667,
% 3.06/0.92                 c_13730]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_13820,plain,
% 3.06/0.92      ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
% 3.06/0.92      | sK1(sK3) = X0
% 3.06/0.92      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.06/0.92      inference(renaming,[status(thm)],[c_13819]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_13829,plain,
% 3.06/0.92      ( sK1(sK3) = sK0(sK3)
% 3.06/0.92      | r2_hidden(sK0(sK3),k1_xboole_0) != iProver_top ),
% 3.06/0.92      inference(equality_resolution,[status(thm)],[c_13820]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_13836,plain,
% 3.06/0.92      ( r2_hidden(sK0(sK3),k1_xboole_0) != iProver_top ),
% 3.06/0.92      inference(global_propositional_subsumption,
% 3.06/0.92                [status(thm)],
% 3.06/0.92                [c_13829,c_28,c_25,c_30,c_61,c_573,c_847,c_1981,c_3003,
% 3.06/0.92                 c_3004,c_3078,c_3080,c_3355,c_3356,c_11993,c_13730]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(c_13841,plain,
% 3.06/0.92      ( v2_funct_1(sK3) = iProver_top ),
% 3.06/0.92      inference(superposition,[status(thm)],[c_9076,c_13836]) ).
% 3.06/0.92  
% 3.06/0.92  cnf(contradiction,plain,
% 3.06/0.92      ( $false ),
% 3.06/0.92      inference(minisat,
% 3.06/0.92                [status(thm)],
% 3.06/0.92                [c_13841,c_13730,c_11993,c_3356,c_3355,c_3080,c_3078,
% 3.06/0.92                 c_3004,c_3003,c_1981,c_847,c_573,c_30,c_25]) ).
% 3.06/0.92  
% 3.06/0.92  
% 3.06/0.92  % SZS output end CNFRefutation for theBenchmark.p
% 3.06/0.92  
% 3.06/0.92  ------                               Statistics
% 3.06/0.92  
% 3.06/0.92  ------ General
% 3.06/0.92  
% 3.06/0.92  abstr_ref_over_cycles:                  0
% 3.06/0.92  abstr_ref_under_cycles:                 0
% 3.06/0.92  gc_basic_clause_elim:                   0
% 3.06/0.92  forced_gc_time:                         0
% 3.06/0.92  parsing_time:                           0.009
% 3.06/0.92  unif_index_cands_time:                  0.
% 3.06/0.92  unif_index_add_time:                    0.
% 3.06/0.92  orderings_time:                         0.
% 3.06/0.92  out_proof_time:                         0.018
% 3.06/0.92  total_time:                             0.336
% 3.06/0.92  num_of_symbols:                         53
% 3.06/0.92  num_of_terms:                           10926
% 3.06/0.92  
% 3.06/0.92  ------ Preprocessing
% 3.06/0.92  
% 3.06/0.92  num_of_splits:                          2
% 3.06/0.92  num_of_split_atoms:                     2
% 3.06/0.92  num_of_reused_defs:                     0
% 3.06/0.92  num_eq_ax_congr_red:                    16
% 3.06/0.92  num_of_sem_filtered_clauses:            1
% 3.06/0.92  num_of_subtypes:                        0
% 3.06/0.92  monotx_restored_types:                  0
% 3.06/0.92  sat_num_of_epr_types:                   0
% 3.06/0.92  sat_num_of_non_cyclic_types:            0
% 3.06/0.92  sat_guarded_non_collapsed_types:        0
% 3.06/0.92  num_pure_diseq_elim:                    0
% 3.06/0.92  simp_replaced_by:                       0
% 3.06/0.92  res_preprocessed:                       135
% 3.06/0.92  prep_upred:                             0
% 3.06/0.92  prep_unflattend:                        8
% 3.06/0.92  smt_new_axioms:                         0
% 3.06/0.92  pred_elim_cands:                        5
% 3.06/0.92  pred_elim:                              2
% 3.06/0.92  pred_elim_cl:                           2
% 3.06/0.92  pred_elim_cycles:                       4
% 3.06/0.92  merged_defs:                            8
% 3.06/0.92  merged_defs_ncl:                        0
% 3.06/0.92  bin_hyper_res:                          10
% 3.06/0.92  prep_cycles:                            4
% 3.06/0.92  pred_elim_time:                         0.022
% 3.06/0.92  splitting_time:                         0.
% 3.06/0.92  sem_filter_time:                        0.
% 3.06/0.92  monotx_time:                            0.
% 3.06/0.92  subtype_inf_time:                       0.
% 3.06/0.92  
% 3.06/0.92  ------ Problem properties
% 3.06/0.92  
% 3.06/0.92  clauses:                                27
% 3.06/0.92  conjectures:                            6
% 3.06/0.92  epr:                                    11
% 3.06/0.92  horn:                                   22
% 3.06/0.92  ground:                                 11
% 3.06/0.92  unary:                                  5
% 3.06/0.92  binary:                                 9
% 3.06/0.92  lits:                                   66
% 3.06/0.92  lits_eq:                                12
% 3.06/0.92  fd_pure:                                0
% 3.06/0.92  fd_pseudo:                              0
% 3.06/0.92  fd_cond:                                0
% 3.06/0.92  fd_pseudo_cond:                         3
% 3.06/0.92  ac_symbols:                             0
% 3.06/0.92  
% 3.06/0.92  ------ Propositional Solver
% 3.06/0.92  
% 3.06/0.92  prop_solver_calls:                      31
% 3.06/0.92  prop_fast_solver_calls:                 1481
% 3.06/0.92  smt_solver_calls:                       0
% 3.06/0.92  smt_fast_solver_calls:                  0
% 3.06/0.92  prop_num_of_clauses:                    4682
% 3.06/0.92  prop_preprocess_simplified:             9634
% 3.06/0.92  prop_fo_subsumed:                       51
% 3.06/0.92  prop_solver_time:                       0.
% 3.06/0.92  smt_solver_time:                        0.
% 3.06/0.92  smt_fast_solver_time:                   0.
% 3.06/0.92  prop_fast_solver_time:                  0.
% 3.06/0.92  prop_unsat_core_time:                   0.
% 3.06/0.92  
% 3.06/0.92  ------ QBF
% 3.06/0.92  
% 3.06/0.92  qbf_q_res:                              0
% 3.06/0.92  qbf_num_tautologies:                    0
% 3.06/0.92  qbf_prep_cycles:                        0
% 3.06/0.92  
% 3.06/0.92  ------ BMC1
% 3.06/0.92  
% 3.06/0.92  bmc1_current_bound:                     -1
% 3.06/0.92  bmc1_last_solved_bound:                 -1
% 3.06/0.92  bmc1_unsat_core_size:                   -1
% 3.06/0.92  bmc1_unsat_core_parents_size:           -1
% 3.06/0.92  bmc1_merge_next_fun:                    0
% 3.06/0.92  bmc1_unsat_core_clauses_time:           0.
% 3.06/0.92  
% 3.06/0.92  ------ Instantiation
% 3.06/0.92  
% 3.06/0.92  inst_num_of_clauses:                    1169
% 3.06/0.92  inst_num_in_passive:                    463
% 3.06/0.92  inst_num_in_active:                     707
% 3.06/0.92  inst_num_in_unprocessed:                0
% 3.06/0.92  inst_num_of_loops:                      780
% 3.06/0.92  inst_num_of_learning_restarts:          0
% 3.06/0.92  inst_num_moves_active_passive:          67
% 3.06/0.92  inst_lit_activity:                      0
% 3.06/0.92  inst_lit_activity_moves:                0
% 3.06/0.92  inst_num_tautologies:                   0
% 3.06/0.92  inst_num_prop_implied:                  0
% 3.06/0.92  inst_num_existing_simplified:           0
% 3.06/0.92  inst_num_eq_res_simplified:             0
% 3.06/0.92  inst_num_child_elim:                    0
% 3.06/0.92  inst_num_of_dismatching_blockings:      965
% 3.06/0.92  inst_num_of_non_proper_insts:           2234
% 3.06/0.92  inst_num_of_duplicates:                 0
% 3.06/0.92  inst_inst_num_from_inst_to_res:         0
% 3.06/0.92  inst_dismatching_checking_time:         0.
% 3.06/0.92  
% 3.06/0.92  ------ Resolution
% 3.06/0.92  
% 3.06/0.92  res_num_of_clauses:                     0
% 3.06/0.92  res_num_in_passive:                     0
% 3.06/0.92  res_num_in_active:                      0
% 3.06/0.92  res_num_of_loops:                       139
% 3.06/0.92  res_forward_subset_subsumed:            248
% 3.06/0.92  res_backward_subset_subsumed:           8
% 3.06/0.92  res_forward_subsumed:                   0
% 3.06/0.92  res_backward_subsumed:                  0
% 3.06/0.92  res_forward_subsumption_resolution:     0
% 3.06/0.92  res_backward_subsumption_resolution:    0
% 3.06/0.92  res_clause_to_clause_subsumption:       611
% 3.06/0.92  res_orphan_elimination:                 0
% 3.06/0.92  res_tautology_del:                      251
% 3.06/0.92  res_num_eq_res_simplified:              0
% 3.06/0.92  res_num_sel_changes:                    0
% 3.06/0.92  res_moves_from_active_to_pass:          0
% 3.06/0.92  
% 3.06/0.92  ------ Superposition
% 3.06/0.92  
% 3.06/0.92  sup_time_total:                         0.
% 3.06/0.92  sup_time_generating:                    0.
% 3.06/0.92  sup_time_sim_full:                      0.
% 3.06/0.92  sup_time_sim_immed:                     0.
% 3.06/0.92  
% 3.06/0.92  sup_num_of_clauses:                     211
% 3.06/0.92  sup_num_in_active:                      107
% 3.06/0.92  sup_num_in_passive:                     104
% 3.06/0.92  sup_num_of_loops:                       155
% 3.06/0.92  sup_fw_superposition:                   207
% 3.06/0.92  sup_bw_superposition:                   212
% 3.06/0.92  sup_immediate_simplified:               81
% 3.06/0.92  sup_given_eliminated:                   0
% 3.06/0.92  comparisons_done:                       0
% 3.06/0.92  comparisons_avoided:                    39
% 3.06/0.92  
% 3.06/0.92  ------ Simplifications
% 3.06/0.92  
% 3.06/0.92  
% 3.06/0.92  sim_fw_subset_subsumed:                 34
% 3.06/0.92  sim_bw_subset_subsumed:                 24
% 3.06/0.92  sim_fw_subsumed:                        17
% 3.06/0.92  sim_bw_subsumed:                        0
% 3.06/0.92  sim_fw_subsumption_res:                 3
% 3.06/0.92  sim_bw_subsumption_res:                 1
% 3.06/0.92  sim_tautology_del:                      13
% 3.06/0.92  sim_eq_tautology_del:                   29
% 3.06/0.92  sim_eq_res_simp:                        0
% 3.06/0.92  sim_fw_demodulated:                     15
% 3.06/0.92  sim_bw_demodulated:                     44
% 3.06/0.92  sim_light_normalised:                   12
% 3.06/0.92  sim_joinable_taut:                      0
% 3.06/0.92  sim_joinable_simp:                      0
% 3.06/0.92  sim_ac_normalised:                      0
% 3.06/0.92  sim_smt_subsumption:                    0
% 3.06/0.92  
%------------------------------------------------------------------------------
