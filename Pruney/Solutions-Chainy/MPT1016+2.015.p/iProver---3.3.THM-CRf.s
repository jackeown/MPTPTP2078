%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:54 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :  152 (3176 expanded)
%              Number of clauses        :  102 ( 928 expanded)
%              Number of leaves         :   15 ( 622 expanded)
%              Depth                    :   22
%              Number of atoms          :  548 (23618 expanded)
%              Number of equality atoms :  220 (7426 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).

fof(f37,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f30,plain,(
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

fof(f29,plain,
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

fof(f31,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f28,f30,f29])).

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f31])).

fof(f38,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | sK0(X0) != sK1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK2)
      | v2_funct_1(sK3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f35,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK0(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK1(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f50,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f51,plain,
    ( sK4 != sK5
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_290,plain,
    ( ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_19])).

cnf(c_291,plain,
    ( ~ v1_relat_1(sK3)
    | v2_funct_1(sK3)
    | k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_1914,plain,
    ( ~ v1_relat_1(sK3)
    | v2_funct_1(sK3)
    | k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
    inference(subtyping,[status(esa)],[c_291])).

cnf(c_2318,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1914])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_22,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1986,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1914])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | sK1(X0) != sK0(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_303,plain,
    ( ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | sK1(X0) != sK0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_19])).

cnf(c_304,plain,
    ( ~ v1_relat_1(sK3)
    | v2_funct_1(sK3)
    | sK1(sK3) != sK0(sK3) ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_1913,plain,
    ( ~ v1_relat_1(sK3)
    | v2_funct_1(sK3)
    | sK1(sK3) != sK0(sK3) ),
    inference(subtyping,[status(esa)],[c_304])).

cnf(c_1987,plain,
    ( sK1(sK3) != sK0(sK3)
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1913])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1927,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | v1_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2469,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1927])).

cnf(c_2470,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2469])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(X1,sK2)
    | v2_funct_1(sK3)
    | X1 = X0
    | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1920,negated_conjecture,
    ( ~ r2_hidden(X0_48,sK2)
    | ~ r2_hidden(X1_48,sK2)
    | v2_funct_1(sK3)
    | X1_48 = X0_48
    | k1_funct_1(sK3,X1_48) != k1_funct_1(sK3,X0_48) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2500,plain,
    ( ~ r2_hidden(sK1(sK3),sK2)
    | ~ r2_hidden(sK0(sK3),sK2)
    | v2_funct_1(sK3)
    | k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
    | sK1(sK3) = sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_1920])).

cnf(c_2501,plain,
    ( k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
    | sK1(sK3) = sK0(sK3)
    | r2_hidden(sK1(sK3),sK2) != iProver_top
    | r2_hidden(sK0(sK3),sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2500])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_264,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_19])).

cnf(c_265,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_264])).

cnf(c_1916,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(subtyping,[status(esa)],[c_265])).

cnf(c_2316,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1916])).

cnf(c_266,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_265])).

cnf(c_3198,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2316,c_22,c_266,c_2470])).

cnf(c_1919,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2312,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1919])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1925,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | k1_relset_1(X1_49,X2_49,X0_49) = k1_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2306,plain,
    ( k1_relset_1(X0_49,X1_49,X2_49) = k1_relat_1(X2_49)
    | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1925])).

cnf(c_2681,plain,
    ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2312,c_2306])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1926,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | m1_subset_1(k1_relset_1(X1_49,X2_49,X0_49),k1_zfmisc_1(X1_49)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2305,plain,
    ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))) != iProver_top
    | m1_subset_1(k1_relset_1(X1_49,X2_49,X0_49),k1_zfmisc_1(X1_49)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1926])).

cnf(c_2740,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2681,c_2305])).

cnf(c_3010,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2740,c_22])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1928,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(X1_49))
    | ~ r2_hidden(X0_48,X0_49)
    | r2_hidden(X0_48,X1_49) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2303,plain,
    ( m1_subset_1(X0_49,k1_zfmisc_1(X1_49)) != iProver_top
    | r2_hidden(X0_48,X0_49) != iProver_top
    | r2_hidden(X0_48,X1_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1928])).

cnf(c_3015,plain,
    ( r2_hidden(X0_48,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X0_48,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3010,c_2303])).

cnf(c_3204,plain,
    ( r2_hidden(sK0(sK3),sK2) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3198,c_3015])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_277,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_19])).

cnf(c_278,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_277])).

cnf(c_1915,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(subtyping,[status(esa)],[c_278])).

cnf(c_2317,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1915])).

cnf(c_279,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_278])).

cnf(c_3220,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2317,c_22,c_279,c_2470])).

cnf(c_3226,plain,
    ( r2_hidden(sK1(sK3),sK2) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3220,c_3015])).

cnf(c_3229,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2318,c_22,c_1986,c_1987,c_2470,c_2501,c_3204,c_3226])).

cnf(c_13,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1923,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2308,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1923])).

cnf(c_3238,plain,
    ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_3229,c_2308])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1922,negated_conjecture,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2309,plain,
    ( r2_hidden(sK5,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1922])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_235,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
    | sK2 != X2
    | sK2 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_236,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ r2_hidden(X0,sK2)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_235])).

cnf(c_240,plain,
    ( ~ r2_hidden(X0,sK2)
    | ~ v2_funct_1(sK3)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_236,c_19,c_17])).

cnf(c_1917,plain,
    ( ~ r2_hidden(X0_48,sK2)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK2
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0_48)) = X0_48 ),
    inference(subtyping,[status(esa)],[c_240])).

cnf(c_1929,plain,
    ( ~ r2_hidden(X0_48,sK2)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0_48)) = X0_48
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1917])).

cnf(c_2315,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0_48)) = X0_48
    | r2_hidden(X0_48,sK2) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1929])).

cnf(c_2789,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
    | v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2309,c_2315])).

cnf(c_3284,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
    | v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_3238,c_2789])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1934,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_1962,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1934])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_224,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_7])).

cnf(c_225,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_224])).

cnf(c_1918,plain,
    ( ~ r2_hidden(X0_48,k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_225])).

cnf(c_1978,plain,
    ( ~ r2_hidden(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1918])).

cnf(c_1930,plain,
    ( ~ v2_funct_1(sK3)
    | sP0_iProver_split
    | k1_xboole_0 = sK2 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1917])).

cnf(c_1980,plain,
    ( k1_xboole_0 = sK2
    | v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1930])).

cnf(c_3231,plain,
    ( v2_funct_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3229])).

cnf(c_3236,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3229,c_2789])).

cnf(c_3243,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3236,c_3238])).

cnf(c_1939,plain,
    ( ~ r2_hidden(X0_48,X0_49)
    | r2_hidden(X1_48,X1_49)
    | X1_49 != X0_49
    | X1_48 != X0_48 ),
    theory(equality)).

cnf(c_3026,plain,
    ( r2_hidden(X0_48,X0_49)
    | ~ r2_hidden(sK4,sK2)
    | X0_49 != sK2
    | X0_48 != sK4 ),
    inference(instantiation,[status(thm)],[c_1939])).

cnf(c_3513,plain,
    ( r2_hidden(X0_48,k1_xboole_0)
    | ~ r2_hidden(sK4,sK2)
    | k1_xboole_0 != sK2
    | X0_48 != sK4 ),
    inference(instantiation,[status(thm)],[c_3026])).

cnf(c_3518,plain,
    ( ~ r2_hidden(sK4,sK2)
    | r2_hidden(sK4,k1_xboole_0)
    | k1_xboole_0 != sK2
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3513])).

cnf(c_3533,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3284,c_22,c_15,c_1962,c_1978,c_1980,c_1986,c_1987,c_2470,c_2501,c_3204,c_3226,c_3231,c_3243,c_3518])).

cnf(c_1921,negated_conjecture,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2310,plain,
    ( r2_hidden(sK4,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1921])).

cnf(c_2790,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2310,c_2315])).

cnf(c_3235,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3229,c_2790])).

cnf(c_3536,plain,
    ( sK5 = sK4
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_3533,c_3235])).

cnf(c_1937,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_3049,plain,
    ( sK5 != X0_48
    | sK4 != X0_48
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_1937])).

cnf(c_3050,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3049])).

cnf(c_12,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | sK4 != sK5 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1924,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | sK4 != sK5 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1971,plain,
    ( sK4 != sK5
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1924])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3536,c_3518,c_3231,c_3229,c_3050,c_1980,c_1978,c_1971,c_1962,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:17:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.77/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/0.98  
% 1.77/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.77/0.98  
% 1.77/0.98  ------  iProver source info
% 1.77/0.98  
% 1.77/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.77/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.77/0.98  git: non_committed_changes: false
% 1.77/0.98  git: last_make_outside_of_git: false
% 1.77/0.98  
% 1.77/0.98  ------ 
% 1.77/0.98  
% 1.77/0.98  ------ Input Options
% 1.77/0.98  
% 1.77/0.98  --out_options                           all
% 1.77/0.98  --tptp_safe_out                         true
% 1.77/0.98  --problem_path                          ""
% 1.77/0.98  --include_path                          ""
% 1.77/0.98  --clausifier                            res/vclausify_rel
% 1.77/0.98  --clausifier_options                    --mode clausify
% 1.77/0.98  --stdin                                 false
% 1.77/0.98  --stats_out                             all
% 1.77/0.98  
% 1.77/0.98  ------ General Options
% 1.77/0.98  
% 1.77/0.98  --fof                                   false
% 1.77/0.98  --time_out_real                         305.
% 1.77/0.98  --time_out_virtual                      -1.
% 1.77/0.98  --symbol_type_check                     false
% 1.77/0.98  --clausify_out                          false
% 1.77/0.98  --sig_cnt_out                           false
% 1.77/0.98  --trig_cnt_out                          false
% 1.77/0.98  --trig_cnt_out_tolerance                1.
% 1.77/0.98  --trig_cnt_out_sk_spl                   false
% 1.77/0.98  --abstr_cl_out                          false
% 1.77/0.98  
% 1.77/0.98  ------ Global Options
% 1.77/0.98  
% 1.77/0.98  --schedule                              default
% 1.77/0.98  --add_important_lit                     false
% 1.77/0.98  --prop_solver_per_cl                    1000
% 1.77/0.98  --min_unsat_core                        false
% 1.77/0.98  --soft_assumptions                      false
% 1.77/0.98  --soft_lemma_size                       3
% 1.77/0.98  --prop_impl_unit_size                   0
% 1.77/0.98  --prop_impl_unit                        []
% 1.77/0.98  --share_sel_clauses                     true
% 1.77/0.98  --reset_solvers                         false
% 1.77/0.98  --bc_imp_inh                            [conj_cone]
% 1.77/0.98  --conj_cone_tolerance                   3.
% 1.77/0.98  --extra_neg_conj                        none
% 1.77/0.98  --large_theory_mode                     true
% 1.77/0.98  --prolific_symb_bound                   200
% 1.77/0.98  --lt_threshold                          2000
% 1.77/0.98  --clause_weak_htbl                      true
% 1.77/0.98  --gc_record_bc_elim                     false
% 1.77/0.98  
% 1.77/0.98  ------ Preprocessing Options
% 1.77/0.98  
% 1.77/0.98  --preprocessing_flag                    true
% 1.77/0.98  --time_out_prep_mult                    0.1
% 1.77/0.98  --splitting_mode                        input
% 1.77/0.98  --splitting_grd                         true
% 1.77/0.98  --splitting_cvd                         false
% 1.77/0.98  --splitting_cvd_svl                     false
% 1.77/0.98  --splitting_nvd                         32
% 1.77/0.98  --sub_typing                            true
% 1.77/0.98  --prep_gs_sim                           true
% 1.77/0.98  --prep_unflatten                        true
% 1.77/0.98  --prep_res_sim                          true
% 1.77/0.98  --prep_upred                            true
% 1.77/0.98  --prep_sem_filter                       exhaustive
% 1.77/0.98  --prep_sem_filter_out                   false
% 1.77/0.98  --pred_elim                             true
% 1.77/0.98  --res_sim_input                         true
% 1.77/0.98  --eq_ax_congr_red                       true
% 1.77/0.98  --pure_diseq_elim                       true
% 1.77/0.98  --brand_transform                       false
% 1.77/0.98  --non_eq_to_eq                          false
% 1.77/0.98  --prep_def_merge                        true
% 1.77/0.98  --prep_def_merge_prop_impl              false
% 1.77/0.98  --prep_def_merge_mbd                    true
% 1.77/0.98  --prep_def_merge_tr_red                 false
% 1.77/0.98  --prep_def_merge_tr_cl                  false
% 1.77/0.98  --smt_preprocessing                     true
% 1.77/0.98  --smt_ac_axioms                         fast
% 1.77/0.98  --preprocessed_out                      false
% 1.77/0.98  --preprocessed_stats                    false
% 1.77/0.98  
% 1.77/0.98  ------ Abstraction refinement Options
% 1.77/0.98  
% 1.77/0.98  --abstr_ref                             []
% 1.77/0.98  --abstr_ref_prep                        false
% 1.77/0.98  --abstr_ref_until_sat                   false
% 1.77/0.98  --abstr_ref_sig_restrict                funpre
% 1.77/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.77/0.98  --abstr_ref_under                       []
% 1.77/0.98  
% 1.77/0.98  ------ SAT Options
% 1.77/0.98  
% 1.77/0.98  --sat_mode                              false
% 1.77/0.98  --sat_fm_restart_options                ""
% 1.77/0.98  --sat_gr_def                            false
% 1.77/0.98  --sat_epr_types                         true
% 1.77/0.98  --sat_non_cyclic_types                  false
% 1.77/0.98  --sat_finite_models                     false
% 1.77/0.98  --sat_fm_lemmas                         false
% 1.77/0.98  --sat_fm_prep                           false
% 1.77/0.98  --sat_fm_uc_incr                        true
% 1.77/0.98  --sat_out_model                         small
% 1.77/0.98  --sat_out_clauses                       false
% 1.77/0.98  
% 1.77/0.98  ------ QBF Options
% 1.77/0.98  
% 1.77/0.98  --qbf_mode                              false
% 1.77/0.98  --qbf_elim_univ                         false
% 1.77/0.98  --qbf_dom_inst                          none
% 1.77/0.98  --qbf_dom_pre_inst                      false
% 1.77/0.98  --qbf_sk_in                             false
% 1.77/0.98  --qbf_pred_elim                         true
% 1.77/0.98  --qbf_split                             512
% 1.77/0.98  
% 1.77/0.98  ------ BMC1 Options
% 1.77/0.98  
% 1.77/0.98  --bmc1_incremental                      false
% 1.77/0.98  --bmc1_axioms                           reachable_all
% 1.77/0.98  --bmc1_min_bound                        0
% 1.77/0.98  --bmc1_max_bound                        -1
% 1.77/0.98  --bmc1_max_bound_default                -1
% 1.77/0.98  --bmc1_symbol_reachability              true
% 1.77/0.98  --bmc1_property_lemmas                  false
% 1.77/0.98  --bmc1_k_induction                      false
% 1.77/0.98  --bmc1_non_equiv_states                 false
% 1.77/0.98  --bmc1_deadlock                         false
% 1.77/0.98  --bmc1_ucm                              false
% 1.77/0.98  --bmc1_add_unsat_core                   none
% 1.77/0.98  --bmc1_unsat_core_children              false
% 1.77/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.77/0.98  --bmc1_out_stat                         full
% 1.77/0.98  --bmc1_ground_init                      false
% 1.77/0.98  --bmc1_pre_inst_next_state              false
% 1.77/0.98  --bmc1_pre_inst_state                   false
% 1.77/0.98  --bmc1_pre_inst_reach_state             false
% 1.77/0.98  --bmc1_out_unsat_core                   false
% 1.77/0.98  --bmc1_aig_witness_out                  false
% 1.77/0.98  --bmc1_verbose                          false
% 1.77/0.98  --bmc1_dump_clauses_tptp                false
% 1.77/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.77/0.98  --bmc1_dump_file                        -
% 1.77/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.77/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.77/0.98  --bmc1_ucm_extend_mode                  1
% 1.77/0.98  --bmc1_ucm_init_mode                    2
% 1.77/0.98  --bmc1_ucm_cone_mode                    none
% 1.77/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.77/0.98  --bmc1_ucm_relax_model                  4
% 1.77/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.77/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.77/0.98  --bmc1_ucm_layered_model                none
% 1.77/0.98  --bmc1_ucm_max_lemma_size               10
% 1.77/0.98  
% 1.77/0.98  ------ AIG Options
% 1.77/0.98  
% 1.77/0.98  --aig_mode                              false
% 1.77/0.98  
% 1.77/0.98  ------ Instantiation Options
% 1.77/0.98  
% 1.77/0.98  --instantiation_flag                    true
% 1.77/0.98  --inst_sos_flag                         false
% 1.77/0.98  --inst_sos_phase                        true
% 1.77/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.77/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.77/0.98  --inst_lit_sel_side                     num_symb
% 1.77/0.98  --inst_solver_per_active                1400
% 1.77/0.98  --inst_solver_calls_frac                1.
% 1.77/0.98  --inst_passive_queue_type               priority_queues
% 1.77/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.77/0.98  --inst_passive_queues_freq              [25;2]
% 1.77/0.98  --inst_dismatching                      true
% 1.77/0.98  --inst_eager_unprocessed_to_passive     true
% 1.77/0.98  --inst_prop_sim_given                   true
% 1.77/0.98  --inst_prop_sim_new                     false
% 1.77/0.98  --inst_subs_new                         false
% 1.77/0.98  --inst_eq_res_simp                      false
% 1.77/0.98  --inst_subs_given                       false
% 1.77/0.98  --inst_orphan_elimination               true
% 1.77/0.98  --inst_learning_loop_flag               true
% 1.77/0.98  --inst_learning_start                   3000
% 1.77/0.98  --inst_learning_factor                  2
% 1.77/0.98  --inst_start_prop_sim_after_learn       3
% 1.77/0.98  --inst_sel_renew                        solver
% 1.77/0.98  --inst_lit_activity_flag                true
% 1.77/0.98  --inst_restr_to_given                   false
% 1.77/0.98  --inst_activity_threshold               500
% 1.77/0.98  --inst_out_proof                        true
% 1.77/0.98  
% 1.77/0.98  ------ Resolution Options
% 1.77/0.98  
% 1.77/0.98  --resolution_flag                       true
% 1.77/0.98  --res_lit_sel                           adaptive
% 1.77/0.98  --res_lit_sel_side                      none
% 1.77/0.98  --res_ordering                          kbo
% 1.77/0.98  --res_to_prop_solver                    active
% 1.77/0.98  --res_prop_simpl_new                    false
% 1.77/0.98  --res_prop_simpl_given                  true
% 1.77/0.98  --res_passive_queue_type                priority_queues
% 1.77/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.77/0.98  --res_passive_queues_freq               [15;5]
% 1.77/0.98  --res_forward_subs                      full
% 1.77/0.98  --res_backward_subs                     full
% 1.77/0.98  --res_forward_subs_resolution           true
% 1.77/0.98  --res_backward_subs_resolution          true
% 1.77/0.98  --res_orphan_elimination                true
% 1.77/0.98  --res_time_limit                        2.
% 1.77/0.98  --res_out_proof                         true
% 1.77/0.98  
% 1.77/0.98  ------ Superposition Options
% 1.77/0.98  
% 1.77/0.98  --superposition_flag                    true
% 1.77/0.98  --sup_passive_queue_type                priority_queues
% 1.77/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.77/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.77/0.98  --demod_completeness_check              fast
% 1.77/0.98  --demod_use_ground                      true
% 1.77/0.98  --sup_to_prop_solver                    passive
% 1.77/0.98  --sup_prop_simpl_new                    true
% 1.77/0.98  --sup_prop_simpl_given                  true
% 1.77/0.98  --sup_fun_splitting                     false
% 1.77/0.98  --sup_smt_interval                      50000
% 1.77/0.98  
% 1.77/0.98  ------ Superposition Simplification Setup
% 1.77/0.98  
% 1.77/0.98  --sup_indices_passive                   []
% 1.77/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.77/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.77/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.77/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.77/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.77/0.98  --sup_full_bw                           [BwDemod]
% 1.77/0.98  --sup_immed_triv                        [TrivRules]
% 1.77/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.77/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.77/0.98  --sup_immed_bw_main                     []
% 1.77/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.77/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.77/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.77/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.77/0.98  
% 1.77/0.98  ------ Combination Options
% 1.77/0.98  
% 1.77/0.98  --comb_res_mult                         3
% 1.77/0.98  --comb_sup_mult                         2
% 1.77/0.98  --comb_inst_mult                        10
% 1.77/0.98  
% 1.77/0.98  ------ Debug Options
% 1.77/0.98  
% 1.77/0.98  --dbg_backtrace                         false
% 1.77/0.98  --dbg_dump_prop_clauses                 false
% 1.77/0.98  --dbg_dump_prop_clauses_file            -
% 1.77/0.98  --dbg_out_stat                          false
% 1.77/0.98  ------ Parsing...
% 1.77/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.77/0.98  
% 1.77/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.77/0.98  
% 1.77/0.98  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.77/0.98  
% 1.77/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.77/0.98  ------ Proving...
% 1.77/0.98  ------ Problem Properties 
% 1.77/0.98  
% 1.77/0.98  
% 1.77/0.98  clauses                                 19
% 1.77/0.98  conjectures                             6
% 1.77/0.98  EPR                                     6
% 1.77/0.98  Horn                                    14
% 1.77/0.98  unary                                   2
% 1.77/0.98  binary                                  7
% 1.77/0.98  lits                                    50
% 1.77/0.98  lits eq                                 11
% 1.77/0.98  fd_pure                                 0
% 1.77/0.98  fd_pseudo                               0
% 1.77/0.98  fd_cond                                 0
% 1.77/0.98  fd_pseudo_cond                          2
% 1.77/0.98  AC symbols                              0
% 1.77/0.98  
% 1.77/0.98  ------ Schedule dynamic 5 is on 
% 1.77/0.98  
% 1.77/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.77/0.98  
% 1.77/0.98  
% 1.77/0.98  ------ 
% 1.77/0.98  Current options:
% 1.77/0.98  ------ 
% 1.77/0.98  
% 1.77/0.98  ------ Input Options
% 1.77/0.98  
% 1.77/0.98  --out_options                           all
% 1.77/0.98  --tptp_safe_out                         true
% 1.77/0.98  --problem_path                          ""
% 1.77/0.98  --include_path                          ""
% 1.77/0.98  --clausifier                            res/vclausify_rel
% 1.77/0.98  --clausifier_options                    --mode clausify
% 1.77/0.98  --stdin                                 false
% 1.77/0.98  --stats_out                             all
% 1.77/0.98  
% 1.77/0.98  ------ General Options
% 1.77/0.98  
% 1.77/0.98  --fof                                   false
% 1.77/0.98  --time_out_real                         305.
% 1.77/0.98  --time_out_virtual                      -1.
% 1.77/0.98  --symbol_type_check                     false
% 1.77/0.98  --clausify_out                          false
% 1.77/0.98  --sig_cnt_out                           false
% 1.77/0.98  --trig_cnt_out                          false
% 1.77/0.98  --trig_cnt_out_tolerance                1.
% 1.77/0.98  --trig_cnt_out_sk_spl                   false
% 1.77/0.98  --abstr_cl_out                          false
% 1.77/0.98  
% 1.77/0.98  ------ Global Options
% 1.77/0.98  
% 1.77/0.98  --schedule                              default
% 1.77/0.98  --add_important_lit                     false
% 1.77/0.98  --prop_solver_per_cl                    1000
% 1.77/0.98  --min_unsat_core                        false
% 1.77/0.98  --soft_assumptions                      false
% 1.77/0.98  --soft_lemma_size                       3
% 1.77/0.98  --prop_impl_unit_size                   0
% 1.77/0.98  --prop_impl_unit                        []
% 1.77/0.98  --share_sel_clauses                     true
% 1.77/0.98  --reset_solvers                         false
% 1.77/0.98  --bc_imp_inh                            [conj_cone]
% 1.77/0.98  --conj_cone_tolerance                   3.
% 1.77/0.98  --extra_neg_conj                        none
% 1.77/0.98  --large_theory_mode                     true
% 1.77/0.98  --prolific_symb_bound                   200
% 1.77/0.98  --lt_threshold                          2000
% 1.77/0.98  --clause_weak_htbl                      true
% 1.77/0.98  --gc_record_bc_elim                     false
% 1.77/0.98  
% 1.77/0.98  ------ Preprocessing Options
% 1.77/0.98  
% 1.77/0.98  --preprocessing_flag                    true
% 1.77/0.98  --time_out_prep_mult                    0.1
% 1.77/0.98  --splitting_mode                        input
% 1.77/0.98  --splitting_grd                         true
% 1.77/0.98  --splitting_cvd                         false
% 1.77/0.98  --splitting_cvd_svl                     false
% 1.77/0.98  --splitting_nvd                         32
% 1.77/0.98  --sub_typing                            true
% 1.77/0.98  --prep_gs_sim                           true
% 1.77/0.98  --prep_unflatten                        true
% 1.77/0.98  --prep_res_sim                          true
% 1.77/0.98  --prep_upred                            true
% 1.77/0.98  --prep_sem_filter                       exhaustive
% 1.77/0.98  --prep_sem_filter_out                   false
% 1.77/0.98  --pred_elim                             true
% 1.77/0.98  --res_sim_input                         true
% 1.77/0.98  --eq_ax_congr_red                       true
% 1.77/0.98  --pure_diseq_elim                       true
% 1.77/0.98  --brand_transform                       false
% 1.77/0.98  --non_eq_to_eq                          false
% 1.77/0.98  --prep_def_merge                        true
% 1.77/0.98  --prep_def_merge_prop_impl              false
% 1.77/0.98  --prep_def_merge_mbd                    true
% 1.77/0.98  --prep_def_merge_tr_red                 false
% 1.77/0.98  --prep_def_merge_tr_cl                  false
% 1.77/0.98  --smt_preprocessing                     true
% 1.77/0.98  --smt_ac_axioms                         fast
% 1.77/0.98  --preprocessed_out                      false
% 1.77/0.98  --preprocessed_stats                    false
% 1.77/0.98  
% 1.77/0.98  ------ Abstraction refinement Options
% 1.77/0.98  
% 1.77/0.98  --abstr_ref                             []
% 1.77/0.98  --abstr_ref_prep                        false
% 1.77/0.98  --abstr_ref_until_sat                   false
% 1.77/0.98  --abstr_ref_sig_restrict                funpre
% 1.77/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.77/0.98  --abstr_ref_under                       []
% 1.77/0.98  
% 1.77/0.98  ------ SAT Options
% 1.77/0.98  
% 1.77/0.98  --sat_mode                              false
% 1.77/0.98  --sat_fm_restart_options                ""
% 1.77/0.98  --sat_gr_def                            false
% 1.77/0.98  --sat_epr_types                         true
% 1.77/0.98  --sat_non_cyclic_types                  false
% 1.77/0.98  --sat_finite_models                     false
% 1.77/0.98  --sat_fm_lemmas                         false
% 1.77/0.98  --sat_fm_prep                           false
% 1.77/0.98  --sat_fm_uc_incr                        true
% 1.77/0.98  --sat_out_model                         small
% 1.77/0.98  --sat_out_clauses                       false
% 1.77/0.98  
% 1.77/0.98  ------ QBF Options
% 1.77/0.98  
% 1.77/0.98  --qbf_mode                              false
% 1.77/0.98  --qbf_elim_univ                         false
% 1.77/0.98  --qbf_dom_inst                          none
% 1.77/0.98  --qbf_dom_pre_inst                      false
% 1.77/0.98  --qbf_sk_in                             false
% 1.77/0.98  --qbf_pred_elim                         true
% 1.77/0.98  --qbf_split                             512
% 1.77/0.98  
% 1.77/0.98  ------ BMC1 Options
% 1.77/0.98  
% 1.77/0.98  --bmc1_incremental                      false
% 1.77/0.98  --bmc1_axioms                           reachable_all
% 1.77/0.98  --bmc1_min_bound                        0
% 1.77/0.98  --bmc1_max_bound                        -1
% 1.77/0.98  --bmc1_max_bound_default                -1
% 1.77/0.98  --bmc1_symbol_reachability              true
% 1.77/0.98  --bmc1_property_lemmas                  false
% 1.77/0.98  --bmc1_k_induction                      false
% 1.77/0.98  --bmc1_non_equiv_states                 false
% 1.77/0.98  --bmc1_deadlock                         false
% 1.77/0.98  --bmc1_ucm                              false
% 1.77/0.98  --bmc1_add_unsat_core                   none
% 1.77/0.98  --bmc1_unsat_core_children              false
% 1.77/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.77/0.98  --bmc1_out_stat                         full
% 1.77/0.98  --bmc1_ground_init                      false
% 1.77/0.98  --bmc1_pre_inst_next_state              false
% 1.77/0.98  --bmc1_pre_inst_state                   false
% 1.77/0.98  --bmc1_pre_inst_reach_state             false
% 1.77/0.98  --bmc1_out_unsat_core                   false
% 1.77/0.98  --bmc1_aig_witness_out                  false
% 1.77/0.98  --bmc1_verbose                          false
% 1.77/0.98  --bmc1_dump_clauses_tptp                false
% 1.77/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.77/0.98  --bmc1_dump_file                        -
% 1.77/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.77/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.77/0.98  --bmc1_ucm_extend_mode                  1
% 1.77/0.98  --bmc1_ucm_init_mode                    2
% 1.77/0.98  --bmc1_ucm_cone_mode                    none
% 1.77/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.77/0.98  --bmc1_ucm_relax_model                  4
% 1.77/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.77/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.77/0.98  --bmc1_ucm_layered_model                none
% 1.77/0.98  --bmc1_ucm_max_lemma_size               10
% 1.77/0.98  
% 1.77/0.98  ------ AIG Options
% 1.77/0.98  
% 1.77/0.98  --aig_mode                              false
% 1.77/0.98  
% 1.77/0.98  ------ Instantiation Options
% 1.77/0.98  
% 1.77/0.98  --instantiation_flag                    true
% 1.77/0.98  --inst_sos_flag                         false
% 1.77/0.98  --inst_sos_phase                        true
% 1.77/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.77/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.77/0.98  --inst_lit_sel_side                     none
% 1.77/0.98  --inst_solver_per_active                1400
% 1.77/0.98  --inst_solver_calls_frac                1.
% 1.77/0.98  --inst_passive_queue_type               priority_queues
% 1.77/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.77/0.98  --inst_passive_queues_freq              [25;2]
% 1.77/0.98  --inst_dismatching                      true
% 1.77/0.98  --inst_eager_unprocessed_to_passive     true
% 1.77/0.98  --inst_prop_sim_given                   true
% 1.77/0.98  --inst_prop_sim_new                     false
% 1.77/0.98  --inst_subs_new                         false
% 1.77/0.98  --inst_eq_res_simp                      false
% 1.77/0.98  --inst_subs_given                       false
% 1.77/0.98  --inst_orphan_elimination               true
% 1.77/0.98  --inst_learning_loop_flag               true
% 1.77/0.98  --inst_learning_start                   3000
% 1.77/0.98  --inst_learning_factor                  2
% 1.77/0.98  --inst_start_prop_sim_after_learn       3
% 1.77/0.98  --inst_sel_renew                        solver
% 1.77/0.98  --inst_lit_activity_flag                true
% 1.77/0.98  --inst_restr_to_given                   false
% 1.77/0.98  --inst_activity_threshold               500
% 1.77/0.98  --inst_out_proof                        true
% 1.77/0.98  
% 1.77/0.98  ------ Resolution Options
% 1.77/0.98  
% 1.77/0.98  --resolution_flag                       false
% 1.77/0.98  --res_lit_sel                           adaptive
% 1.77/0.98  --res_lit_sel_side                      none
% 1.77/0.98  --res_ordering                          kbo
% 1.77/0.98  --res_to_prop_solver                    active
% 1.77/0.98  --res_prop_simpl_new                    false
% 1.77/0.98  --res_prop_simpl_given                  true
% 1.77/0.98  --res_passive_queue_type                priority_queues
% 1.77/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.77/0.98  --res_passive_queues_freq               [15;5]
% 1.77/0.98  --res_forward_subs                      full
% 1.77/0.98  --res_backward_subs                     full
% 1.77/0.98  --res_forward_subs_resolution           true
% 1.77/0.98  --res_backward_subs_resolution          true
% 1.77/0.98  --res_orphan_elimination                true
% 1.77/0.98  --res_time_limit                        2.
% 1.77/0.98  --res_out_proof                         true
% 1.77/0.98  
% 1.77/0.98  ------ Superposition Options
% 1.77/0.98  
% 1.77/0.98  --superposition_flag                    true
% 1.77/0.98  --sup_passive_queue_type                priority_queues
% 1.77/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.77/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.77/0.98  --demod_completeness_check              fast
% 1.77/0.98  --demod_use_ground                      true
% 1.77/0.98  --sup_to_prop_solver                    passive
% 1.77/0.98  --sup_prop_simpl_new                    true
% 1.77/0.98  --sup_prop_simpl_given                  true
% 1.77/0.98  --sup_fun_splitting                     false
% 1.77/0.98  --sup_smt_interval                      50000
% 1.77/0.98  
% 1.77/0.98  ------ Superposition Simplification Setup
% 1.77/0.98  
% 1.77/0.98  --sup_indices_passive                   []
% 1.77/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.77/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.77/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.77/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.77/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.77/0.98  --sup_full_bw                           [BwDemod]
% 1.77/0.98  --sup_immed_triv                        [TrivRules]
% 1.77/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.77/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.77/0.98  --sup_immed_bw_main                     []
% 1.77/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.77/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.77/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.77/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.77/0.98  
% 1.77/0.98  ------ Combination Options
% 1.77/0.98  
% 1.77/0.98  --comb_res_mult                         3
% 1.77/0.98  --comb_sup_mult                         2
% 1.77/0.98  --comb_inst_mult                        10
% 1.77/0.98  
% 1.77/0.98  ------ Debug Options
% 1.77/0.98  
% 1.77/0.98  --dbg_backtrace                         false
% 1.77/0.98  --dbg_dump_prop_clauses                 false
% 1.77/0.98  --dbg_dump_prop_clauses_file            -
% 1.77/0.98  --dbg_out_stat                          false
% 1.77/0.98  
% 1.77/0.98  
% 1.77/0.98  
% 1.77/0.98  
% 1.77/0.98  ------ Proving...
% 1.77/0.98  
% 1.77/0.98  
% 1.77/0.98  % SZS status Theorem for theBenchmark.p
% 1.77/0.98  
% 1.77/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.77/0.98  
% 1.77/0.98  fof(f3,axiom,(
% 1.77/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 1.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.77/0.98  
% 1.77/0.98  fof(f12,plain,(
% 1.77/0.98    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.77/0.98    inference(ennf_transformation,[],[f3])).
% 1.77/0.98  
% 1.77/0.98  fof(f13,plain,(
% 1.77/0.98    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.77/0.98    inference(flattening,[],[f12])).
% 1.77/0.98  
% 1.77/0.98  fof(f22,plain,(
% 1.77/0.98    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.77/0.98    inference(nnf_transformation,[],[f13])).
% 1.77/0.98  
% 1.77/0.98  fof(f23,plain,(
% 1.77/0.98    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.77/0.98    inference(rectify,[],[f22])).
% 1.77/0.98  
% 1.77/0.98  fof(f24,plain,(
% 1.77/0.98    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0))))),
% 1.77/0.98    introduced(choice_axiom,[])).
% 1.77/0.98  
% 1.77/0.98  fof(f25,plain,(
% 1.77/0.98    ! [X0] : (((v2_funct_1(X0) | (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.77/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).
% 1.77/0.98  
% 1.77/0.98  fof(f37,plain,(
% 1.77/0.98    ( ! [X0] : (v2_funct_1(X0) | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.77/0.98    inference(cnf_transformation,[],[f25])).
% 1.77/0.98  
% 1.77/0.98  fof(f9,conjecture,(
% 1.77/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 1.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.77/0.98  
% 1.77/0.98  fof(f10,negated_conjecture,(
% 1.77/0.98    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 1.77/0.98    inference(negated_conjecture,[],[f9])).
% 1.77/0.98  
% 1.77/0.98  fof(f20,plain,(
% 1.77/0.98    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.77/0.98    inference(ennf_transformation,[],[f10])).
% 1.77/0.98  
% 1.77/0.98  fof(f21,plain,(
% 1.77/0.98    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.77/0.98    inference(flattening,[],[f20])).
% 1.77/0.98  
% 1.77/0.98  fof(f26,plain,(
% 1.77/0.98    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.77/0.98    inference(nnf_transformation,[],[f21])).
% 1.77/0.98  
% 1.77/0.98  fof(f27,plain,(
% 1.77/0.98    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.77/0.98    inference(flattening,[],[f26])).
% 1.77/0.98  
% 1.77/0.98  fof(f28,plain,(
% 1.77/0.98    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.77/0.98    inference(rectify,[],[f27])).
% 1.77/0.98  
% 1.77/0.98  fof(f30,plain,(
% 1.77/0.98    ( ! [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (sK4 != sK5 & k1_funct_1(X1,sK4) = k1_funct_1(X1,sK5) & r2_hidden(sK5,X0) & r2_hidden(sK4,X0))) )),
% 1.77/0.98    introduced(choice_axiom,[])).
% 1.77/0.98  
% 1.77/0.98  fof(f29,plain,(
% 1.77/0.98    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3) & r2_hidden(X3,sK2) & r2_hidden(X2,sK2)) | ~v2_funct_1(sK3)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 1.77/0.98    introduced(choice_axiom,[])).
% 1.77/0.98  
% 1.77/0.98  fof(f31,plain,(
% 1.77/0.98    ((sK4 != sK5 & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) & r2_hidden(sK5,sK2) & r2_hidden(sK4,sK2)) | ~v2_funct_1(sK3)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 1.77/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f28,f30,f29])).
% 1.77/0.98  
% 1.77/0.98  fof(f44,plain,(
% 1.77/0.98    v1_funct_1(sK3)),
% 1.77/0.98    inference(cnf_transformation,[],[f31])).
% 1.77/0.98  
% 1.77/0.98  fof(f46,plain,(
% 1.77/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 1.77/0.98    inference(cnf_transformation,[],[f31])).
% 1.77/0.98  
% 1.77/0.98  fof(f38,plain,(
% 1.77/0.98    ( ! [X0] : (v2_funct_1(X0) | sK0(X0) != sK1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.77/0.98    inference(cnf_transformation,[],[f25])).
% 1.77/0.98  
% 1.77/0.98  fof(f5,axiom,(
% 1.77/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.77/0.98  
% 1.77/0.98  fof(f15,plain,(
% 1.77/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.77/0.98    inference(ennf_transformation,[],[f5])).
% 1.77/0.98  
% 1.77/0.98  fof(f40,plain,(
% 1.77/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.77/0.98    inference(cnf_transformation,[],[f15])).
% 1.77/0.98  
% 1.77/0.98  fof(f47,plain,(
% 1.77/0.98    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2) | v2_funct_1(sK3)) )),
% 1.77/0.98    inference(cnf_transformation,[],[f31])).
% 1.77/0.98  
% 1.77/0.98  fof(f35,plain,(
% 1.77/0.98    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK0(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.77/0.98    inference(cnf_transformation,[],[f25])).
% 1.77/0.98  
% 1.77/0.98  fof(f7,axiom,(
% 1.77/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.77/0.98  
% 1.77/0.98  fof(f17,plain,(
% 1.77/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.77/0.98    inference(ennf_transformation,[],[f7])).
% 1.77/0.98  
% 1.77/0.98  fof(f42,plain,(
% 1.77/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.77/0.98    inference(cnf_transformation,[],[f17])).
% 1.77/0.98  
% 1.77/0.98  fof(f6,axiom,(
% 1.77/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.77/0.98  
% 1.77/0.98  fof(f16,plain,(
% 1.77/0.98    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.77/0.98    inference(ennf_transformation,[],[f6])).
% 1.77/0.98  
% 1.77/0.98  fof(f41,plain,(
% 1.77/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.77/0.98    inference(cnf_transformation,[],[f16])).
% 1.77/0.98  
% 1.77/0.98  fof(f2,axiom,(
% 1.77/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.77/0.98  
% 1.77/0.98  fof(f11,plain,(
% 1.77/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.77/0.98    inference(ennf_transformation,[],[f2])).
% 1.77/0.98  
% 1.77/0.98  fof(f33,plain,(
% 1.77/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.77/0.98    inference(cnf_transformation,[],[f11])).
% 1.77/0.98  
% 1.77/0.98  fof(f36,plain,(
% 1.77/0.98    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK1(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.77/0.98    inference(cnf_transformation,[],[f25])).
% 1.77/0.98  
% 1.77/0.98  fof(f50,plain,(
% 1.77/0.98    k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) | ~v2_funct_1(sK3)),
% 1.77/0.98    inference(cnf_transformation,[],[f31])).
% 1.77/0.98  
% 1.77/0.98  fof(f49,plain,(
% 1.77/0.98    r2_hidden(sK5,sK2) | ~v2_funct_1(sK3)),
% 1.77/0.98    inference(cnf_transformation,[],[f31])).
% 1.77/0.98  
% 1.77/0.98  fof(f8,axiom,(
% 1.77/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 1.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.77/0.98  
% 1.77/0.98  fof(f18,plain,(
% 1.77/0.98    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.77/0.98    inference(ennf_transformation,[],[f8])).
% 1.77/0.98  
% 1.77/0.98  fof(f19,plain,(
% 1.77/0.98    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.77/0.98    inference(flattening,[],[f18])).
% 1.77/0.98  
% 1.77/0.98  fof(f43,plain,(
% 1.77/0.98    ( ! [X2,X0,X3,X1] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.77/0.98    inference(cnf_transformation,[],[f19])).
% 1.77/0.98  
% 1.77/0.98  fof(f45,plain,(
% 1.77/0.98    v1_funct_2(sK3,sK2,sK2)),
% 1.77/0.98    inference(cnf_transformation,[],[f31])).
% 1.77/0.98  
% 1.77/0.98  fof(f48,plain,(
% 1.77/0.98    r2_hidden(sK4,sK2) | ~v2_funct_1(sK3)),
% 1.77/0.98    inference(cnf_transformation,[],[f31])).
% 1.77/0.98  
% 1.77/0.98  fof(f1,axiom,(
% 1.77/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.77/0.98  
% 1.77/0.98  fof(f32,plain,(
% 1.77/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.77/0.98    inference(cnf_transformation,[],[f1])).
% 1.77/0.98  
% 1.77/0.98  fof(f4,axiom,(
% 1.77/0.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.77/0.98  
% 1.77/0.98  fof(f14,plain,(
% 1.77/0.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.77/0.98    inference(ennf_transformation,[],[f4])).
% 1.77/0.98  
% 1.77/0.98  fof(f39,plain,(
% 1.77/0.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.77/0.98    inference(cnf_transformation,[],[f14])).
% 1.77/0.98  
% 1.77/0.98  fof(f51,plain,(
% 1.77/0.98    sK4 != sK5 | ~v2_funct_1(sK3)),
% 1.77/0.98    inference(cnf_transformation,[],[f31])).
% 1.77/0.98  
% 1.77/0.98  cnf(c_3,plain,
% 1.77/0.98      ( ~ v1_relat_1(X0)
% 1.77/0.98      | ~ v1_funct_1(X0)
% 1.77/0.98      | v2_funct_1(X0)
% 1.77/0.98      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
% 1.77/0.98      inference(cnf_transformation,[],[f37]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_19,negated_conjecture,
% 1.77/0.98      ( v1_funct_1(sK3) ),
% 1.77/0.98      inference(cnf_transformation,[],[f44]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_290,plain,
% 1.77/0.98      ( ~ v1_relat_1(X0)
% 1.77/0.98      | v2_funct_1(X0)
% 1.77/0.98      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
% 1.77/0.98      | sK3 != X0 ),
% 1.77/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_19]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_291,plain,
% 1.77/0.98      ( ~ v1_relat_1(sK3)
% 1.77/0.98      | v2_funct_1(sK3)
% 1.77/0.98      | k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
% 1.77/0.98      inference(unflattening,[status(thm)],[c_290]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_1914,plain,
% 1.77/0.98      ( ~ v1_relat_1(sK3)
% 1.77/0.98      | v2_funct_1(sK3)
% 1.77/0.98      | k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
% 1.77/0.98      inference(subtyping,[status(esa)],[c_291]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_2318,plain,
% 1.77/0.98      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
% 1.77/0.98      | v1_relat_1(sK3) != iProver_top
% 1.77/0.98      | v2_funct_1(sK3) = iProver_top ),
% 1.77/0.98      inference(predicate_to_equality,[status(thm)],[c_1914]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_17,negated_conjecture,
% 1.77/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 1.77/0.98      inference(cnf_transformation,[],[f46]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_22,plain,
% 1.77/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 1.77/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_1986,plain,
% 1.77/0.98      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
% 1.77/0.98      | v1_relat_1(sK3) != iProver_top
% 1.77/0.98      | v2_funct_1(sK3) = iProver_top ),
% 1.77/0.98      inference(predicate_to_equality,[status(thm)],[c_1914]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_2,plain,
% 1.77/0.98      ( ~ v1_relat_1(X0)
% 1.77/0.98      | ~ v1_funct_1(X0)
% 1.77/0.98      | v2_funct_1(X0)
% 1.77/0.98      | sK1(X0) != sK0(X0) ),
% 1.77/0.98      inference(cnf_transformation,[],[f38]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_303,plain,
% 1.77/0.98      ( ~ v1_relat_1(X0)
% 1.77/0.98      | v2_funct_1(X0)
% 1.77/0.98      | sK1(X0) != sK0(X0)
% 1.77/0.98      | sK3 != X0 ),
% 1.77/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_19]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_304,plain,
% 1.77/0.98      ( ~ v1_relat_1(sK3) | v2_funct_1(sK3) | sK1(sK3) != sK0(sK3) ),
% 1.77/0.98      inference(unflattening,[status(thm)],[c_303]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_1913,plain,
% 1.77/0.98      ( ~ v1_relat_1(sK3) | v2_funct_1(sK3) | sK1(sK3) != sK0(sK3) ),
% 1.77/0.98      inference(subtyping,[status(esa)],[c_304]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_1987,plain,
% 1.77/0.98      ( sK1(sK3) != sK0(sK3)
% 1.77/0.98      | v1_relat_1(sK3) != iProver_top
% 1.77/0.98      | v2_funct_1(sK3) = iProver_top ),
% 1.77/0.98      inference(predicate_to_equality,[status(thm)],[c_1913]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_8,plain,
% 1.77/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.77/0.98      | v1_relat_1(X0) ),
% 1.77/0.98      inference(cnf_transformation,[],[f40]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_1927,plain,
% 1.77/0.98      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 1.77/0.98      | v1_relat_1(X0_49) ),
% 1.77/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_2469,plain,
% 1.77/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 1.77/0.98      | v1_relat_1(sK3) ),
% 1.77/0.98      inference(instantiation,[status(thm)],[c_1927]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_2470,plain,
% 1.77/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 1.77/0.98      | v1_relat_1(sK3) = iProver_top ),
% 1.77/0.98      inference(predicate_to_equality,[status(thm)],[c_2469]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_16,negated_conjecture,
% 1.77/0.98      ( ~ r2_hidden(X0,sK2)
% 1.77/0.98      | ~ r2_hidden(X1,sK2)
% 1.77/0.98      | v2_funct_1(sK3)
% 1.77/0.98      | X1 = X0
% 1.77/0.98      | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
% 1.77/0.98      inference(cnf_transformation,[],[f47]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_1920,negated_conjecture,
% 1.77/0.98      ( ~ r2_hidden(X0_48,sK2)
% 1.77/0.98      | ~ r2_hidden(X1_48,sK2)
% 1.77/0.98      | v2_funct_1(sK3)
% 1.77/0.98      | X1_48 = X0_48
% 1.77/0.98      | k1_funct_1(sK3,X1_48) != k1_funct_1(sK3,X0_48) ),
% 1.77/0.98      inference(subtyping,[status(esa)],[c_16]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_2500,plain,
% 1.77/0.98      ( ~ r2_hidden(sK1(sK3),sK2)
% 1.77/0.98      | ~ r2_hidden(sK0(sK3),sK2)
% 1.77/0.98      | v2_funct_1(sK3)
% 1.77/0.98      | k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
% 1.77/0.98      | sK1(sK3) = sK0(sK3) ),
% 1.77/0.98      inference(instantiation,[status(thm)],[c_1920]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_2501,plain,
% 1.77/0.98      ( k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
% 1.77/0.98      | sK1(sK3) = sK0(sK3)
% 1.77/0.98      | r2_hidden(sK1(sK3),sK2) != iProver_top
% 1.77/0.98      | r2_hidden(sK0(sK3),sK2) != iProver_top
% 1.77/0.98      | v2_funct_1(sK3) = iProver_top ),
% 1.77/0.98      inference(predicate_to_equality,[status(thm)],[c_2500]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_5,plain,
% 1.77/0.98      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 1.77/0.98      | ~ v1_relat_1(X0)
% 1.77/0.98      | ~ v1_funct_1(X0)
% 1.77/0.98      | v2_funct_1(X0) ),
% 1.77/0.98      inference(cnf_transformation,[],[f35]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_264,plain,
% 1.77/0.98      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 1.77/0.98      | ~ v1_relat_1(X0)
% 1.77/0.98      | v2_funct_1(X0)
% 1.77/0.98      | sK3 != X0 ),
% 1.77/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_19]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_265,plain,
% 1.77/0.98      ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 1.77/0.98      | ~ v1_relat_1(sK3)
% 1.77/0.98      | v2_funct_1(sK3) ),
% 1.77/0.98      inference(unflattening,[status(thm)],[c_264]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_1916,plain,
% 1.77/0.98      ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 1.77/0.98      | ~ v1_relat_1(sK3)
% 1.77/0.98      | v2_funct_1(sK3) ),
% 1.77/0.98      inference(subtyping,[status(esa)],[c_265]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_2316,plain,
% 1.77/0.98      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 1.77/0.98      | v1_relat_1(sK3) != iProver_top
% 1.77/0.98      | v2_funct_1(sK3) = iProver_top ),
% 1.77/0.98      inference(predicate_to_equality,[status(thm)],[c_1916]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_266,plain,
% 1.77/0.98      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 1.77/0.98      | v1_relat_1(sK3) != iProver_top
% 1.77/0.98      | v2_funct_1(sK3) = iProver_top ),
% 1.77/0.98      inference(predicate_to_equality,[status(thm)],[c_265]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_3198,plain,
% 1.77/0.98      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 1.77/0.98      | v2_funct_1(sK3) = iProver_top ),
% 1.77/0.98      inference(global_propositional_subsumption,
% 1.77/0.98                [status(thm)],
% 1.77/0.98                [c_2316,c_22,c_266,c_2470]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_1919,negated_conjecture,
% 1.77/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 1.77/0.98      inference(subtyping,[status(esa)],[c_17]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_2312,plain,
% 1.77/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 1.77/0.98      inference(predicate_to_equality,[status(thm)],[c_1919]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_10,plain,
% 1.77/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.77/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.77/0.98      inference(cnf_transformation,[],[f42]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_1925,plain,
% 1.77/0.98      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 1.77/0.98      | k1_relset_1(X1_49,X2_49,X0_49) = k1_relat_1(X0_49) ),
% 1.77/0.98      inference(subtyping,[status(esa)],[c_10]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_2306,plain,
% 1.77/0.98      ( k1_relset_1(X0_49,X1_49,X2_49) = k1_relat_1(X2_49)
% 1.77/0.98      | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
% 1.77/0.98      inference(predicate_to_equality,[status(thm)],[c_1925]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_2681,plain,
% 1.77/0.98      ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
% 1.77/0.98      inference(superposition,[status(thm)],[c_2312,c_2306]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_9,plain,
% 1.77/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.77/0.98      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 1.77/0.98      inference(cnf_transformation,[],[f41]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_1926,plain,
% 1.77/0.98      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 1.77/0.98      | m1_subset_1(k1_relset_1(X1_49,X2_49,X0_49),k1_zfmisc_1(X1_49)) ),
% 1.77/0.98      inference(subtyping,[status(esa)],[c_9]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_2305,plain,
% 1.77/0.98      ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))) != iProver_top
% 1.77/0.98      | m1_subset_1(k1_relset_1(X1_49,X2_49,X0_49),k1_zfmisc_1(X1_49)) = iProver_top ),
% 1.77/0.98      inference(predicate_to_equality,[status(thm)],[c_1926]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_2740,plain,
% 1.77/0.98      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
% 1.77/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
% 1.77/0.98      inference(superposition,[status(thm)],[c_2681,c_2305]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_3010,plain,
% 1.77/0.98      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top ),
% 1.77/0.98      inference(global_propositional_subsumption,
% 1.77/0.98                [status(thm)],
% 1.77/0.98                [c_2740,c_22]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_1,plain,
% 1.77/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.77/0.98      | ~ r2_hidden(X2,X0)
% 1.77/0.98      | r2_hidden(X2,X1) ),
% 1.77/0.98      inference(cnf_transformation,[],[f33]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_1928,plain,
% 1.77/0.98      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(X1_49))
% 1.77/0.98      | ~ r2_hidden(X0_48,X0_49)
% 1.77/0.98      | r2_hidden(X0_48,X1_49) ),
% 1.77/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_2303,plain,
% 1.77/0.98      ( m1_subset_1(X0_49,k1_zfmisc_1(X1_49)) != iProver_top
% 1.77/0.98      | r2_hidden(X0_48,X0_49) != iProver_top
% 1.77/0.98      | r2_hidden(X0_48,X1_49) = iProver_top ),
% 1.77/0.98      inference(predicate_to_equality,[status(thm)],[c_1928]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_3015,plain,
% 1.77/0.98      ( r2_hidden(X0_48,k1_relat_1(sK3)) != iProver_top
% 1.77/0.98      | r2_hidden(X0_48,sK2) = iProver_top ),
% 1.77/0.98      inference(superposition,[status(thm)],[c_3010,c_2303]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_3204,plain,
% 1.77/0.98      ( r2_hidden(sK0(sK3),sK2) = iProver_top
% 1.77/0.98      | v2_funct_1(sK3) = iProver_top ),
% 1.77/0.98      inference(superposition,[status(thm)],[c_3198,c_3015]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_4,plain,
% 1.77/0.98      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 1.77/0.98      | ~ v1_relat_1(X0)
% 1.77/0.98      | ~ v1_funct_1(X0)
% 1.77/0.98      | v2_funct_1(X0) ),
% 1.77/0.98      inference(cnf_transformation,[],[f36]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_277,plain,
% 1.77/0.98      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 1.77/0.98      | ~ v1_relat_1(X0)
% 1.77/0.98      | v2_funct_1(X0)
% 1.77/0.98      | sK3 != X0 ),
% 1.77/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_19]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_278,plain,
% 1.77/0.98      ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 1.77/0.98      | ~ v1_relat_1(sK3)
% 1.77/0.98      | v2_funct_1(sK3) ),
% 1.77/0.98      inference(unflattening,[status(thm)],[c_277]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_1915,plain,
% 1.77/0.98      ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 1.77/0.98      | ~ v1_relat_1(sK3)
% 1.77/0.98      | v2_funct_1(sK3) ),
% 1.77/0.98      inference(subtyping,[status(esa)],[c_278]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_2317,plain,
% 1.77/0.98      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
% 1.77/0.98      | v1_relat_1(sK3) != iProver_top
% 1.77/0.98      | v2_funct_1(sK3) = iProver_top ),
% 1.77/0.98      inference(predicate_to_equality,[status(thm)],[c_1915]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_279,plain,
% 1.77/0.98      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
% 1.77/0.98      | v1_relat_1(sK3) != iProver_top
% 1.77/0.98      | v2_funct_1(sK3) = iProver_top ),
% 1.77/0.98      inference(predicate_to_equality,[status(thm)],[c_278]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_3220,plain,
% 1.77/0.98      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
% 1.77/0.98      | v2_funct_1(sK3) = iProver_top ),
% 1.77/0.98      inference(global_propositional_subsumption,
% 1.77/0.98                [status(thm)],
% 1.77/0.98                [c_2317,c_22,c_279,c_2470]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_3226,plain,
% 1.77/0.98      ( r2_hidden(sK1(sK3),sK2) = iProver_top
% 1.77/0.98      | v2_funct_1(sK3) = iProver_top ),
% 1.77/0.98      inference(superposition,[status(thm)],[c_3220,c_3015]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_3229,plain,
% 1.77/0.98      ( v2_funct_1(sK3) = iProver_top ),
% 1.77/0.98      inference(global_propositional_subsumption,
% 1.77/0.98                [status(thm)],
% 1.77/0.98                [c_2318,c_22,c_1986,c_1987,c_2470,c_2501,c_3204,c_3226]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_13,negated_conjecture,
% 1.77/0.98      ( ~ v2_funct_1(sK3) | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
% 1.77/0.98      inference(cnf_transformation,[],[f50]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_1923,negated_conjecture,
% 1.77/0.98      ( ~ v2_funct_1(sK3) | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
% 1.77/0.98      inference(subtyping,[status(esa)],[c_13]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_2308,plain,
% 1.77/0.98      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
% 1.77/0.98      | v2_funct_1(sK3) != iProver_top ),
% 1.77/0.98      inference(predicate_to_equality,[status(thm)],[c_1923]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_3238,plain,
% 1.77/0.98      ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
% 1.77/0.98      inference(superposition,[status(thm)],[c_3229,c_2308]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_14,negated_conjecture,
% 1.77/0.98      ( r2_hidden(sK5,sK2) | ~ v2_funct_1(sK3) ),
% 1.77/0.98      inference(cnf_transformation,[],[f49]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_1922,negated_conjecture,
% 1.77/0.98      ( r2_hidden(sK5,sK2) | ~ v2_funct_1(sK3) ),
% 1.77/0.98      inference(subtyping,[status(esa)],[c_14]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_2309,plain,
% 1.77/0.98      ( r2_hidden(sK5,sK2) = iProver_top
% 1.77/0.98      | v2_funct_1(sK3) != iProver_top ),
% 1.77/0.98      inference(predicate_to_equality,[status(thm)],[c_1922]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_11,plain,
% 1.77/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.77/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.77/0.98      | ~ r2_hidden(X3,X1)
% 1.77/0.98      | ~ v1_funct_1(X0)
% 1.77/0.98      | ~ v2_funct_1(X0)
% 1.77/0.98      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
% 1.77/0.98      | k1_xboole_0 = X2 ),
% 1.77/0.98      inference(cnf_transformation,[],[f43]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_18,negated_conjecture,
% 1.77/0.98      ( v1_funct_2(sK3,sK2,sK2) ),
% 1.77/0.98      inference(cnf_transformation,[],[f45]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_235,plain,
% 1.77/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.77/0.98      | ~ r2_hidden(X3,X1)
% 1.77/0.98      | ~ v1_funct_1(X0)
% 1.77/0.98      | ~ v2_funct_1(X0)
% 1.77/0.98      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
% 1.77/0.98      | sK2 != X2
% 1.77/0.98      | sK2 != X1
% 1.77/0.98      | sK3 != X0
% 1.77/0.98      | k1_xboole_0 = X2 ),
% 1.77/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_236,plain,
% 1.77/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 1.77/0.98      | ~ r2_hidden(X0,sK2)
% 1.77/0.98      | ~ v1_funct_1(sK3)
% 1.77/0.98      | ~ v2_funct_1(sK3)
% 1.77/0.98      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 1.77/0.98      | k1_xboole_0 = sK2 ),
% 1.77/0.98      inference(unflattening,[status(thm)],[c_235]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_240,plain,
% 1.77/0.98      ( ~ r2_hidden(X0,sK2)
% 1.77/0.98      | ~ v2_funct_1(sK3)
% 1.77/0.98      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 1.77/0.98      | k1_xboole_0 = sK2 ),
% 1.77/0.98      inference(global_propositional_subsumption,
% 1.77/0.98                [status(thm)],
% 1.77/0.98                [c_236,c_19,c_17]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_1917,plain,
% 1.77/0.98      ( ~ r2_hidden(X0_48,sK2)
% 1.77/0.98      | ~ v2_funct_1(sK3)
% 1.77/0.98      | k1_xboole_0 = sK2
% 1.77/0.98      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0_48)) = X0_48 ),
% 1.77/0.98      inference(subtyping,[status(esa)],[c_240]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_1929,plain,
% 1.77/0.98      ( ~ r2_hidden(X0_48,sK2)
% 1.77/0.98      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0_48)) = X0_48
% 1.77/0.98      | ~ sP0_iProver_split ),
% 1.77/0.98      inference(splitting,
% 1.77/0.98                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.77/0.98                [c_1917]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_2315,plain,
% 1.77/0.98      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0_48)) = X0_48
% 1.77/0.98      | r2_hidden(X0_48,sK2) != iProver_top
% 1.77/0.98      | sP0_iProver_split != iProver_top ),
% 1.77/0.98      inference(predicate_to_equality,[status(thm)],[c_1929]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_2789,plain,
% 1.77/0.98      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
% 1.77/0.98      | v2_funct_1(sK3) != iProver_top
% 1.77/0.98      | sP0_iProver_split != iProver_top ),
% 1.77/0.98      inference(superposition,[status(thm)],[c_2309,c_2315]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_3284,plain,
% 1.77/0.98      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
% 1.77/0.98      | v2_funct_1(sK3) != iProver_top
% 1.77/0.98      | sP0_iProver_split != iProver_top ),
% 1.77/0.98      inference(demodulation,[status(thm)],[c_3238,c_2789]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_15,negated_conjecture,
% 1.77/0.98      ( r2_hidden(sK4,sK2) | ~ v2_funct_1(sK3) ),
% 1.77/0.98      inference(cnf_transformation,[],[f48]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_1934,plain,( X0_48 = X0_48 ),theory(equality) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_1962,plain,
% 1.77/0.98      ( sK4 = sK4 ),
% 1.77/0.98      inference(instantiation,[status(thm)],[c_1934]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_0,plain,
% 1.77/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 1.77/0.98      inference(cnf_transformation,[],[f32]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_7,plain,
% 1.77/0.98      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 1.77/0.98      inference(cnf_transformation,[],[f39]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_224,plain,
% 1.77/0.98      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 1.77/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_7]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_225,plain,
% 1.77/0.98      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 1.77/0.98      inference(unflattening,[status(thm)],[c_224]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_1918,plain,
% 1.77/0.98      ( ~ r2_hidden(X0_48,k1_xboole_0) ),
% 1.77/0.98      inference(subtyping,[status(esa)],[c_225]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_1978,plain,
% 1.77/0.98      ( ~ r2_hidden(sK4,k1_xboole_0) ),
% 1.77/0.98      inference(instantiation,[status(thm)],[c_1918]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_1930,plain,
% 1.77/0.98      ( ~ v2_funct_1(sK3) | sP0_iProver_split | k1_xboole_0 = sK2 ),
% 1.77/0.98      inference(splitting,
% 1.77/0.98                [splitting(split),new_symbols(definition,[])],
% 1.77/0.98                [c_1917]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_1980,plain,
% 1.77/0.98      ( k1_xboole_0 = sK2
% 1.77/0.98      | v2_funct_1(sK3) != iProver_top
% 1.77/0.98      | sP0_iProver_split = iProver_top ),
% 1.77/0.98      inference(predicate_to_equality,[status(thm)],[c_1930]) ).
% 1.77/0.98  
% 1.77/0.98  cnf(c_3231,plain,
% 1.77/0.98      ( v2_funct_1(sK3) ),
% 1.77/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_3229]) ).
% 1.77/0.99  
% 1.77/0.99  cnf(c_3236,plain,
% 1.77/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
% 1.77/0.99      | sP0_iProver_split != iProver_top ),
% 1.77/0.99      inference(superposition,[status(thm)],[c_3229,c_2789]) ).
% 1.77/0.99  
% 1.77/0.99  cnf(c_3243,plain,
% 1.77/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
% 1.77/0.99      | sP0_iProver_split != iProver_top ),
% 1.77/0.99      inference(light_normalisation,[status(thm)],[c_3236,c_3238]) ).
% 1.77/0.99  
% 1.77/0.99  cnf(c_1939,plain,
% 1.77/0.99      ( ~ r2_hidden(X0_48,X0_49)
% 1.77/0.99      | r2_hidden(X1_48,X1_49)
% 1.77/0.99      | X1_49 != X0_49
% 1.77/0.99      | X1_48 != X0_48 ),
% 1.77/0.99      theory(equality) ).
% 1.77/0.99  
% 1.77/0.99  cnf(c_3026,plain,
% 1.77/0.99      ( r2_hidden(X0_48,X0_49)
% 1.77/0.99      | ~ r2_hidden(sK4,sK2)
% 1.77/0.99      | X0_49 != sK2
% 1.77/0.99      | X0_48 != sK4 ),
% 1.77/0.99      inference(instantiation,[status(thm)],[c_1939]) ).
% 1.77/0.99  
% 1.77/0.99  cnf(c_3513,plain,
% 1.77/0.99      ( r2_hidden(X0_48,k1_xboole_0)
% 1.77/0.99      | ~ r2_hidden(sK4,sK2)
% 1.77/0.99      | k1_xboole_0 != sK2
% 1.77/0.99      | X0_48 != sK4 ),
% 1.77/0.99      inference(instantiation,[status(thm)],[c_3026]) ).
% 1.77/0.99  
% 1.77/0.99  cnf(c_3518,plain,
% 1.77/0.99      ( ~ r2_hidden(sK4,sK2)
% 1.77/0.99      | r2_hidden(sK4,k1_xboole_0)
% 1.77/0.99      | k1_xboole_0 != sK2
% 1.77/0.99      | sK4 != sK4 ),
% 1.77/0.99      inference(instantiation,[status(thm)],[c_3513]) ).
% 1.77/0.99  
% 1.77/0.99  cnf(c_3533,plain,
% 1.77/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5 ),
% 1.77/0.99      inference(global_propositional_subsumption,
% 1.77/0.99                [status(thm)],
% 1.77/0.99                [c_3284,c_22,c_15,c_1962,c_1978,c_1980,c_1986,c_1987,
% 1.77/0.99                 c_2470,c_2501,c_3204,c_3226,c_3231,c_3243,c_3518]) ).
% 1.77/0.99  
% 1.77/0.99  cnf(c_1921,negated_conjecture,
% 1.77/0.99      ( r2_hidden(sK4,sK2) | ~ v2_funct_1(sK3) ),
% 1.77/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 1.77/0.99  
% 1.77/0.99  cnf(c_2310,plain,
% 1.77/0.99      ( r2_hidden(sK4,sK2) = iProver_top
% 1.77/0.99      | v2_funct_1(sK3) != iProver_top ),
% 1.77/0.99      inference(predicate_to_equality,[status(thm)],[c_1921]) ).
% 1.77/0.99  
% 1.77/0.99  cnf(c_2790,plain,
% 1.77/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 1.77/0.99      | v2_funct_1(sK3) != iProver_top
% 1.77/0.99      | sP0_iProver_split != iProver_top ),
% 1.77/0.99      inference(superposition,[status(thm)],[c_2310,c_2315]) ).
% 1.77/0.99  
% 1.77/0.99  cnf(c_3235,plain,
% 1.77/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 1.77/0.99      | sP0_iProver_split != iProver_top ),
% 1.77/0.99      inference(superposition,[status(thm)],[c_3229,c_2790]) ).
% 1.77/0.99  
% 1.77/0.99  cnf(c_3536,plain,
% 1.77/0.99      ( sK5 = sK4 | sP0_iProver_split != iProver_top ),
% 1.77/0.99      inference(demodulation,[status(thm)],[c_3533,c_3235]) ).
% 1.77/0.99  
% 1.77/0.99  cnf(c_1937,plain,
% 1.77/0.99      ( X0_48 != X1_48 | X2_48 != X1_48 | X2_48 = X0_48 ),
% 1.77/0.99      theory(equality) ).
% 1.77/0.99  
% 1.77/0.99  cnf(c_3049,plain,
% 1.77/0.99      ( sK5 != X0_48 | sK4 != X0_48 | sK4 = sK5 ),
% 1.77/0.99      inference(instantiation,[status(thm)],[c_1937]) ).
% 1.77/0.99  
% 1.77/0.99  cnf(c_3050,plain,
% 1.77/0.99      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 1.77/0.99      inference(instantiation,[status(thm)],[c_3049]) ).
% 1.77/0.99  
% 1.77/0.99  cnf(c_12,negated_conjecture,
% 1.77/0.99      ( ~ v2_funct_1(sK3) | sK4 != sK5 ),
% 1.77/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.77/0.99  
% 1.77/0.99  cnf(c_1924,negated_conjecture,
% 1.77/0.99      ( ~ v2_funct_1(sK3) | sK4 != sK5 ),
% 1.77/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 1.77/0.99  
% 1.77/0.99  cnf(c_1971,plain,
% 1.77/0.99      ( sK4 != sK5 | v2_funct_1(sK3) != iProver_top ),
% 1.77/0.99      inference(predicate_to_equality,[status(thm)],[c_1924]) ).
% 1.77/0.99  
% 1.77/0.99  cnf(contradiction,plain,
% 1.77/0.99      ( $false ),
% 1.77/0.99      inference(minisat,
% 1.77/0.99                [status(thm)],
% 1.77/0.99                [c_3536,c_3518,c_3231,c_3229,c_3050,c_1980,c_1978,c_1971,
% 1.77/0.99                 c_1962,c_15]) ).
% 1.77/0.99  
% 1.77/0.99  
% 1.77/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.77/0.99  
% 1.77/0.99  ------                               Statistics
% 1.77/0.99  
% 1.77/0.99  ------ General
% 1.77/0.99  
% 1.77/0.99  abstr_ref_over_cycles:                  0
% 1.77/0.99  abstr_ref_under_cycles:                 0
% 1.77/0.99  gc_basic_clause_elim:                   0
% 1.77/0.99  forced_gc_time:                         0
% 1.77/0.99  parsing_time:                           0.008
% 1.77/0.99  unif_index_cands_time:                  0.
% 1.77/0.99  unif_index_add_time:                    0.
% 1.77/0.99  orderings_time:                         0.
% 1.77/0.99  out_proof_time:                         0.007
% 1.77/0.99  total_time:                             0.113
% 1.77/0.99  num_of_symbols:                         56
% 1.77/0.99  num_of_terms:                           1670
% 1.77/0.99  
% 1.77/0.99  ------ Preprocessing
% 1.77/0.99  
% 1.77/0.99  num_of_splits:                          2
% 1.77/0.99  num_of_split_atoms:                     2
% 1.77/0.99  num_of_reused_defs:                     0
% 1.77/0.99  num_eq_ax_congr_red:                    15
% 1.77/0.99  num_of_sem_filtered_clauses:            1
% 1.77/0.99  num_of_subtypes:                        3
% 1.77/0.99  monotx_restored_types:                  1
% 1.77/0.99  sat_num_of_epr_types:                   0
% 1.77/0.99  sat_num_of_non_cyclic_types:            0
% 1.77/0.99  sat_guarded_non_collapsed_types:        0
% 1.77/0.99  num_pure_diseq_elim:                    0
% 1.77/0.99  simp_replaced_by:                       0
% 1.77/0.99  res_preprocessed:                       108
% 1.77/0.99  prep_upred:                             0
% 1.77/0.99  prep_unflattend:                        20
% 1.77/0.99  smt_new_axioms:                         0
% 1.77/0.99  pred_elim_cands:                        4
% 1.77/0.99  pred_elim:                              3
% 1.77/0.99  pred_elim_cl:                           3
% 1.77/0.99  pred_elim_cycles:                       7
% 1.77/0.99  merged_defs:                            0
% 1.77/0.99  merged_defs_ncl:                        0
% 1.77/0.99  bin_hyper_res:                          0
% 1.77/0.99  prep_cycles:                            4
% 1.77/0.99  pred_elim_time:                         0.021
% 1.77/0.99  splitting_time:                         0.
% 1.77/0.99  sem_filter_time:                        0.
% 1.77/0.99  monotx_time:                            0.
% 1.77/0.99  subtype_inf_time:                       0.001
% 1.77/0.99  
% 1.77/0.99  ------ Problem properties
% 1.77/0.99  
% 1.77/0.99  clauses:                                19
% 1.77/0.99  conjectures:                            6
% 1.77/0.99  epr:                                    6
% 1.77/0.99  horn:                                   14
% 1.77/0.99  ground:                                 11
% 1.77/0.99  unary:                                  2
% 1.77/0.99  binary:                                 7
% 1.77/0.99  lits:                                   50
% 1.77/0.99  lits_eq:                                11
% 1.77/0.99  fd_pure:                                0
% 1.77/0.99  fd_pseudo:                              0
% 1.77/0.99  fd_cond:                                0
% 1.77/0.99  fd_pseudo_cond:                         2
% 1.77/0.99  ac_symbols:                             0
% 1.77/0.99  
% 1.77/0.99  ------ Propositional Solver
% 1.77/0.99  
% 1.77/0.99  prop_solver_calls:                      28
% 1.77/0.99  prop_fast_solver_calls:                 987
% 1.77/0.99  smt_solver_calls:                       0
% 1.77/0.99  smt_fast_solver_calls:                  0
% 1.77/0.99  prop_num_of_clauses:                    708
% 1.77/0.99  prop_preprocess_simplified:             3496
% 1.77/0.99  prop_fo_subsumed:                       11
% 1.77/0.99  prop_solver_time:                       0.
% 1.77/0.99  smt_solver_time:                        0.
% 1.77/0.99  smt_fast_solver_time:                   0.
% 1.77/0.99  prop_fast_solver_time:                  0.
% 1.77/0.99  prop_unsat_core_time:                   0.
% 1.77/0.99  
% 1.77/0.99  ------ QBF
% 1.77/0.99  
% 1.77/0.99  qbf_q_res:                              0
% 1.77/0.99  qbf_num_tautologies:                    0
% 1.77/0.99  qbf_prep_cycles:                        0
% 1.77/0.99  
% 1.77/0.99  ------ BMC1
% 1.77/0.99  
% 1.77/0.99  bmc1_current_bound:                     -1
% 1.77/0.99  bmc1_last_solved_bound:                 -1
% 1.77/0.99  bmc1_unsat_core_size:                   -1
% 1.77/0.99  bmc1_unsat_core_parents_size:           -1
% 1.77/0.99  bmc1_merge_next_fun:                    0
% 1.77/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.77/0.99  
% 1.77/0.99  ------ Instantiation
% 1.77/0.99  
% 1.77/0.99  inst_num_of_clauses:                    214
% 1.77/0.99  inst_num_in_passive:                    53
% 1.77/0.99  inst_num_in_active:                     160
% 1.77/0.99  inst_num_in_unprocessed:                2
% 1.77/0.99  inst_num_of_loops:                      190
% 1.77/0.99  inst_num_of_learning_restarts:          0
% 1.77/0.99  inst_num_moves_active_passive:          25
% 1.77/0.99  inst_lit_activity:                      0
% 1.77/0.99  inst_lit_activity_moves:                0
% 1.77/0.99  inst_num_tautologies:                   0
% 1.77/0.99  inst_num_prop_implied:                  0
% 1.77/0.99  inst_num_existing_simplified:           0
% 1.77/0.99  inst_num_eq_res_simplified:             0
% 1.77/0.99  inst_num_child_elim:                    0
% 1.77/0.99  inst_num_of_dismatching_blockings:      18
% 1.77/0.99  inst_num_of_non_proper_insts:           195
% 1.77/0.99  inst_num_of_duplicates:                 0
% 1.77/0.99  inst_inst_num_from_inst_to_res:         0
% 1.77/0.99  inst_dismatching_checking_time:         0.
% 1.77/0.99  
% 1.77/0.99  ------ Resolution
% 1.77/0.99  
% 1.77/0.99  res_num_of_clauses:                     0
% 1.77/0.99  res_num_in_passive:                     0
% 1.77/0.99  res_num_in_active:                      0
% 1.77/0.99  res_num_of_loops:                       112
% 1.77/0.99  res_forward_subset_subsumed:            43
% 1.77/0.99  res_backward_subset_subsumed:           2
% 1.77/0.99  res_forward_subsumed:                   0
% 1.77/0.99  res_backward_subsumed:                  0
% 1.77/0.99  res_forward_subsumption_resolution:     0
% 1.77/0.99  res_backward_subsumption_resolution:    0
% 1.77/0.99  res_clause_to_clause_subsumption:       80
% 1.77/0.99  res_orphan_elimination:                 0
% 1.77/0.99  res_tautology_del:                      43
% 1.77/0.99  res_num_eq_res_simplified:              0
% 1.77/0.99  res_num_sel_changes:                    0
% 1.77/0.99  res_moves_from_active_to_pass:          0
% 1.77/0.99  
% 1.77/0.99  ------ Superposition
% 1.77/0.99  
% 1.77/0.99  sup_time_total:                         0.
% 1.77/0.99  sup_time_generating:                    0.
% 1.77/0.99  sup_time_sim_full:                      0.
% 1.77/0.99  sup_time_sim_immed:                     0.
% 1.77/0.99  
% 1.77/0.99  sup_num_of_clauses:                     41
% 1.77/0.99  sup_num_in_active:                      32
% 1.77/0.99  sup_num_in_passive:                     9
% 1.77/0.99  sup_num_of_loops:                       37
% 1.77/0.99  sup_fw_superposition:                   11
% 1.77/0.99  sup_bw_superposition:                   16
% 1.77/0.99  sup_immediate_simplified:               3
% 1.77/0.99  sup_given_eliminated:                   0
% 1.77/0.99  comparisons_done:                       0
% 1.77/0.99  comparisons_avoided:                    0
% 1.77/0.99  
% 1.77/0.99  ------ Simplifications
% 1.77/0.99  
% 1.77/0.99  
% 1.77/0.99  sim_fw_subset_subsumed:                 1
% 1.77/0.99  sim_bw_subset_subsumed:                 1
% 1.77/0.99  sim_fw_subsumed:                        0
% 1.77/0.99  sim_bw_subsumed:                        1
% 1.77/0.99  sim_fw_subsumption_res:                 0
% 1.77/0.99  sim_bw_subsumption_res:                 0
% 1.77/0.99  sim_tautology_del:                      0
% 1.77/0.99  sim_eq_tautology_del:                   3
% 1.77/0.99  sim_eq_res_simp:                        0
% 1.77/0.99  sim_fw_demodulated:                     0
% 1.77/0.99  sim_bw_demodulated:                     4
% 1.77/0.99  sim_light_normalised:                   2
% 1.77/0.99  sim_joinable_taut:                      0
% 1.77/0.99  sim_joinable_simp:                      0
% 1.77/0.99  sim_ac_normalised:                      0
% 1.77/0.99  sim_smt_subsumption:                    0
% 1.77/0.99  
%------------------------------------------------------------------------------
