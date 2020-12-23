%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:57 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :  177 (3043 expanded)
%              Number of clauses        :  116 ( 908 expanded)
%              Number of leaves         :   19 ( 608 expanded)
%              Depth                    :   22
%              Number of atoms          :  644 (20695 expanded)
%              Number of equality atoms :  267 (6482 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( sK5 != sK6
        & k1_funct_1(X1,sK5) = k1_funct_1(X1,sK6)
        & r2_hidden(sK6,X0)
        & r2_hidden(sK5,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
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
            & k1_funct_1(sK4,X2) = k1_funct_1(sK4,X3)
            & r2_hidden(X3,sK3)
            & r2_hidden(X2,sK3) )
        | ~ v2_funct_1(sK4) )
      & ( ! [X5,X4] :
            ( X4 = X5
            | k1_funct_1(sK4,X4) != k1_funct_1(sK4,X5)
            | ~ r2_hidden(X5,sK3)
            | ~ r2_hidden(X4,sK3) )
        | v2_funct_1(sK4) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
      & v1_funct_2(sK4,sK3,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( ( sK5 != sK6
        & k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
        & r2_hidden(sK6,sK3)
        & r2_hidden(sK5,sK3) )
      | ~ v2_funct_1(sK4) )
    & ( ! [X4,X5] :
          ( X4 = X5
          | k1_funct_1(sK4,X4) != k1_funct_1(sK4,X5)
          | ~ r2_hidden(X5,sK3)
          | ~ r2_hidden(X4,sK3) )
      | v2_funct_1(sK4) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    & v1_funct_2(sK4,sK3,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f35,f37,f36])).

fof(f58,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
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

fof(f15,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK1(X0) != sK2(X0)
        & k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0))
        & r2_hidden(sK2(X0),k1_relat_1(X0))
        & r2_hidden(sK1(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK1(X0) != sK2(X0)
            & k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0))
            & r2_hidden(sK2(X0),k1_relat_1(X0))
            & r2_hidden(sK1(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f31])).

fof(f50,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f51,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | sK1(X0) != sK2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK4,X4) != k1_funct_1(sK4,X5)
      | ~ r2_hidden(X5,sK3)
      | ~ r2_hidden(X4,sK3)
      | v2_funct_1(sK4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK2(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK1(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f20])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    v1_funct_2(sK4,sK3,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,
    ( r2_hidden(sK6,sK3)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f60,plain,
    ( r2_hidden(sK5,sK3)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f47,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,
    ( sK5 != sK6
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2925,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2935,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3343,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2925,c_2935])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_195,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_196,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_195])).

cnf(c_247,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_196])).

cnf(c_2924,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_247])).

cnf(c_4641,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK3)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3343,c_2924])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2934,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4848,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4641,c_2934])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_391,plain,
    ( v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK1(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_24])).

cnf(c_392,plain,
    ( v2_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK2(sK4)) = k1_funct_1(sK4,sK1(sK4)) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_2919,plain,
    ( k1_funct_1(sK4,sK2(sK4)) = k1_funct_1(sK4,sK1(sK4))
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_392])).

cnf(c_4850,plain,
    ( k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK2(sK4))
    | v2_funct_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4848,c_2919])).

cnf(c_25,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_56,plain,
    ( k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_58,plain,
    ( k1_funct_1(sK4,sK2(sK4)) = k1_funct_1(sK4,sK1(sK4))
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK2(X0) != sK1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_59,plain,
    ( sK2(X0) != sK1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_61,plain,
    ( sK2(sK4) != sK1(sK4)
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_59])).

cnf(c_21,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X1,sK3)
    | v2_funct_1(sK4)
    | X1 = X0
    | k1_funct_1(sK4,X1) != k1_funct_1(sK4,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3325,plain,
    ( ~ r2_hidden(sK2(sK4),sK3)
    | ~ r2_hidden(sK1(sK4),sK3)
    | v2_funct_1(sK4)
    | k1_funct_1(sK4,sK2(sK4)) != k1_funct_1(sK4,sK1(sK4))
    | sK2(sK4) = sK1(sK4) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_3326,plain,
    ( k1_funct_1(sK4,sK2(sK4)) != k1_funct_1(sK4,sK1(sK4))
    | sK2(sK4) = sK1(sK4)
    | r2_hidden(sK2(sK4),sK3) != iProver_top
    | r2_hidden(sK1(sK4),sK3) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3325])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2931,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3719,plain,
    ( k1_relset_1(sK3,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2925,c_2931])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2932,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3855,plain,
    ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3719,c_2932])).

cnf(c_27,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4192,plain,
    ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3855,c_27])).

cnf(c_4197,plain,
    ( r1_tarski(k1_relat_1(sK4),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4192,c_2935])).

cnf(c_10,plain,
    ( r2_hidden(sK2(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_378,plain,
    ( r2_hidden(sK2(X0),k1_relat_1(X0))
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_24])).

cnf(c_379,plain,
    ( r2_hidden(sK2(sK4),k1_relat_1(sK4))
    | v2_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_2920,plain,
    ( r2_hidden(sK2(sK4),k1_relat_1(sK4)) = iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_379])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2938,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3885,plain,
    ( r2_hidden(sK2(sK4),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2920,c_2938])).

cnf(c_4565,plain,
    ( r2_hidden(sK2(sK4),sK3) = iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4197,c_3885])).

cnf(c_11,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_365,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_24])).

cnf(c_366,plain,
    ( r2_hidden(sK1(sK4),k1_relat_1(sK4))
    | v2_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_2921,plain,
    ( r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_366])).

cnf(c_3884,plain,
    ( r2_hidden(sK1(sK4),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2921,c_2938])).

cnf(c_4566,plain,
    ( r2_hidden(sK1(sK4),sK3) = iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4197,c_3884])).

cnf(c_4929,plain,
    ( v2_funct_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4850,c_25,c_58,c_61,c_3326,c_4565,c_4566,c_4848])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK4,sK3,sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_336,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
    | sK3 != X2
    | sK3 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_337,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    | ~ r2_hidden(X0,sK3)
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_341,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ v2_funct_1(sK4)
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_337,c_24,c_22])).

cnf(c_2302,plain,
    ( ~ v2_funct_1(sK4)
    | sP1_iProver_split
    | k1_xboole_0 = sK3 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_341])).

cnf(c_2922,plain,
    ( k1_xboole_0 = sK3
    | v2_funct_1(sK4) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2302])).

cnf(c_4936,plain,
    ( sK3 = k1_xboole_0
    | sP1_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_4929,c_2922])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK6,sK3)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2928,plain,
    ( r2_hidden(sK6,sK3) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2301,plain,
    ( ~ r2_hidden(X0,sK3)
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_341])).

cnf(c_2923,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0
    | r2_hidden(X0,sK3) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2301])).

cnf(c_3543,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK6)) = sK6
    | v2_funct_1(sK4) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2928,c_2923])).

cnf(c_4938,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK6)) = sK6
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_4929,c_3543])).

cnf(c_18,negated_conjecture,
    ( ~ v2_funct_1(sK4)
    | k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2929,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4940,plain,
    ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_4929,c_2929])).

cnf(c_4947,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK6
    | sP1_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4938,c_4940])).

cnf(c_5587,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK6
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4936,c_4947])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2933,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3313,plain,
    ( r1_tarski(sK3,sK6) != iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2928,c_2933])).

cnf(c_3323,plain,
    ( ~ r1_tarski(sK3,sK6)
    | ~ v2_funct_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3313])).

cnf(c_4931,plain,
    ( v2_funct_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4929])).

cnf(c_2306,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_3647,plain,
    ( ~ r1_tarski(X0,sK6)
    | r1_tarski(sK3,sK6)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_2306])).

cnf(c_5616,plain,
    ( r1_tarski(sK3,sK6)
    | ~ r1_tarski(k1_xboole_0,sK6)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3647])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_5617,plain,
    ( r1_tarski(k1_xboole_0,sK6) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6104,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5587,c_3323,c_4931,c_5616,c_5617])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK5,sK3)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2927,plain,
    ( r2_hidden(sK5,sK3) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3544,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK5
    | v2_funct_1(sK4) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2927,c_2923])).

cnf(c_4937,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK5
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_4929,c_3544])).

cnf(c_6107,plain,
    ( sK6 = sK5
    | sP1_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_6104,c_4937])).

cnf(c_4849,plain,
    ( v1_relat_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4848])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_417,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | X2 = X0
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_418,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ r2_hidden(X1,k1_relat_1(sK4))
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | X0 = X1
    | k1_funct_1(sK4,X0) != k1_funct_1(sK4,X1) ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_2299,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ r2_hidden(X1,k1_relat_1(sK4))
    | X0 = X1
    | k1_funct_1(sK4,X0) != k1_funct_1(sK4,X1)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_418])).

cnf(c_3752,plain,
    ( ~ r2_hidden(sK2(sK4),k1_relat_1(sK4))
    | ~ r2_hidden(sK1(sK4),k1_relat_1(sK4))
    | ~ sP0_iProver_split
    | k1_funct_1(sK4,sK1(sK4)) != k1_funct_1(sK4,sK2(sK4))
    | sK1(sK4) = sK2(sK4) ),
    inference(instantiation,[status(thm)],[c_2299])).

cnf(c_3753,plain,
    ( k1_funct_1(sK4,sK1(sK4)) != k1_funct_1(sK4,sK2(sK4))
    | sK1(sK4) = sK2(sK4)
    | r2_hidden(sK2(sK4),k1_relat_1(sK4)) != iProver_top
    | r2_hidden(sK1(sK4),k1_relat_1(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3752])).

cnf(c_2305,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3328,plain,
    ( sK2(sK4) != X0
    | sK2(sK4) = sK1(sK4)
    | sK1(sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_2305])).

cnf(c_3534,plain,
    ( sK2(sK4) != sK2(sK4)
    | sK2(sK4) = sK1(sK4)
    | sK1(sK4) != sK2(sK4) ),
    inference(instantiation,[status(thm)],[c_3328])).

cnf(c_2300,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_418])).

cnf(c_2332,plain,
    ( v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2300])).

cnf(c_2304,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2331,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2304])).

cnf(c_2314,plain,
    ( X0 != X1
    | sK2(X0) = sK2(X1) ),
    theory(equality)).

cnf(c_2326,plain,
    ( sK2(sK4) = sK2(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2314])).

cnf(c_17,negated_conjecture,
    ( ~ v2_funct_1(sK4)
    | sK5 != sK6 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1024,plain,
    ( r2_hidden(sK1(sK4),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | sK6 != sK5 ),
    inference(resolution,[status(thm)],[c_366,c_17])).

cnf(c_1025,plain,
    ( sK6 != sK5
    | r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1024])).

cnf(c_933,plain,
    ( r2_hidden(sK2(sK4),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | sK6 != sK5 ),
    inference(resolution,[status(thm)],[c_379,c_17])).

cnf(c_934,plain,
    ( sK6 != sK5
    | r2_hidden(sK2(sK4),k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_933])).

cnf(c_842,plain,
    ( ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK2(sK4))
    | sK6 != sK5 ),
    inference(resolution,[status(thm)],[c_392,c_17])).

cnf(c_404,plain,
    ( v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK2(X0) != sK1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_405,plain,
    ( v2_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | sK2(sK4) != sK1(sK4) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_751,plain,
    ( ~ v1_relat_1(sK4)
    | sK2(sK4) != sK1(sK4)
    | sK6 != sK5 ),
    inference(resolution,[status(thm)],[c_405,c_17])).

cnf(c_752,plain,
    ( sK2(sK4) != sK1(sK4)
    | sK6 != sK5
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_751])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6107,c_5617,c_5616,c_4936,c_4931,c_4929,c_4849,c_4848,c_3753,c_3534,c_3323,c_2332,c_2331,c_2326,c_1025,c_934,c_842,c_752])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:07:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.88/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/0.98  
% 2.88/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.88/0.98  
% 2.88/0.98  ------  iProver source info
% 2.88/0.98  
% 2.88/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.88/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.88/0.98  git: non_committed_changes: false
% 2.88/0.98  git: last_make_outside_of_git: false
% 2.88/0.98  
% 2.88/0.98  ------ 
% 2.88/0.98  
% 2.88/0.98  ------ Input Options
% 2.88/0.98  
% 2.88/0.98  --out_options                           all
% 2.88/0.98  --tptp_safe_out                         true
% 2.88/0.98  --problem_path                          ""
% 2.88/0.98  --include_path                          ""
% 2.88/0.98  --clausifier                            res/vclausify_rel
% 2.88/0.98  --clausifier_options                    --mode clausify
% 2.88/0.98  --stdin                                 false
% 2.88/0.98  --stats_out                             all
% 2.88/0.98  
% 2.88/0.98  ------ General Options
% 2.88/0.98  
% 2.88/0.98  --fof                                   false
% 2.88/0.98  --time_out_real                         305.
% 2.88/0.98  --time_out_virtual                      -1.
% 2.88/0.98  --symbol_type_check                     false
% 2.88/0.98  --clausify_out                          false
% 2.88/0.98  --sig_cnt_out                           false
% 2.88/0.98  --trig_cnt_out                          false
% 2.88/0.98  --trig_cnt_out_tolerance                1.
% 2.88/0.98  --trig_cnt_out_sk_spl                   false
% 2.88/0.98  --abstr_cl_out                          false
% 2.88/0.98  
% 2.88/0.98  ------ Global Options
% 2.88/0.98  
% 2.88/0.98  --schedule                              default
% 2.88/0.98  --add_important_lit                     false
% 2.88/0.98  --prop_solver_per_cl                    1000
% 2.88/0.98  --min_unsat_core                        false
% 2.88/0.98  --soft_assumptions                      false
% 2.88/0.98  --soft_lemma_size                       3
% 2.88/0.98  --prop_impl_unit_size                   0
% 2.88/0.98  --prop_impl_unit                        []
% 2.88/0.98  --share_sel_clauses                     true
% 2.88/0.98  --reset_solvers                         false
% 2.88/0.98  --bc_imp_inh                            [conj_cone]
% 2.88/0.98  --conj_cone_tolerance                   3.
% 2.88/0.98  --extra_neg_conj                        none
% 2.88/0.98  --large_theory_mode                     true
% 2.88/0.98  --prolific_symb_bound                   200
% 2.88/0.98  --lt_threshold                          2000
% 2.88/0.98  --clause_weak_htbl                      true
% 2.88/0.98  --gc_record_bc_elim                     false
% 2.88/0.98  
% 2.88/0.98  ------ Preprocessing Options
% 2.88/0.98  
% 2.88/0.98  --preprocessing_flag                    true
% 2.88/0.98  --time_out_prep_mult                    0.1
% 2.88/0.98  --splitting_mode                        input
% 2.88/0.98  --splitting_grd                         true
% 2.88/0.98  --splitting_cvd                         false
% 2.88/0.98  --splitting_cvd_svl                     false
% 2.88/0.98  --splitting_nvd                         32
% 2.88/0.98  --sub_typing                            true
% 2.88/0.98  --prep_gs_sim                           true
% 2.88/0.98  --prep_unflatten                        true
% 2.88/0.98  --prep_res_sim                          true
% 2.88/0.98  --prep_upred                            true
% 2.88/0.98  --prep_sem_filter                       exhaustive
% 2.88/0.98  --prep_sem_filter_out                   false
% 2.88/0.98  --pred_elim                             true
% 2.88/0.98  --res_sim_input                         true
% 2.88/0.98  --eq_ax_congr_red                       true
% 2.88/0.98  --pure_diseq_elim                       true
% 2.88/0.98  --brand_transform                       false
% 2.88/0.98  --non_eq_to_eq                          false
% 2.88/0.98  --prep_def_merge                        true
% 2.88/0.98  --prep_def_merge_prop_impl              false
% 2.88/0.98  --prep_def_merge_mbd                    true
% 2.88/0.98  --prep_def_merge_tr_red                 false
% 2.88/0.98  --prep_def_merge_tr_cl                  false
% 2.88/0.98  --smt_preprocessing                     true
% 2.88/0.98  --smt_ac_axioms                         fast
% 2.88/0.98  --preprocessed_out                      false
% 2.88/0.98  --preprocessed_stats                    false
% 2.88/0.98  
% 2.88/0.98  ------ Abstraction refinement Options
% 2.88/0.98  
% 2.88/0.98  --abstr_ref                             []
% 2.88/0.98  --abstr_ref_prep                        false
% 2.88/0.98  --abstr_ref_until_sat                   false
% 2.88/0.98  --abstr_ref_sig_restrict                funpre
% 2.88/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.88/0.98  --abstr_ref_under                       []
% 2.88/0.98  
% 2.88/0.98  ------ SAT Options
% 2.88/0.98  
% 2.88/0.98  --sat_mode                              false
% 2.88/0.98  --sat_fm_restart_options                ""
% 2.88/0.98  --sat_gr_def                            false
% 2.88/0.98  --sat_epr_types                         true
% 2.88/0.98  --sat_non_cyclic_types                  false
% 2.88/0.98  --sat_finite_models                     false
% 2.88/0.98  --sat_fm_lemmas                         false
% 2.88/0.98  --sat_fm_prep                           false
% 2.88/0.98  --sat_fm_uc_incr                        true
% 2.88/0.98  --sat_out_model                         small
% 2.88/0.98  --sat_out_clauses                       false
% 2.88/0.98  
% 2.88/0.98  ------ QBF Options
% 2.88/0.98  
% 2.88/0.98  --qbf_mode                              false
% 2.88/0.98  --qbf_elim_univ                         false
% 2.88/0.98  --qbf_dom_inst                          none
% 2.88/0.98  --qbf_dom_pre_inst                      false
% 2.88/0.98  --qbf_sk_in                             false
% 2.88/0.98  --qbf_pred_elim                         true
% 2.88/0.98  --qbf_split                             512
% 2.88/0.98  
% 2.88/0.98  ------ BMC1 Options
% 2.88/0.98  
% 2.88/0.98  --bmc1_incremental                      false
% 2.88/0.98  --bmc1_axioms                           reachable_all
% 2.88/0.98  --bmc1_min_bound                        0
% 2.88/0.98  --bmc1_max_bound                        -1
% 2.88/0.98  --bmc1_max_bound_default                -1
% 2.88/0.98  --bmc1_symbol_reachability              true
% 2.88/0.98  --bmc1_property_lemmas                  false
% 2.88/0.98  --bmc1_k_induction                      false
% 2.88/0.98  --bmc1_non_equiv_states                 false
% 2.88/0.98  --bmc1_deadlock                         false
% 2.88/0.98  --bmc1_ucm                              false
% 2.88/0.98  --bmc1_add_unsat_core                   none
% 2.88/0.98  --bmc1_unsat_core_children              false
% 2.88/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.88/0.98  --bmc1_out_stat                         full
% 2.88/0.98  --bmc1_ground_init                      false
% 2.88/0.98  --bmc1_pre_inst_next_state              false
% 2.88/0.98  --bmc1_pre_inst_state                   false
% 2.88/0.98  --bmc1_pre_inst_reach_state             false
% 2.88/0.98  --bmc1_out_unsat_core                   false
% 2.88/0.98  --bmc1_aig_witness_out                  false
% 2.88/0.98  --bmc1_verbose                          false
% 2.88/0.98  --bmc1_dump_clauses_tptp                false
% 2.88/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.88/0.98  --bmc1_dump_file                        -
% 2.88/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.88/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.88/0.98  --bmc1_ucm_extend_mode                  1
% 2.88/0.98  --bmc1_ucm_init_mode                    2
% 2.88/0.98  --bmc1_ucm_cone_mode                    none
% 2.88/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.88/0.98  --bmc1_ucm_relax_model                  4
% 2.88/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.88/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.88/0.98  --bmc1_ucm_layered_model                none
% 2.88/0.98  --bmc1_ucm_max_lemma_size               10
% 2.88/0.98  
% 2.88/0.98  ------ AIG Options
% 2.88/0.98  
% 2.88/0.98  --aig_mode                              false
% 2.88/0.98  
% 2.88/0.98  ------ Instantiation Options
% 2.88/0.98  
% 2.88/0.98  --instantiation_flag                    true
% 2.88/0.98  --inst_sos_flag                         false
% 2.88/0.98  --inst_sos_phase                        true
% 2.88/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.88/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.88/0.98  --inst_lit_sel_side                     num_symb
% 2.88/0.98  --inst_solver_per_active                1400
% 2.88/0.98  --inst_solver_calls_frac                1.
% 2.88/0.98  --inst_passive_queue_type               priority_queues
% 2.88/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.88/0.98  --inst_passive_queues_freq              [25;2]
% 2.88/0.98  --inst_dismatching                      true
% 2.88/0.98  --inst_eager_unprocessed_to_passive     true
% 2.88/0.98  --inst_prop_sim_given                   true
% 2.88/0.98  --inst_prop_sim_new                     false
% 2.88/0.98  --inst_subs_new                         false
% 2.88/0.98  --inst_eq_res_simp                      false
% 2.88/0.98  --inst_subs_given                       false
% 2.88/0.98  --inst_orphan_elimination               true
% 2.88/0.98  --inst_learning_loop_flag               true
% 2.88/0.98  --inst_learning_start                   3000
% 2.88/0.98  --inst_learning_factor                  2
% 2.88/0.98  --inst_start_prop_sim_after_learn       3
% 2.88/0.98  --inst_sel_renew                        solver
% 2.88/0.98  --inst_lit_activity_flag                true
% 2.88/0.98  --inst_restr_to_given                   false
% 2.88/0.98  --inst_activity_threshold               500
% 2.88/0.98  --inst_out_proof                        true
% 2.88/0.98  
% 2.88/0.98  ------ Resolution Options
% 2.88/0.98  
% 2.88/0.98  --resolution_flag                       true
% 2.88/0.98  --res_lit_sel                           adaptive
% 2.88/0.98  --res_lit_sel_side                      none
% 2.88/0.98  --res_ordering                          kbo
% 2.88/0.98  --res_to_prop_solver                    active
% 2.88/0.98  --res_prop_simpl_new                    false
% 2.88/0.98  --res_prop_simpl_given                  true
% 2.88/0.98  --res_passive_queue_type                priority_queues
% 2.88/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.88/0.98  --res_passive_queues_freq               [15;5]
% 2.88/0.98  --res_forward_subs                      full
% 2.88/0.98  --res_backward_subs                     full
% 2.88/0.98  --res_forward_subs_resolution           true
% 2.88/0.98  --res_backward_subs_resolution          true
% 2.88/0.98  --res_orphan_elimination                true
% 2.88/0.98  --res_time_limit                        2.
% 2.88/0.98  --res_out_proof                         true
% 2.88/0.98  
% 2.88/0.98  ------ Superposition Options
% 2.88/0.98  
% 2.88/0.98  --superposition_flag                    true
% 2.88/0.98  --sup_passive_queue_type                priority_queues
% 2.88/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.88/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.88/0.98  --demod_completeness_check              fast
% 2.88/0.98  --demod_use_ground                      true
% 2.88/0.98  --sup_to_prop_solver                    passive
% 2.88/0.98  --sup_prop_simpl_new                    true
% 2.88/0.98  --sup_prop_simpl_given                  true
% 2.88/0.98  --sup_fun_splitting                     false
% 2.88/0.98  --sup_smt_interval                      50000
% 2.88/0.98  
% 2.88/0.98  ------ Superposition Simplification Setup
% 2.88/0.98  
% 2.88/0.98  --sup_indices_passive                   []
% 2.88/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.88/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.98  --sup_full_bw                           [BwDemod]
% 2.88/0.98  --sup_immed_triv                        [TrivRules]
% 2.88/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.88/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.98  --sup_immed_bw_main                     []
% 2.88/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.88/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/0.98  
% 2.88/0.98  ------ Combination Options
% 2.88/0.98  
% 2.88/0.98  --comb_res_mult                         3
% 2.88/0.98  --comb_sup_mult                         2
% 2.88/0.98  --comb_inst_mult                        10
% 2.88/0.98  
% 2.88/0.98  ------ Debug Options
% 2.88/0.98  
% 2.88/0.98  --dbg_backtrace                         false
% 2.88/0.98  --dbg_dump_prop_clauses                 false
% 2.88/0.98  --dbg_dump_prop_clauses_file            -
% 2.88/0.98  --dbg_out_stat                          false
% 2.88/0.98  ------ Parsing...
% 2.88/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.88/0.98  
% 2.88/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.88/0.98  
% 2.88/0.98  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.88/0.98  
% 2.88/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.88/0.98  ------ Proving...
% 2.88/0.98  ------ Problem Properties 
% 2.88/0.98  
% 2.88/0.98  
% 2.88/0.98  clauses                                 25
% 2.88/0.98  conjectures                             6
% 2.88/0.98  EPR                                     9
% 2.88/0.98  Horn                                    19
% 2.88/0.98  unary                                   3
% 2.88/0.98  binary                                  11
% 2.88/0.98  lits                                    62
% 2.88/0.98  lits eq                                 11
% 2.88/0.98  fd_pure                                 0
% 2.88/0.98  fd_pseudo                               0
% 2.88/0.98  fd_cond                                 0
% 2.88/0.98  fd_pseudo_cond                          2
% 2.88/0.98  AC symbols                              0
% 2.88/0.98  
% 2.88/0.98  ------ Schedule dynamic 5 is on 
% 2.88/0.98  
% 2.88/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.88/0.98  
% 2.88/0.98  
% 2.88/0.98  ------ 
% 2.88/0.98  Current options:
% 2.88/0.98  ------ 
% 2.88/0.98  
% 2.88/0.98  ------ Input Options
% 2.88/0.98  
% 2.88/0.98  --out_options                           all
% 2.88/0.98  --tptp_safe_out                         true
% 2.88/0.98  --problem_path                          ""
% 2.88/0.98  --include_path                          ""
% 2.88/0.98  --clausifier                            res/vclausify_rel
% 2.88/0.98  --clausifier_options                    --mode clausify
% 2.88/0.98  --stdin                                 false
% 2.88/0.98  --stats_out                             all
% 2.88/0.98  
% 2.88/0.98  ------ General Options
% 2.88/0.98  
% 2.88/0.98  --fof                                   false
% 2.88/0.98  --time_out_real                         305.
% 2.88/0.98  --time_out_virtual                      -1.
% 2.88/0.98  --symbol_type_check                     false
% 2.88/0.98  --clausify_out                          false
% 2.88/0.98  --sig_cnt_out                           false
% 2.88/0.98  --trig_cnt_out                          false
% 2.88/0.98  --trig_cnt_out_tolerance                1.
% 2.88/0.98  --trig_cnt_out_sk_spl                   false
% 2.88/0.98  --abstr_cl_out                          false
% 2.88/0.98  
% 2.88/0.98  ------ Global Options
% 2.88/0.98  
% 2.88/0.98  --schedule                              default
% 2.88/0.98  --add_important_lit                     false
% 2.88/0.98  --prop_solver_per_cl                    1000
% 2.88/0.98  --min_unsat_core                        false
% 2.88/0.98  --soft_assumptions                      false
% 2.88/0.98  --soft_lemma_size                       3
% 2.88/0.98  --prop_impl_unit_size                   0
% 2.88/0.98  --prop_impl_unit                        []
% 2.88/0.98  --share_sel_clauses                     true
% 2.88/0.98  --reset_solvers                         false
% 2.88/0.98  --bc_imp_inh                            [conj_cone]
% 2.88/0.98  --conj_cone_tolerance                   3.
% 2.88/0.98  --extra_neg_conj                        none
% 2.88/0.98  --large_theory_mode                     true
% 2.88/0.98  --prolific_symb_bound                   200
% 2.88/0.98  --lt_threshold                          2000
% 2.88/0.98  --clause_weak_htbl                      true
% 2.88/0.98  --gc_record_bc_elim                     false
% 2.88/0.98  
% 2.88/0.98  ------ Preprocessing Options
% 2.88/0.98  
% 2.88/0.98  --preprocessing_flag                    true
% 2.88/0.98  --time_out_prep_mult                    0.1
% 2.88/0.98  --splitting_mode                        input
% 2.88/0.98  --splitting_grd                         true
% 2.88/0.98  --splitting_cvd                         false
% 2.88/0.98  --splitting_cvd_svl                     false
% 2.88/0.98  --splitting_nvd                         32
% 2.88/0.98  --sub_typing                            true
% 2.88/0.98  --prep_gs_sim                           true
% 2.88/0.98  --prep_unflatten                        true
% 2.88/0.98  --prep_res_sim                          true
% 2.88/0.98  --prep_upred                            true
% 2.88/0.98  --prep_sem_filter                       exhaustive
% 2.88/0.98  --prep_sem_filter_out                   false
% 2.88/0.98  --pred_elim                             true
% 2.88/0.98  --res_sim_input                         true
% 2.88/0.98  --eq_ax_congr_red                       true
% 2.88/0.98  --pure_diseq_elim                       true
% 2.88/0.98  --brand_transform                       false
% 2.88/0.98  --non_eq_to_eq                          false
% 2.88/0.98  --prep_def_merge                        true
% 2.88/0.98  --prep_def_merge_prop_impl              false
% 2.88/0.98  --prep_def_merge_mbd                    true
% 2.88/0.98  --prep_def_merge_tr_red                 false
% 2.88/0.98  --prep_def_merge_tr_cl                  false
% 2.88/0.98  --smt_preprocessing                     true
% 2.88/0.98  --smt_ac_axioms                         fast
% 2.88/0.98  --preprocessed_out                      false
% 2.88/0.98  --preprocessed_stats                    false
% 2.88/0.98  
% 2.88/0.98  ------ Abstraction refinement Options
% 2.88/0.98  
% 2.88/0.98  --abstr_ref                             []
% 2.88/0.98  --abstr_ref_prep                        false
% 2.88/0.98  --abstr_ref_until_sat                   false
% 2.88/0.98  --abstr_ref_sig_restrict                funpre
% 2.88/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.88/0.98  --abstr_ref_under                       []
% 2.88/0.98  
% 2.88/0.98  ------ SAT Options
% 2.88/0.98  
% 2.88/0.98  --sat_mode                              false
% 2.88/0.98  --sat_fm_restart_options                ""
% 2.88/0.98  --sat_gr_def                            false
% 2.88/0.98  --sat_epr_types                         true
% 2.88/0.98  --sat_non_cyclic_types                  false
% 2.88/0.98  --sat_finite_models                     false
% 2.88/0.98  --sat_fm_lemmas                         false
% 2.88/0.98  --sat_fm_prep                           false
% 2.88/0.98  --sat_fm_uc_incr                        true
% 2.88/0.98  --sat_out_model                         small
% 2.88/0.98  --sat_out_clauses                       false
% 2.88/0.98  
% 2.88/0.98  ------ QBF Options
% 2.88/0.98  
% 2.88/0.98  --qbf_mode                              false
% 2.88/0.98  --qbf_elim_univ                         false
% 2.88/0.98  --qbf_dom_inst                          none
% 2.88/0.98  --qbf_dom_pre_inst                      false
% 2.88/0.98  --qbf_sk_in                             false
% 2.88/0.98  --qbf_pred_elim                         true
% 2.88/0.98  --qbf_split                             512
% 2.88/0.98  
% 2.88/0.98  ------ BMC1 Options
% 2.88/0.98  
% 2.88/0.98  --bmc1_incremental                      false
% 2.88/0.98  --bmc1_axioms                           reachable_all
% 2.88/0.98  --bmc1_min_bound                        0
% 2.88/0.98  --bmc1_max_bound                        -1
% 2.88/0.98  --bmc1_max_bound_default                -1
% 2.88/0.98  --bmc1_symbol_reachability              true
% 2.88/0.98  --bmc1_property_lemmas                  false
% 2.88/0.98  --bmc1_k_induction                      false
% 2.88/0.98  --bmc1_non_equiv_states                 false
% 2.88/0.98  --bmc1_deadlock                         false
% 2.88/0.98  --bmc1_ucm                              false
% 2.88/0.98  --bmc1_add_unsat_core                   none
% 2.88/0.98  --bmc1_unsat_core_children              false
% 2.88/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.88/0.98  --bmc1_out_stat                         full
% 2.88/0.98  --bmc1_ground_init                      false
% 2.88/0.98  --bmc1_pre_inst_next_state              false
% 2.88/0.98  --bmc1_pre_inst_state                   false
% 2.88/0.98  --bmc1_pre_inst_reach_state             false
% 2.88/0.98  --bmc1_out_unsat_core                   false
% 2.88/0.98  --bmc1_aig_witness_out                  false
% 2.88/0.98  --bmc1_verbose                          false
% 2.88/0.98  --bmc1_dump_clauses_tptp                false
% 2.88/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.88/0.98  --bmc1_dump_file                        -
% 2.88/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.88/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.88/0.98  --bmc1_ucm_extend_mode                  1
% 2.88/0.98  --bmc1_ucm_init_mode                    2
% 2.88/0.98  --bmc1_ucm_cone_mode                    none
% 2.88/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.88/0.98  --bmc1_ucm_relax_model                  4
% 2.88/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.88/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.88/0.98  --bmc1_ucm_layered_model                none
% 2.88/0.98  --bmc1_ucm_max_lemma_size               10
% 2.88/0.98  
% 2.88/0.98  ------ AIG Options
% 2.88/0.98  
% 2.88/0.98  --aig_mode                              false
% 2.88/0.98  
% 2.88/0.98  ------ Instantiation Options
% 2.88/0.98  
% 2.88/0.98  --instantiation_flag                    true
% 2.88/0.98  --inst_sos_flag                         false
% 2.88/0.98  --inst_sos_phase                        true
% 2.88/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.88/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.88/0.98  --inst_lit_sel_side                     none
% 2.88/0.98  --inst_solver_per_active                1400
% 2.88/0.98  --inst_solver_calls_frac                1.
% 2.88/0.98  --inst_passive_queue_type               priority_queues
% 2.88/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.88/0.98  --inst_passive_queues_freq              [25;2]
% 2.88/0.98  --inst_dismatching                      true
% 2.88/0.98  --inst_eager_unprocessed_to_passive     true
% 2.88/0.98  --inst_prop_sim_given                   true
% 2.88/0.98  --inst_prop_sim_new                     false
% 2.88/0.98  --inst_subs_new                         false
% 2.88/0.98  --inst_eq_res_simp                      false
% 2.88/0.98  --inst_subs_given                       false
% 2.88/0.98  --inst_orphan_elimination               true
% 2.88/0.98  --inst_learning_loop_flag               true
% 2.88/0.98  --inst_learning_start                   3000
% 2.88/0.98  --inst_learning_factor                  2
% 2.88/0.98  --inst_start_prop_sim_after_learn       3
% 2.88/0.98  --inst_sel_renew                        solver
% 2.88/0.98  --inst_lit_activity_flag                true
% 2.88/0.98  --inst_restr_to_given                   false
% 2.88/0.98  --inst_activity_threshold               500
% 2.88/0.98  --inst_out_proof                        true
% 2.88/0.98  
% 2.88/0.98  ------ Resolution Options
% 2.88/0.98  
% 2.88/0.98  --resolution_flag                       false
% 2.88/0.98  --res_lit_sel                           adaptive
% 2.88/0.98  --res_lit_sel_side                      none
% 2.88/0.98  --res_ordering                          kbo
% 2.88/0.98  --res_to_prop_solver                    active
% 2.88/0.98  --res_prop_simpl_new                    false
% 2.88/0.98  --res_prop_simpl_given                  true
% 2.88/0.98  --res_passive_queue_type                priority_queues
% 2.88/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.88/0.98  --res_passive_queues_freq               [15;5]
% 2.88/0.98  --res_forward_subs                      full
% 2.88/0.98  --res_backward_subs                     full
% 2.88/0.98  --res_forward_subs_resolution           true
% 2.88/0.98  --res_backward_subs_resolution          true
% 2.88/0.98  --res_orphan_elimination                true
% 2.88/0.98  --res_time_limit                        2.
% 2.88/0.98  --res_out_proof                         true
% 2.88/0.98  
% 2.88/0.98  ------ Superposition Options
% 2.88/0.98  
% 2.88/0.98  --superposition_flag                    true
% 2.88/0.98  --sup_passive_queue_type                priority_queues
% 2.88/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.88/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.88/0.98  --demod_completeness_check              fast
% 2.88/0.98  --demod_use_ground                      true
% 2.88/0.98  --sup_to_prop_solver                    passive
% 2.88/0.98  --sup_prop_simpl_new                    true
% 2.88/0.98  --sup_prop_simpl_given                  true
% 2.88/0.98  --sup_fun_splitting                     false
% 2.88/0.98  --sup_smt_interval                      50000
% 2.88/0.98  
% 2.88/0.98  ------ Superposition Simplification Setup
% 2.88/0.98  
% 2.88/0.98  --sup_indices_passive                   []
% 2.88/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.88/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.98  --sup_full_bw                           [BwDemod]
% 2.88/0.98  --sup_immed_triv                        [TrivRules]
% 2.88/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.88/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.98  --sup_immed_bw_main                     []
% 2.88/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.88/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/0.98  
% 2.88/0.98  ------ Combination Options
% 2.88/0.98  
% 2.88/0.98  --comb_res_mult                         3
% 2.88/0.98  --comb_sup_mult                         2
% 2.88/0.98  --comb_inst_mult                        10
% 2.88/0.98  
% 2.88/0.98  ------ Debug Options
% 2.88/0.98  
% 2.88/0.98  --dbg_backtrace                         false
% 2.88/0.98  --dbg_dump_prop_clauses                 false
% 2.88/0.98  --dbg_dump_prop_clauses_file            -
% 2.88/0.98  --dbg_out_stat                          false
% 2.88/0.98  
% 2.88/0.98  
% 2.88/0.98  
% 2.88/0.98  
% 2.88/0.98  ------ Proving...
% 2.88/0.98  
% 2.88/0.98  
% 2.88/0.98  % SZS status Theorem for theBenchmark.p
% 2.88/0.98  
% 2.88/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.88/0.98  
% 2.88/0.98  fof(f11,conjecture,(
% 2.88/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 2.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.98  
% 2.88/0.98  fof(f12,negated_conjecture,(
% 2.88/0.98    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 2.88/0.98    inference(negated_conjecture,[],[f11])).
% 2.88/0.98  
% 2.88/0.98  fof(f22,plain,(
% 2.88/0.98    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.88/0.98    inference(ennf_transformation,[],[f12])).
% 2.88/0.98  
% 2.88/0.98  fof(f23,plain,(
% 2.88/0.98    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.88/0.98    inference(flattening,[],[f22])).
% 2.88/0.98  
% 2.88/0.98  fof(f33,plain,(
% 2.88/0.98    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.88/0.98    inference(nnf_transformation,[],[f23])).
% 2.88/0.98  
% 2.88/0.98  fof(f34,plain,(
% 2.88/0.98    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.88/0.98    inference(flattening,[],[f33])).
% 2.88/0.98  
% 2.88/0.98  fof(f35,plain,(
% 2.88/0.98    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.88/0.98    inference(rectify,[],[f34])).
% 2.88/0.98  
% 2.88/0.98  fof(f37,plain,(
% 2.88/0.98    ( ! [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (sK5 != sK6 & k1_funct_1(X1,sK5) = k1_funct_1(X1,sK6) & r2_hidden(sK6,X0) & r2_hidden(sK5,X0))) )),
% 2.88/0.98    introduced(choice_axiom,[])).
% 2.88/0.98  
% 2.88/0.98  fof(f36,plain,(
% 2.88/0.98    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK4,X2) = k1_funct_1(sK4,X3) & r2_hidden(X3,sK3) & r2_hidden(X2,sK3)) | ~v2_funct_1(sK4)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK4,X4) != k1_funct_1(sK4,X5) | ~r2_hidden(X5,sK3) | ~r2_hidden(X4,sK3)) | v2_funct_1(sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) & v1_funct_2(sK4,sK3,sK3) & v1_funct_1(sK4))),
% 2.88/0.98    introduced(choice_axiom,[])).
% 2.88/0.98  
% 2.88/0.98  fof(f38,plain,(
% 2.88/0.98    ((sK5 != sK6 & k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) & r2_hidden(sK6,sK3) & r2_hidden(sK5,sK3)) | ~v2_funct_1(sK4)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK4,X4) != k1_funct_1(sK4,X5) | ~r2_hidden(X5,sK3) | ~r2_hidden(X4,sK3)) | v2_funct_1(sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) & v1_funct_2(sK4,sK3,sK3) & v1_funct_1(sK4)),
% 2.88/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f35,f37,f36])).
% 2.88/0.98  
% 2.88/0.98  fof(f58,plain,(
% 2.88/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))),
% 2.88/0.98    inference(cnf_transformation,[],[f38])).
% 2.88/0.98  
% 2.88/0.98  fof(f3,axiom,(
% 2.88/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.98  
% 2.88/0.98  fof(f28,plain,(
% 2.88/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.88/0.98    inference(nnf_transformation,[],[f3])).
% 2.88/0.98  
% 2.88/0.98  fof(f43,plain,(
% 2.88/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.88/0.98    inference(cnf_transformation,[],[f28])).
% 2.88/0.98  
% 2.88/0.98  fof(f4,axiom,(
% 2.88/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.98  
% 2.88/0.98  fof(f14,plain,(
% 2.88/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.88/0.98    inference(ennf_transformation,[],[f4])).
% 2.88/0.98  
% 2.88/0.98  fof(f45,plain,(
% 2.88/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.88/0.98    inference(cnf_transformation,[],[f14])).
% 2.88/0.98  
% 2.88/0.98  fof(f44,plain,(
% 2.88/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.88/0.98    inference(cnf_transformation,[],[f28])).
% 2.88/0.98  
% 2.88/0.98  fof(f5,axiom,(
% 2.88/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.98  
% 2.88/0.98  fof(f46,plain,(
% 2.88/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.88/0.98    inference(cnf_transformation,[],[f5])).
% 2.88/0.98  
% 2.88/0.98  fof(f6,axiom,(
% 2.88/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 2.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.98  
% 2.88/0.98  fof(f15,plain,(
% 2.88/0.98    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.88/0.98    inference(ennf_transformation,[],[f6])).
% 2.88/0.98  
% 2.88/0.98  fof(f16,plain,(
% 2.88/0.98    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.88/0.98    inference(flattening,[],[f15])).
% 2.88/0.98  
% 2.88/0.98  fof(f29,plain,(
% 2.88/0.98    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.88/0.98    inference(nnf_transformation,[],[f16])).
% 2.88/0.98  
% 2.88/0.98  fof(f30,plain,(
% 2.88/0.98    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.88/0.98    inference(rectify,[],[f29])).
% 2.88/0.98  
% 2.88/0.98  fof(f31,plain,(
% 2.88/0.98    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK1(X0) != sK2(X0) & k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0)) & r2_hidden(sK2(X0),k1_relat_1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0))))),
% 2.88/0.98    introduced(choice_axiom,[])).
% 2.88/0.98  
% 2.88/0.98  fof(f32,plain,(
% 2.88/0.98    ! [X0] : (((v2_funct_1(X0) | (sK1(X0) != sK2(X0) & k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0)) & r2_hidden(sK2(X0),k1_relat_1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.88/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f31])).
% 2.88/0.98  
% 2.88/0.98  fof(f50,plain,(
% 2.88/0.98    ( ! [X0] : (v2_funct_1(X0) | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.88/0.98    inference(cnf_transformation,[],[f32])).
% 2.88/0.98  
% 2.88/0.98  fof(f56,plain,(
% 2.88/0.98    v1_funct_1(sK4)),
% 2.88/0.98    inference(cnf_transformation,[],[f38])).
% 2.88/0.98  
% 2.88/0.98  fof(f51,plain,(
% 2.88/0.98    ( ! [X0] : (v2_funct_1(X0) | sK1(X0) != sK2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.88/0.98    inference(cnf_transformation,[],[f32])).
% 2.88/0.98  
% 2.88/0.98  fof(f59,plain,(
% 2.88/0.98    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK4,X4) != k1_funct_1(sK4,X5) | ~r2_hidden(X5,sK3) | ~r2_hidden(X4,sK3) | v2_funct_1(sK4)) )),
% 2.88/0.98    inference(cnf_transformation,[],[f38])).
% 2.88/0.98  
% 2.88/0.98  fof(f9,axiom,(
% 2.88/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.98  
% 2.88/0.98  fof(f19,plain,(
% 2.88/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.88/0.98    inference(ennf_transformation,[],[f9])).
% 2.88/0.98  
% 2.88/0.98  fof(f54,plain,(
% 2.88/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.88/0.98    inference(cnf_transformation,[],[f19])).
% 2.88/0.98  
% 2.88/0.98  fof(f8,axiom,(
% 2.88/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.98  
% 2.88/0.98  fof(f18,plain,(
% 2.88/0.98    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.88/0.98    inference(ennf_transformation,[],[f8])).
% 2.88/0.98  
% 2.88/0.98  fof(f53,plain,(
% 2.88/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.88/0.98    inference(cnf_transformation,[],[f18])).
% 2.88/0.98  
% 2.88/0.98  fof(f49,plain,(
% 2.88/0.98    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK2(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.88/0.98    inference(cnf_transformation,[],[f32])).
% 2.88/0.98  
% 2.88/0.98  fof(f1,axiom,(
% 2.88/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.98  
% 2.88/0.98  fof(f13,plain,(
% 2.88/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.88/0.98    inference(ennf_transformation,[],[f1])).
% 2.88/0.98  
% 2.88/0.98  fof(f24,plain,(
% 2.88/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.88/0.98    inference(nnf_transformation,[],[f13])).
% 2.88/0.98  
% 2.88/0.98  fof(f25,plain,(
% 2.88/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.88/0.98    inference(rectify,[],[f24])).
% 2.88/0.98  
% 2.88/0.98  fof(f26,plain,(
% 2.88/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.88/0.98    introduced(choice_axiom,[])).
% 2.88/0.98  
% 2.88/0.98  fof(f27,plain,(
% 2.88/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.88/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 2.88/0.98  
% 2.88/0.98  fof(f39,plain,(
% 2.88/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.88/0.98    inference(cnf_transformation,[],[f27])).
% 2.88/0.98  
% 2.88/0.98  fof(f48,plain,(
% 2.88/0.98    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK1(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.88/0.98    inference(cnf_transformation,[],[f32])).
% 2.88/0.98  
% 2.88/0.98  fof(f10,axiom,(
% 2.88/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 2.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.98  
% 2.88/0.98  fof(f20,plain,(
% 2.88/0.98    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.88/0.98    inference(ennf_transformation,[],[f10])).
% 2.88/0.98  
% 2.88/0.98  fof(f21,plain,(
% 2.88/0.98    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.88/0.98    inference(flattening,[],[f20])).
% 2.88/0.98  
% 2.88/0.98  fof(f55,plain,(
% 2.88/0.98    ( ! [X2,X0,X3,X1] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.88/0.98    inference(cnf_transformation,[],[f21])).
% 2.88/0.98  
% 2.88/0.98  fof(f57,plain,(
% 2.88/0.98    v1_funct_2(sK4,sK3,sK3)),
% 2.88/0.98    inference(cnf_transformation,[],[f38])).
% 2.88/0.98  
% 2.88/0.98  fof(f61,plain,(
% 2.88/0.98    r2_hidden(sK6,sK3) | ~v2_funct_1(sK4)),
% 2.88/0.98    inference(cnf_transformation,[],[f38])).
% 2.88/0.98  
% 2.88/0.98  fof(f62,plain,(
% 2.88/0.98    k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) | ~v2_funct_1(sK4)),
% 2.88/0.98    inference(cnf_transformation,[],[f38])).
% 2.88/0.98  
% 2.88/0.98  fof(f7,axiom,(
% 2.88/0.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.98  
% 2.88/0.98  fof(f17,plain,(
% 2.88/0.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.88/0.98    inference(ennf_transformation,[],[f7])).
% 2.88/0.98  
% 2.88/0.98  fof(f52,plain,(
% 2.88/0.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.88/0.98    inference(cnf_transformation,[],[f17])).
% 2.88/0.98  
% 2.88/0.98  fof(f2,axiom,(
% 2.88/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.98  
% 2.88/0.98  fof(f42,plain,(
% 2.88/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.88/0.98    inference(cnf_transformation,[],[f2])).
% 2.88/0.98  
% 2.88/0.98  fof(f60,plain,(
% 2.88/0.98    r2_hidden(sK5,sK3) | ~v2_funct_1(sK4)),
% 2.88/0.98    inference(cnf_transformation,[],[f38])).
% 2.88/0.98  
% 2.88/0.98  fof(f47,plain,(
% 2.88/0.98    ( ! [X4,X0,X3] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.88/0.98    inference(cnf_transformation,[],[f32])).
% 2.88/0.98  
% 2.88/0.98  fof(f63,plain,(
% 2.88/0.98    sK5 != sK6 | ~v2_funct_1(sK4)),
% 2.88/0.98    inference(cnf_transformation,[],[f38])).
% 2.88/0.98  
% 2.88/0.98  cnf(c_22,negated_conjecture,
% 2.88/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) ),
% 2.88/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_2925,plain,
% 2.88/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) = iProver_top ),
% 2.88/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_5,plain,
% 2.88/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.88/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_2935,plain,
% 2.88/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.88/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.88/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_3343,plain,
% 2.88/0.98      ( r1_tarski(sK4,k2_zfmisc_1(sK3,sK3)) = iProver_top ),
% 2.88/0.98      inference(superposition,[status(thm)],[c_2925,c_2935]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_6,plain,
% 2.88/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.88/0.98      | ~ v1_relat_1(X1)
% 2.88/0.98      | v1_relat_1(X0) ),
% 2.88/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_4,plain,
% 2.88/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.88/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_195,plain,
% 2.88/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.88/0.98      inference(prop_impl,[status(thm)],[c_4]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_196,plain,
% 2.88/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.88/0.98      inference(renaming,[status(thm)],[c_195]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_247,plain,
% 2.88/0.98      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.88/0.98      inference(bin_hyper_res,[status(thm)],[c_6,c_196]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_2924,plain,
% 2.88/0.98      ( r1_tarski(X0,X1) != iProver_top
% 2.88/0.98      | v1_relat_1(X1) != iProver_top
% 2.88/0.98      | v1_relat_1(X0) = iProver_top ),
% 2.88/0.98      inference(predicate_to_equality,[status(thm)],[c_247]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_4641,plain,
% 2.88/0.98      ( v1_relat_1(k2_zfmisc_1(sK3,sK3)) != iProver_top
% 2.88/0.98      | v1_relat_1(sK4) = iProver_top ),
% 2.88/0.98      inference(superposition,[status(thm)],[c_3343,c_2924]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_7,plain,
% 2.88/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.88/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_2934,plain,
% 2.88/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.88/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_4848,plain,
% 2.88/0.98      ( v1_relat_1(sK4) = iProver_top ),
% 2.88/0.98      inference(forward_subsumption_resolution,
% 2.88/0.98                [status(thm)],
% 2.88/0.98                [c_4641,c_2934]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_9,plain,
% 2.88/0.98      ( ~ v1_funct_1(X0)
% 2.88/0.98      | v2_funct_1(X0)
% 2.88/0.98      | ~ v1_relat_1(X0)
% 2.88/0.98      | k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK1(X0)) ),
% 2.88/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_24,negated_conjecture,
% 2.88/0.98      ( v1_funct_1(sK4) ),
% 2.88/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_391,plain,
% 2.88/0.98      ( v2_funct_1(X0)
% 2.88/0.98      | ~ v1_relat_1(X0)
% 2.88/0.98      | k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK1(X0))
% 2.88/0.98      | sK4 != X0 ),
% 2.88/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_24]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_392,plain,
% 2.88/0.98      ( v2_funct_1(sK4)
% 2.88/0.98      | ~ v1_relat_1(sK4)
% 2.88/0.98      | k1_funct_1(sK4,sK2(sK4)) = k1_funct_1(sK4,sK1(sK4)) ),
% 2.88/0.98      inference(unflattening,[status(thm)],[c_391]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_2919,plain,
% 2.88/0.98      ( k1_funct_1(sK4,sK2(sK4)) = k1_funct_1(sK4,sK1(sK4))
% 2.88/0.98      | v2_funct_1(sK4) = iProver_top
% 2.88/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.88/0.98      inference(predicate_to_equality,[status(thm)],[c_392]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_4850,plain,
% 2.88/0.98      ( k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK2(sK4))
% 2.88/0.98      | v2_funct_1(sK4) = iProver_top ),
% 2.88/0.98      inference(superposition,[status(thm)],[c_4848,c_2919]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_25,plain,
% 2.88/0.98      ( v1_funct_1(sK4) = iProver_top ),
% 2.88/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_56,plain,
% 2.88/0.98      ( k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK1(X0))
% 2.88/0.98      | v1_funct_1(X0) != iProver_top
% 2.88/0.98      | v2_funct_1(X0) = iProver_top
% 2.88/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.88/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_58,plain,
% 2.88/0.98      ( k1_funct_1(sK4,sK2(sK4)) = k1_funct_1(sK4,sK1(sK4))
% 2.88/0.98      | v1_funct_1(sK4) != iProver_top
% 2.88/0.98      | v2_funct_1(sK4) = iProver_top
% 2.88/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.88/0.98      inference(instantiation,[status(thm)],[c_56]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_8,plain,
% 2.88/0.98      ( ~ v1_funct_1(X0)
% 2.88/0.98      | v2_funct_1(X0)
% 2.88/0.98      | ~ v1_relat_1(X0)
% 2.88/0.98      | sK2(X0) != sK1(X0) ),
% 2.88/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_59,plain,
% 2.88/0.98      ( sK2(X0) != sK1(X0)
% 2.88/0.98      | v1_funct_1(X0) != iProver_top
% 2.88/0.98      | v2_funct_1(X0) = iProver_top
% 2.88/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.88/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_61,plain,
% 2.88/0.98      ( sK2(sK4) != sK1(sK4)
% 2.88/0.98      | v1_funct_1(sK4) != iProver_top
% 2.88/0.98      | v2_funct_1(sK4) = iProver_top
% 2.88/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.88/0.98      inference(instantiation,[status(thm)],[c_59]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_21,negated_conjecture,
% 2.88/0.98      ( ~ r2_hidden(X0,sK3)
% 2.88/0.98      | ~ r2_hidden(X1,sK3)
% 2.88/0.98      | v2_funct_1(sK4)
% 2.88/0.98      | X1 = X0
% 2.88/0.98      | k1_funct_1(sK4,X1) != k1_funct_1(sK4,X0) ),
% 2.88/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_3325,plain,
% 2.88/0.98      ( ~ r2_hidden(sK2(sK4),sK3)
% 2.88/0.98      | ~ r2_hidden(sK1(sK4),sK3)
% 2.88/0.98      | v2_funct_1(sK4)
% 2.88/0.98      | k1_funct_1(sK4,sK2(sK4)) != k1_funct_1(sK4,sK1(sK4))
% 2.88/0.98      | sK2(sK4) = sK1(sK4) ),
% 2.88/0.98      inference(instantiation,[status(thm)],[c_21]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_3326,plain,
% 2.88/0.98      ( k1_funct_1(sK4,sK2(sK4)) != k1_funct_1(sK4,sK1(sK4))
% 2.88/0.98      | sK2(sK4) = sK1(sK4)
% 2.88/0.98      | r2_hidden(sK2(sK4),sK3) != iProver_top
% 2.88/0.98      | r2_hidden(sK1(sK4),sK3) != iProver_top
% 2.88/0.98      | v2_funct_1(sK4) = iProver_top ),
% 2.88/0.98      inference(predicate_to_equality,[status(thm)],[c_3325]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_15,plain,
% 2.88/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.88/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_2931,plain,
% 2.88/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.88/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.88/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_3719,plain,
% 2.88/0.98      ( k1_relset_1(sK3,sK3,sK4) = k1_relat_1(sK4) ),
% 2.88/0.98      inference(superposition,[status(thm)],[c_2925,c_2931]) ).
% 2.88/0.98  
% 2.88/0.98  cnf(c_14,plain,
% 2.88/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/0.98      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 2.88/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2932,plain,
% 2.88/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.88/0.99      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3855,plain,
% 2.88/0.99      ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top
% 2.88/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_3719,c_2932]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_27,plain,
% 2.88/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4192,plain,
% 2.88/0.99      ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_3855,c_27]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4197,plain,
% 2.88/0.99      ( r1_tarski(k1_relat_1(sK4),sK3) = iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_4192,c_2935]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_10,plain,
% 2.88/0.99      ( r2_hidden(sK2(X0),k1_relat_1(X0))
% 2.88/0.99      | ~ v1_funct_1(X0)
% 2.88/0.99      | v2_funct_1(X0)
% 2.88/0.99      | ~ v1_relat_1(X0) ),
% 2.88/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_378,plain,
% 2.88/0.99      ( r2_hidden(sK2(X0),k1_relat_1(X0))
% 2.88/0.99      | v2_funct_1(X0)
% 2.88/0.99      | ~ v1_relat_1(X0)
% 2.88/0.99      | sK4 != X0 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_24]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_379,plain,
% 2.88/0.99      ( r2_hidden(sK2(sK4),k1_relat_1(sK4))
% 2.88/0.99      | v2_funct_1(sK4)
% 2.88/0.99      | ~ v1_relat_1(sK4) ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_378]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2920,plain,
% 2.88/0.99      ( r2_hidden(sK2(sK4),k1_relat_1(sK4)) = iProver_top
% 2.88/0.99      | v2_funct_1(sK4) = iProver_top
% 2.88/0.99      | v1_relat_1(sK4) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_379]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2,plain,
% 2.88/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.88/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2938,plain,
% 2.88/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.88/0.99      | r2_hidden(X0,X2) = iProver_top
% 2.88/0.99      | r1_tarski(X1,X2) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3885,plain,
% 2.88/0.99      ( r2_hidden(sK2(sK4),X0) = iProver_top
% 2.88/0.99      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 2.88/0.99      | v2_funct_1(sK4) = iProver_top
% 2.88/0.99      | v1_relat_1(sK4) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_2920,c_2938]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4565,plain,
% 2.88/0.99      ( r2_hidden(sK2(sK4),sK3) = iProver_top
% 2.88/0.99      | v2_funct_1(sK4) = iProver_top
% 2.88/0.99      | v1_relat_1(sK4) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_4197,c_3885]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_11,plain,
% 2.88/0.99      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 2.88/0.99      | ~ v1_funct_1(X0)
% 2.88/0.99      | v2_funct_1(X0)
% 2.88/0.99      | ~ v1_relat_1(X0) ),
% 2.88/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_365,plain,
% 2.88/0.99      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 2.88/0.99      | v2_funct_1(X0)
% 2.88/0.99      | ~ v1_relat_1(X0)
% 2.88/0.99      | sK4 != X0 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_24]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_366,plain,
% 2.88/0.99      ( r2_hidden(sK1(sK4),k1_relat_1(sK4))
% 2.88/0.99      | v2_funct_1(sK4)
% 2.88/0.99      | ~ v1_relat_1(sK4) ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_365]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2921,plain,
% 2.88/0.99      ( r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top
% 2.88/0.99      | v2_funct_1(sK4) = iProver_top
% 2.88/0.99      | v1_relat_1(sK4) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_366]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3884,plain,
% 2.88/0.99      ( r2_hidden(sK1(sK4),X0) = iProver_top
% 2.88/0.99      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 2.88/0.99      | v2_funct_1(sK4) = iProver_top
% 2.88/0.99      | v1_relat_1(sK4) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_2921,c_2938]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4566,plain,
% 2.88/0.99      ( r2_hidden(sK1(sK4),sK3) = iProver_top
% 2.88/0.99      | v2_funct_1(sK4) = iProver_top
% 2.88/0.99      | v1_relat_1(sK4) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_4197,c_3884]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4929,plain,
% 2.88/0.99      ( v2_funct_1(sK4) = iProver_top ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_4850,c_25,c_58,c_61,c_3326,c_4565,c_4566,c_4848]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_16,plain,
% 2.88/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.88/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/0.99      | ~ r2_hidden(X3,X1)
% 2.88/0.99      | ~ v1_funct_1(X0)
% 2.88/0.99      | ~ v2_funct_1(X0)
% 2.88/0.99      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
% 2.88/0.99      | k1_xboole_0 = X2 ),
% 2.88/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_23,negated_conjecture,
% 2.88/0.99      ( v1_funct_2(sK4,sK3,sK3) ),
% 2.88/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_336,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/0.99      | ~ r2_hidden(X3,X1)
% 2.88/0.99      | ~ v1_funct_1(X0)
% 2.88/0.99      | ~ v2_funct_1(X0)
% 2.88/0.99      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
% 2.88/0.99      | sK3 != X2
% 2.88/0.99      | sK3 != X1
% 2.88/0.99      | sK4 != X0
% 2.88/0.99      | k1_xboole_0 = X2 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_23]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_337,plain,
% 2.88/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
% 2.88/0.99      | ~ r2_hidden(X0,sK3)
% 2.88/0.99      | ~ v1_funct_1(sK4)
% 2.88/0.99      | ~ v2_funct_1(sK4)
% 2.88/0.99      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0
% 2.88/0.99      | k1_xboole_0 = sK3 ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_336]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_341,plain,
% 2.88/0.99      ( ~ r2_hidden(X0,sK3)
% 2.88/0.99      | ~ v2_funct_1(sK4)
% 2.88/0.99      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0
% 2.88/0.99      | k1_xboole_0 = sK3 ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_337,c_24,c_22]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2302,plain,
% 2.88/0.99      ( ~ v2_funct_1(sK4) | sP1_iProver_split | k1_xboole_0 = sK3 ),
% 2.88/0.99      inference(splitting,
% 2.88/0.99                [splitting(split),new_symbols(definition,[])],
% 2.88/0.99                [c_341]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2922,plain,
% 2.88/0.99      ( k1_xboole_0 = sK3
% 2.88/0.99      | v2_funct_1(sK4) != iProver_top
% 2.88/0.99      | sP1_iProver_split = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_2302]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4936,plain,
% 2.88/0.99      ( sK3 = k1_xboole_0 | sP1_iProver_split = iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_4929,c_2922]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_19,negated_conjecture,
% 2.88/0.99      ( r2_hidden(sK6,sK3) | ~ v2_funct_1(sK4) ),
% 2.88/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2928,plain,
% 2.88/0.99      ( r2_hidden(sK6,sK3) = iProver_top
% 2.88/0.99      | v2_funct_1(sK4) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2301,plain,
% 2.88/0.99      ( ~ r2_hidden(X0,sK3)
% 2.88/0.99      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0
% 2.88/0.99      | ~ sP1_iProver_split ),
% 2.88/0.99      inference(splitting,
% 2.88/0.99                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.88/0.99                [c_341]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2923,plain,
% 2.88/0.99      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0
% 2.88/0.99      | r2_hidden(X0,sK3) != iProver_top
% 2.88/0.99      | sP1_iProver_split != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_2301]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3543,plain,
% 2.88/0.99      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK6)) = sK6
% 2.88/0.99      | v2_funct_1(sK4) != iProver_top
% 2.88/0.99      | sP1_iProver_split != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_2928,c_2923]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4938,plain,
% 2.88/0.99      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK6)) = sK6
% 2.88/0.99      | sP1_iProver_split != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_4929,c_3543]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_18,negated_conjecture,
% 2.88/0.99      ( ~ v2_funct_1(sK4) | k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
% 2.88/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2929,plain,
% 2.88/0.99      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
% 2.88/0.99      | v2_funct_1(sK4) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4940,plain,
% 2.88/0.99      ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5) ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_4929,c_2929]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4947,plain,
% 2.88/0.99      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK6
% 2.88/0.99      | sP1_iProver_split != iProver_top ),
% 2.88/0.99      inference(light_normalisation,[status(thm)],[c_4938,c_4940]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_5587,plain,
% 2.88/0.99      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK6
% 2.88/0.99      | sK3 = k1_xboole_0 ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_4936,c_4947]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_13,plain,
% 2.88/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.88/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2933,plain,
% 2.88/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.88/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3313,plain,
% 2.88/0.99      ( r1_tarski(sK3,sK6) != iProver_top
% 2.88/0.99      | v2_funct_1(sK4) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_2928,c_2933]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3323,plain,
% 2.88/0.99      ( ~ r1_tarski(sK3,sK6) | ~ v2_funct_1(sK4) ),
% 2.88/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3313]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4931,plain,
% 2.88/0.99      ( v2_funct_1(sK4) ),
% 2.88/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4929]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2306,plain,
% 2.88/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 2.88/0.99      theory(equality) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3647,plain,
% 2.88/0.99      ( ~ r1_tarski(X0,sK6) | r1_tarski(sK3,sK6) | sK3 != X0 ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_2306]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_5616,plain,
% 2.88/0.99      ( r1_tarski(sK3,sK6)
% 2.88/0.99      | ~ r1_tarski(k1_xboole_0,sK6)
% 2.88/0.99      | sK3 != k1_xboole_0 ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_3647]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3,plain,
% 2.88/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.88/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_5617,plain,
% 2.88/0.99      ( r1_tarski(k1_xboole_0,sK6) ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_6104,plain,
% 2.88/0.99      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK6 ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_5587,c_3323,c_4931,c_5616,c_5617]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_20,negated_conjecture,
% 2.88/0.99      ( r2_hidden(sK5,sK3) | ~ v2_funct_1(sK4) ),
% 2.88/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2927,plain,
% 2.88/0.99      ( r2_hidden(sK5,sK3) = iProver_top
% 2.88/0.99      | v2_funct_1(sK4) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3544,plain,
% 2.88/0.99      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK5
% 2.88/0.99      | v2_funct_1(sK4) != iProver_top
% 2.88/0.99      | sP1_iProver_split != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_2927,c_2923]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4937,plain,
% 2.88/0.99      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK5
% 2.88/0.99      | sP1_iProver_split != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_4929,c_3544]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_6107,plain,
% 2.88/0.99      ( sK6 = sK5 | sP1_iProver_split != iProver_top ),
% 2.88/0.99      inference(demodulation,[status(thm)],[c_6104,c_4937]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4849,plain,
% 2.88/0.99      ( v1_relat_1(sK4) ),
% 2.88/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4848]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_12,plain,
% 2.88/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.88/0.99      | ~ r2_hidden(X2,k1_relat_1(X1))
% 2.88/0.99      | ~ v1_funct_1(X1)
% 2.88/0.99      | ~ v2_funct_1(X1)
% 2.88/0.99      | ~ v1_relat_1(X1)
% 2.88/0.99      | X0 = X2
% 2.88/0.99      | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
% 2.88/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_417,plain,
% 2.88/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.88/0.99      | ~ r2_hidden(X2,k1_relat_1(X1))
% 2.88/0.99      | ~ v2_funct_1(X1)
% 2.88/0.99      | ~ v1_relat_1(X1)
% 2.88/0.99      | X2 = X0
% 2.88/0.99      | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
% 2.88/0.99      | sK4 != X1 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_418,plain,
% 2.88/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.88/0.99      | ~ r2_hidden(X1,k1_relat_1(sK4))
% 2.88/0.99      | ~ v2_funct_1(sK4)
% 2.88/0.99      | ~ v1_relat_1(sK4)
% 2.88/0.99      | X0 = X1
% 2.88/0.99      | k1_funct_1(sK4,X0) != k1_funct_1(sK4,X1) ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_417]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2299,plain,
% 2.88/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.88/0.99      | ~ r2_hidden(X1,k1_relat_1(sK4))
% 2.88/0.99      | X0 = X1
% 2.88/0.99      | k1_funct_1(sK4,X0) != k1_funct_1(sK4,X1)
% 2.88/0.99      | ~ sP0_iProver_split ),
% 2.88/0.99      inference(splitting,
% 2.88/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.88/0.99                [c_418]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3752,plain,
% 2.88/0.99      ( ~ r2_hidden(sK2(sK4),k1_relat_1(sK4))
% 2.88/0.99      | ~ r2_hidden(sK1(sK4),k1_relat_1(sK4))
% 2.88/0.99      | ~ sP0_iProver_split
% 2.88/0.99      | k1_funct_1(sK4,sK1(sK4)) != k1_funct_1(sK4,sK2(sK4))
% 2.88/0.99      | sK1(sK4) = sK2(sK4) ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_2299]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3753,plain,
% 2.88/0.99      ( k1_funct_1(sK4,sK1(sK4)) != k1_funct_1(sK4,sK2(sK4))
% 2.88/0.99      | sK1(sK4) = sK2(sK4)
% 2.88/0.99      | r2_hidden(sK2(sK4),k1_relat_1(sK4)) != iProver_top
% 2.88/0.99      | r2_hidden(sK1(sK4),k1_relat_1(sK4)) != iProver_top
% 2.88/0.99      | sP0_iProver_split != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_3752]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2305,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3328,plain,
% 2.88/0.99      ( sK2(sK4) != X0 | sK2(sK4) = sK1(sK4) | sK1(sK4) != X0 ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_2305]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3534,plain,
% 2.88/0.99      ( sK2(sK4) != sK2(sK4)
% 2.88/0.99      | sK2(sK4) = sK1(sK4)
% 2.88/0.99      | sK1(sK4) != sK2(sK4) ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_3328]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2300,plain,
% 2.88/0.99      ( ~ v2_funct_1(sK4) | ~ v1_relat_1(sK4) | sP0_iProver_split ),
% 2.88/0.99      inference(splitting,
% 2.88/0.99                [splitting(split),new_symbols(definition,[])],
% 2.88/0.99                [c_418]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2332,plain,
% 2.88/0.99      ( v2_funct_1(sK4) != iProver_top
% 2.88/0.99      | v1_relat_1(sK4) != iProver_top
% 2.88/0.99      | sP0_iProver_split = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_2300]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2304,plain,( X0 = X0 ),theory(equality) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2331,plain,
% 2.88/0.99      ( sK4 = sK4 ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_2304]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2314,plain,( X0 != X1 | sK2(X0) = sK2(X1) ),theory(equality) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2326,plain,
% 2.88/0.99      ( sK2(sK4) = sK2(sK4) | sK4 != sK4 ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_2314]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_17,negated_conjecture,
% 2.88/0.99      ( ~ v2_funct_1(sK4) | sK5 != sK6 ),
% 2.88/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1024,plain,
% 2.88/0.99      ( r2_hidden(sK1(sK4),k1_relat_1(sK4))
% 2.88/0.99      | ~ v1_relat_1(sK4)
% 2.88/0.99      | sK6 != sK5 ),
% 2.88/0.99      inference(resolution,[status(thm)],[c_366,c_17]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1025,plain,
% 2.88/0.99      ( sK6 != sK5
% 2.88/0.99      | r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top
% 2.88/0.99      | v1_relat_1(sK4) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_1024]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_933,plain,
% 2.88/0.99      ( r2_hidden(sK2(sK4),k1_relat_1(sK4))
% 2.88/0.99      | ~ v1_relat_1(sK4)
% 2.88/0.99      | sK6 != sK5 ),
% 2.88/0.99      inference(resolution,[status(thm)],[c_379,c_17]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_934,plain,
% 2.88/0.99      ( sK6 != sK5
% 2.88/0.99      | r2_hidden(sK2(sK4),k1_relat_1(sK4)) = iProver_top
% 2.88/0.99      | v1_relat_1(sK4) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_933]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_842,plain,
% 2.88/0.99      ( ~ v1_relat_1(sK4)
% 2.88/0.99      | k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK2(sK4))
% 2.88/0.99      | sK6 != sK5 ),
% 2.88/0.99      inference(resolution,[status(thm)],[c_392,c_17]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_404,plain,
% 2.88/0.99      ( v2_funct_1(X0)
% 2.88/0.99      | ~ v1_relat_1(X0)
% 2.88/0.99      | sK2(X0) != sK1(X0)
% 2.88/0.99      | sK4 != X0 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_24]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_405,plain,
% 2.88/0.99      ( v2_funct_1(sK4) | ~ v1_relat_1(sK4) | sK2(sK4) != sK1(sK4) ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_404]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_751,plain,
% 2.88/0.99      ( ~ v1_relat_1(sK4) | sK2(sK4) != sK1(sK4) | sK6 != sK5 ),
% 2.88/0.99      inference(resolution,[status(thm)],[c_405,c_17]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_752,plain,
% 2.88/0.99      ( sK2(sK4) != sK1(sK4)
% 2.88/0.99      | sK6 != sK5
% 2.88/0.99      | v1_relat_1(sK4) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_751]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(contradiction,plain,
% 2.88/0.99      ( $false ),
% 2.88/0.99      inference(minisat,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_6107,c_5617,c_5616,c_4936,c_4931,c_4929,c_4849,c_4848,
% 2.88/0.99                 c_3753,c_3534,c_3323,c_2332,c_2331,c_2326,c_1025,c_934,
% 2.88/0.99                 c_842,c_752]) ).
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.88/0.99  
% 2.88/0.99  ------                               Statistics
% 2.88/0.99  
% 2.88/0.99  ------ General
% 2.88/0.99  
% 2.88/0.99  abstr_ref_over_cycles:                  0
% 2.88/0.99  abstr_ref_under_cycles:                 0
% 2.88/0.99  gc_basic_clause_elim:                   0
% 2.88/0.99  forced_gc_time:                         0
% 2.88/0.99  parsing_time:                           0.009
% 2.88/0.99  unif_index_cands_time:                  0.
% 2.88/0.99  unif_index_add_time:                    0.
% 2.88/0.99  orderings_time:                         0.
% 2.88/0.99  out_proof_time:                         0.01
% 2.88/0.99  total_time:                             0.176
% 2.88/0.99  num_of_symbols:                         54
% 2.88/0.99  num_of_terms:                           3475
% 2.88/0.99  
% 2.88/0.99  ------ Preprocessing
% 2.88/0.99  
% 2.88/0.99  num_of_splits:                          2
% 2.88/0.99  num_of_split_atoms:                     2
% 2.88/0.99  num_of_reused_defs:                     0
% 2.88/0.99  num_eq_ax_congr_red:                    22
% 2.88/0.99  num_of_sem_filtered_clauses:            1
% 2.88/0.99  num_of_subtypes:                        0
% 2.88/0.99  monotx_restored_types:                  0
% 2.88/0.99  sat_num_of_epr_types:                   0
% 2.88/0.99  sat_num_of_non_cyclic_types:            0
% 2.88/0.99  sat_guarded_non_collapsed_types:        0
% 2.88/0.99  num_pure_diseq_elim:                    0
% 2.88/0.99  simp_replaced_by:                       0
% 2.88/0.99  res_preprocessed:                       127
% 2.88/0.99  prep_upred:                             0
% 2.88/0.99  prep_unflattend:                        48
% 2.88/0.99  smt_new_axioms:                         0
% 2.88/0.99  pred_elim_cands:                        5
% 2.88/0.99  pred_elim:                              2
% 2.88/0.99  pred_elim_cl:                           2
% 2.88/0.99  pred_elim_cycles:                       6
% 2.88/0.99  merged_defs:                            8
% 2.88/0.99  merged_defs_ncl:                        0
% 2.88/0.99  bin_hyper_res:                          9
% 2.88/0.99  prep_cycles:                            4
% 2.88/0.99  pred_elim_time:                         0.028
% 2.88/0.99  splitting_time:                         0.
% 2.88/0.99  sem_filter_time:                        0.
% 2.88/0.99  monotx_time:                            0.
% 2.88/0.99  subtype_inf_time:                       0.
% 2.88/0.99  
% 2.88/0.99  ------ Problem properties
% 2.88/0.99  
% 2.88/0.99  clauses:                                25
% 2.88/0.99  conjectures:                            6
% 2.88/0.99  epr:                                    9
% 2.88/0.99  horn:                                   19
% 2.88/0.99  ground:                                 11
% 2.88/0.99  unary:                                  3
% 2.88/0.99  binary:                                 11
% 2.88/0.99  lits:                                   62
% 2.88/0.99  lits_eq:                                11
% 2.88/0.99  fd_pure:                                0
% 2.88/0.99  fd_pseudo:                              0
% 2.88/0.99  fd_cond:                                0
% 2.88/0.99  fd_pseudo_cond:                         2
% 2.88/0.99  ac_symbols:                             0
% 2.88/0.99  
% 2.88/0.99  ------ Propositional Solver
% 2.88/0.99  
% 2.88/0.99  prop_solver_calls:                      30
% 2.88/0.99  prop_fast_solver_calls:                 1220
% 2.88/0.99  smt_solver_calls:                       0
% 2.88/0.99  smt_fast_solver_calls:                  0
% 2.88/0.99  prop_num_of_clauses:                    1648
% 2.88/0.99  prop_preprocess_simplified:             5759
% 2.88/0.99  prop_fo_subsumed:                       23
% 2.88/0.99  prop_solver_time:                       0.
% 2.88/0.99  smt_solver_time:                        0.
% 2.88/0.99  smt_fast_solver_time:                   0.
% 2.88/0.99  prop_fast_solver_time:                  0.
% 2.88/0.99  prop_unsat_core_time:                   0.
% 2.88/0.99  
% 2.88/0.99  ------ QBF
% 2.88/0.99  
% 2.88/0.99  qbf_q_res:                              0
% 2.88/0.99  qbf_num_tautologies:                    0
% 2.88/0.99  qbf_prep_cycles:                        0
% 2.88/0.99  
% 2.88/0.99  ------ BMC1
% 2.88/0.99  
% 2.88/0.99  bmc1_current_bound:                     -1
% 2.88/0.99  bmc1_last_solved_bound:                 -1
% 2.88/0.99  bmc1_unsat_core_size:                   -1
% 2.88/0.99  bmc1_unsat_core_parents_size:           -1
% 2.88/0.99  bmc1_merge_next_fun:                    0
% 2.88/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.88/0.99  
% 2.88/0.99  ------ Instantiation
% 2.88/0.99  
% 2.88/0.99  inst_num_of_clauses:                    432
% 2.88/0.99  inst_num_in_passive:                    82
% 2.88/0.99  inst_num_in_active:                     250
% 2.88/0.99  inst_num_in_unprocessed:                100
% 2.88/0.99  inst_num_of_loops:                      380
% 2.88/0.99  inst_num_of_learning_restarts:          0
% 2.88/0.99  inst_num_moves_active_passive:          125
% 2.88/0.99  inst_lit_activity:                      0
% 2.88/0.99  inst_lit_activity_moves:                0
% 2.88/0.99  inst_num_tautologies:                   0
% 2.88/0.99  inst_num_prop_implied:                  0
% 2.88/0.99  inst_num_existing_simplified:           0
% 2.88/0.99  inst_num_eq_res_simplified:             0
% 2.88/0.99  inst_num_child_elim:                    0
% 2.88/0.99  inst_num_of_dismatching_blockings:      36
% 2.88/0.99  inst_num_of_non_proper_insts:           363
% 2.88/0.99  inst_num_of_duplicates:                 0
% 2.88/0.99  inst_inst_num_from_inst_to_res:         0
% 2.88/0.99  inst_dismatching_checking_time:         0.
% 2.88/0.99  
% 2.88/0.99  ------ Resolution
% 2.88/0.99  
% 2.88/0.99  res_num_of_clauses:                     0
% 2.88/0.99  res_num_in_passive:                     0
% 2.88/0.99  res_num_in_active:                      0
% 2.88/0.99  res_num_of_loops:                       131
% 2.88/0.99  res_forward_subset_subsumed:            26
% 2.88/0.99  res_backward_subset_subsumed:           0
% 2.88/0.99  res_forward_subsumed:                   0
% 2.88/0.99  res_backward_subsumed:                  1
% 2.88/0.99  res_forward_subsumption_resolution:     0
% 2.88/0.99  res_backward_subsumption_resolution:    0
% 2.88/0.99  res_clause_to_clause_subsumption:       259
% 2.88/0.99  res_orphan_elimination:                 0
% 2.88/0.99  res_tautology_del:                      61
% 2.88/0.99  res_num_eq_res_simplified:              0
% 2.88/0.99  res_num_sel_changes:                    0
% 2.88/0.99  res_moves_from_active_to_pass:          0
% 2.88/0.99  
% 2.88/0.99  ------ Superposition
% 2.88/0.99  
% 2.88/0.99  sup_time_total:                         0.
% 2.88/0.99  sup_time_generating:                    0.
% 2.88/0.99  sup_time_sim_full:                      0.
% 2.88/0.99  sup_time_sim_immed:                     0.
% 2.88/0.99  
% 2.88/0.99  sup_num_of_clauses:                     101
% 2.88/0.99  sup_num_in_active:                      66
% 2.88/0.99  sup_num_in_passive:                     35
% 2.88/0.99  sup_num_of_loops:                       75
% 2.88/0.99  sup_fw_superposition:                   64
% 2.88/0.99  sup_bw_superposition:                   50
% 2.88/0.99  sup_immediate_simplified:               15
% 2.88/0.99  sup_given_eliminated:                   0
% 2.88/0.99  comparisons_done:                       0
% 2.88/0.99  comparisons_avoided:                    0
% 2.88/0.99  
% 2.88/0.99  ------ Simplifications
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  sim_fw_subset_subsumed:                 10
% 2.88/0.99  sim_bw_subset_subsumed:                 5
% 2.88/0.99  sim_fw_subsumed:                        1
% 2.88/0.99  sim_bw_subsumed:                        1
% 2.88/0.99  sim_fw_subsumption_res:                 2
% 2.88/0.99  sim_bw_subsumption_res:                 0
% 2.88/0.99  sim_tautology_del:                      2
% 2.88/0.99  sim_eq_tautology_del:                   4
% 2.88/0.99  sim_eq_res_simp:                        0
% 2.88/0.99  sim_fw_demodulated:                     1
% 2.88/0.99  sim_bw_demodulated:                     4
% 2.88/0.99  sim_light_normalised:                   3
% 2.88/0.99  sim_joinable_taut:                      0
% 2.88/0.99  sim_joinable_simp:                      0
% 2.88/0.99  sim_ac_normalised:                      0
% 2.88/0.99  sim_smt_subsumption:                    0
% 2.88/0.99  
%------------------------------------------------------------------------------
