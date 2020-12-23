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
% DateTime   : Thu Dec  3 12:06:52 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :  160 (1580 expanded)
%              Number of clauses        :  104 ( 462 expanded)
%              Number of leaves         :   16 ( 308 expanded)
%              Depth                    :   22
%              Number of atoms          :  605 (11223 expanded)
%              Number of equality atoms :  232 (3481 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

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

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

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
    inference(ennf_transformation,[],[f11])).

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

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f34,plain,(
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

fof(f33,plain,
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

fof(f35,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f32,f34,f33])).

fof(f52,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f51,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

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

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).

fof(f43,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK0(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f44,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK1(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f45,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | sK0(X0) != sK1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f54,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK2)
      | v2_funct_1(sK3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f58,plain,
    ( sK4 != sK5
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f42,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_312,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
    | sK2 != X2
    | sK2 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_313,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ r2_hidden(X0,sK2)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_317,plain,
    ( ~ r2_hidden(X0,sK2)
    | ~ v2_funct_1(sK3)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_313,c_22,c_20])).

cnf(c_2400,plain,
    ( ~ v2_funct_1(sK3)
    | sP1_iProver_split
    | k1_xboole_0 = sK2 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_317])).

cnf(c_2951,plain,
    ( k1_xboole_0 = sK2
    | v2_funct_1(sK3) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2400])).

cnf(c_23,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_25,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_9,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_48,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_50,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_8,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_51,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_53,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_51])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_54,plain,
    ( k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_56,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK1(X0) != sK0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_57,plain,
    ( sK1(X0) != sK0(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_59,plain,
    ( sK1(sK3) != sK0(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_2437,plain,
    ( k1_xboole_0 = sK2
    | v2_funct_1(sK3) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2400])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3128,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3129,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3128])).

cnf(c_13,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_341,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_13,c_5])).

cnf(c_345,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_341,c_12])).

cnf(c_346,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_345])).

cnf(c_3140,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | r1_tarski(k1_relat_1(sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_346])).

cnf(c_3141,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3140])).

cnf(c_19,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(X1,sK2)
    | v2_funct_1(sK3)
    | X1 = X0
    | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3208,plain,
    ( ~ r2_hidden(sK1(sK3),sK2)
    | ~ r2_hidden(sK0(sK3),sK2)
    | v2_funct_1(sK3)
    | k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
    | sK1(sK3) = sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_3209,plain,
    ( k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
    | sK1(sK3) = sK0(sK3)
    | r2_hidden(sK1(sK3),sK2) != iProver_top
    | r2_hidden(sK0(sK3),sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3208])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_179,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_180,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_179])).

cnf(c_228,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_1,c_180])).

cnf(c_3169,plain,
    ( r2_hidden(sK0(sK3),X0)
    | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ r1_tarski(k1_relat_1(sK3),X0) ),
    inference(instantiation,[status(thm)],[c_228])).

cnf(c_3294,plain,
    ( ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | r2_hidden(sK0(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_3169])).

cnf(c_3295,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK0(sK3),sK2) = iProver_top
    | r1_tarski(k1_relat_1(sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3294])).

cnf(c_3182,plain,
    ( r2_hidden(sK1(sK3),X0)
    | ~ r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | ~ r1_tarski(k1_relat_1(sK3),X0) ),
    inference(instantiation,[status(thm)],[c_228])).

cnf(c_3303,plain,
    ( ~ r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | r2_hidden(sK1(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_3182])).

cnf(c_3304,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK1(sK3),sK2) = iProver_top
    | r1_tarski(k1_relat_1(sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3303])).

cnf(c_3630,plain,
    ( k1_xboole_0 = sK2
    | sP1_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2951,c_23,c_25,c_50,c_53,c_56,c_59,c_2437,c_3129,c_3141,c_3209,c_3295,c_3304])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2956,plain,
    ( r2_hidden(sK4,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2399,plain,
    ( ~ r2_hidden(X0,sK2)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_317])).

cnf(c_2952,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | r2_hidden(X0,sK2) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2399])).

cnf(c_3573,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | v2_funct_1(sK3) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2956,c_2952])).

cnf(c_3623,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | sP1_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3573,c_23,c_25,c_50,c_53,c_56,c_59,c_3129,c_3141,c_3209,c_3295,c_3304])).

cnf(c_3636,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3630,c_3623])).

cnf(c_566,plain,
    ( v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_22])).

cnf(c_567,plain,
    ( v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
    inference(unflattening,[status(thm)],[c_566])).

cnf(c_2947,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_567])).

cnf(c_3689,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2947,c_23,c_25,c_50,c_53,c_56,c_59,c_3129,c_3141,c_3209,c_3295,c_3304])).

cnf(c_16,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2958,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3695,plain,
    ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_3689,c_2958])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2957,plain,
    ( r2_hidden(sK5,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3572,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
    | v2_funct_1(sK3) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2957,c_2952])).

cnf(c_3589,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
    | sP1_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3572,c_23,c_25,c_50,c_53,c_56,c_59,c_3129,c_3141,c_3209,c_3295,c_3304])).

cnf(c_3733,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
    | sP1_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_3695,c_3589])).

cnf(c_3810,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3630,c_3733])).

cnf(c_4124,plain,
    ( sK2 = k1_xboole_0
    | sK5 = sK4 ),
    inference(superposition,[status(thm)],[c_3636,c_3810])).

cnf(c_579,plain,
    ( v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK1(X0) != sK0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_22])).

cnf(c_580,plain,
    ( v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK1(sK3) != sK0(sK3) ),
    inference(unflattening,[status(thm)],[c_579])).

cnf(c_15,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | sK4 != sK5 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_818,plain,
    ( ~ v1_relat_1(sK3)
    | sK1(sK3) != sK0(sK3)
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_580,c_15])).

cnf(c_909,plain,
    ( ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_567,c_15])).

cnf(c_553,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_22])).

cnf(c_554,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_553])).

cnf(c_1000,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_554,c_15])).

cnf(c_540,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_541,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_540])).

cnf(c_1091,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_541,c_15])).

cnf(c_2412,plain,
    ( X0 != X1
    | sK1(X0) = sK1(X1) ),
    theory(equality)).

cnf(c_2424,plain,
    ( sK1(sK3) = sK1(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2412])).

cnf(c_2402,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2429,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_2402])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_592,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | X2 = X0
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_593,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
    inference(unflattening,[status(thm)],[c_592])).

cnf(c_2398,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_593])).

cnf(c_2403,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3211,plain,
    ( sK1(sK3) != X0
    | sK1(sK3) = sK0(sK3)
    | sK0(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_2403])).

cnf(c_3400,plain,
    ( sK1(sK3) != sK1(sK3)
    | sK1(sK3) = sK0(sK3)
    | sK0(sK3) != sK1(sK3) ),
    inference(instantiation,[status(thm)],[c_3211])).

cnf(c_3691,plain,
    ( v2_funct_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3689])).

cnf(c_2397,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_593])).

cnf(c_3721,plain,
    ( ~ r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ sP0_iProver_split
    | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(sK3))
    | sK0(sK3) = sK1(sK3) ),
    inference(instantiation,[status(thm)],[c_2397])).

cnf(c_4140,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4124,c_20,c_818,c_909,c_1000,c_1091,c_2424,c_2429,c_2398,c_3128,c_3400,c_3691,c_3721])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2961,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3320,plain,
    ( r1_tarski(sK2,sK4) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2956,c_2961])).

cnf(c_3491,plain,
    ( r1_tarski(sK2,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3320,c_23,c_25,c_50,c_53,c_56,c_59,c_3129,c_3141,c_3209,c_3295,c_3304])).

cnf(c_4146,plain,
    ( r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4140,c_3491])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2964,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4399,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4146,c_2964])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.35  % Computer   : n025.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % WCLimit    : 600
% 0.12/0.35  % DateTime   : Tue Dec  1 20:41:06 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 2.01/1.10  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.10  
% 2.01/1.10  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.01/1.10  
% 2.01/1.10  ------  iProver source info
% 2.01/1.10  
% 2.01/1.10  git: date: 2020-06-30 10:37:57 +0100
% 2.01/1.10  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.01/1.10  git: non_committed_changes: false
% 2.01/1.10  git: last_make_outside_of_git: false
% 2.01/1.10  
% 2.01/1.10  ------ 
% 2.01/1.10  
% 2.01/1.10  ------ Input Options
% 2.01/1.10  
% 2.01/1.10  --out_options                           all
% 2.01/1.10  --tptp_safe_out                         true
% 2.01/1.10  --problem_path                          ""
% 2.01/1.10  --include_path                          ""
% 2.01/1.10  --clausifier                            res/vclausify_rel
% 2.01/1.10  --clausifier_options                    --mode clausify
% 2.01/1.10  --stdin                                 false
% 2.01/1.10  --stats_out                             all
% 2.01/1.10  
% 2.01/1.10  ------ General Options
% 2.01/1.10  
% 2.01/1.10  --fof                                   false
% 2.01/1.10  --time_out_real                         305.
% 2.01/1.10  --time_out_virtual                      -1.
% 2.01/1.10  --symbol_type_check                     false
% 2.01/1.10  --clausify_out                          false
% 2.01/1.10  --sig_cnt_out                           false
% 2.01/1.10  --trig_cnt_out                          false
% 2.01/1.10  --trig_cnt_out_tolerance                1.
% 2.01/1.10  --trig_cnt_out_sk_spl                   false
% 2.01/1.10  --abstr_cl_out                          false
% 2.01/1.10  
% 2.01/1.10  ------ Global Options
% 2.01/1.10  
% 2.01/1.10  --schedule                              default
% 2.01/1.10  --add_important_lit                     false
% 2.01/1.10  --prop_solver_per_cl                    1000
% 2.01/1.10  --min_unsat_core                        false
% 2.01/1.10  --soft_assumptions                      false
% 2.01/1.10  --soft_lemma_size                       3
% 2.01/1.10  --prop_impl_unit_size                   0
% 2.01/1.10  --prop_impl_unit                        []
% 2.01/1.10  --share_sel_clauses                     true
% 2.01/1.10  --reset_solvers                         false
% 2.01/1.10  --bc_imp_inh                            [conj_cone]
% 2.01/1.10  --conj_cone_tolerance                   3.
% 2.01/1.10  --extra_neg_conj                        none
% 2.01/1.10  --large_theory_mode                     true
% 2.01/1.10  --prolific_symb_bound                   200
% 2.01/1.10  --lt_threshold                          2000
% 2.01/1.10  --clause_weak_htbl                      true
% 2.01/1.10  --gc_record_bc_elim                     false
% 2.01/1.10  
% 2.01/1.10  ------ Preprocessing Options
% 2.01/1.10  
% 2.01/1.10  --preprocessing_flag                    true
% 2.01/1.10  --time_out_prep_mult                    0.1
% 2.01/1.10  --splitting_mode                        input
% 2.01/1.10  --splitting_grd                         true
% 2.01/1.10  --splitting_cvd                         false
% 2.01/1.10  --splitting_cvd_svl                     false
% 2.01/1.10  --splitting_nvd                         32
% 2.01/1.10  --sub_typing                            true
% 2.01/1.10  --prep_gs_sim                           true
% 2.01/1.10  --prep_unflatten                        true
% 2.01/1.10  --prep_res_sim                          true
% 2.01/1.10  --prep_upred                            true
% 2.01/1.10  --prep_sem_filter                       exhaustive
% 2.01/1.10  --prep_sem_filter_out                   false
% 2.01/1.10  --pred_elim                             true
% 2.01/1.10  --res_sim_input                         true
% 2.01/1.10  --eq_ax_congr_red                       true
% 2.01/1.10  --pure_diseq_elim                       true
% 2.01/1.10  --brand_transform                       false
% 2.01/1.10  --non_eq_to_eq                          false
% 2.01/1.10  --prep_def_merge                        true
% 2.01/1.10  --prep_def_merge_prop_impl              false
% 2.01/1.10  --prep_def_merge_mbd                    true
% 2.01/1.10  --prep_def_merge_tr_red                 false
% 2.01/1.10  --prep_def_merge_tr_cl                  false
% 2.01/1.10  --smt_preprocessing                     true
% 2.01/1.10  --smt_ac_axioms                         fast
% 2.01/1.10  --preprocessed_out                      false
% 2.01/1.10  --preprocessed_stats                    false
% 2.01/1.10  
% 2.01/1.10  ------ Abstraction refinement Options
% 2.01/1.10  
% 2.01/1.10  --abstr_ref                             []
% 2.01/1.10  --abstr_ref_prep                        false
% 2.01/1.10  --abstr_ref_until_sat                   false
% 2.01/1.10  --abstr_ref_sig_restrict                funpre
% 2.01/1.10  --abstr_ref_af_restrict_to_split_sk     false
% 2.01/1.10  --abstr_ref_under                       []
% 2.01/1.10  
% 2.01/1.10  ------ SAT Options
% 2.01/1.10  
% 2.01/1.10  --sat_mode                              false
% 2.01/1.10  --sat_fm_restart_options                ""
% 2.01/1.10  --sat_gr_def                            false
% 2.01/1.10  --sat_epr_types                         true
% 2.01/1.10  --sat_non_cyclic_types                  false
% 2.01/1.10  --sat_finite_models                     false
% 2.01/1.10  --sat_fm_lemmas                         false
% 2.01/1.10  --sat_fm_prep                           false
% 2.01/1.10  --sat_fm_uc_incr                        true
% 2.01/1.10  --sat_out_model                         small
% 2.01/1.10  --sat_out_clauses                       false
% 2.01/1.10  
% 2.01/1.10  ------ QBF Options
% 2.01/1.10  
% 2.01/1.10  --qbf_mode                              false
% 2.01/1.10  --qbf_elim_univ                         false
% 2.01/1.10  --qbf_dom_inst                          none
% 2.01/1.10  --qbf_dom_pre_inst                      false
% 2.01/1.10  --qbf_sk_in                             false
% 2.01/1.10  --qbf_pred_elim                         true
% 2.01/1.10  --qbf_split                             512
% 2.01/1.10  
% 2.01/1.10  ------ BMC1 Options
% 2.01/1.10  
% 2.01/1.10  --bmc1_incremental                      false
% 2.01/1.10  --bmc1_axioms                           reachable_all
% 2.01/1.10  --bmc1_min_bound                        0
% 2.01/1.10  --bmc1_max_bound                        -1
% 2.01/1.10  --bmc1_max_bound_default                -1
% 2.01/1.10  --bmc1_symbol_reachability              true
% 2.01/1.10  --bmc1_property_lemmas                  false
% 2.01/1.10  --bmc1_k_induction                      false
% 2.01/1.10  --bmc1_non_equiv_states                 false
% 2.01/1.10  --bmc1_deadlock                         false
% 2.01/1.10  --bmc1_ucm                              false
% 2.01/1.10  --bmc1_add_unsat_core                   none
% 2.01/1.10  --bmc1_unsat_core_children              false
% 2.01/1.10  --bmc1_unsat_core_extrapolate_axioms    false
% 2.01/1.10  --bmc1_out_stat                         full
% 2.01/1.10  --bmc1_ground_init                      false
% 2.01/1.10  --bmc1_pre_inst_next_state              false
% 2.01/1.10  --bmc1_pre_inst_state                   false
% 2.01/1.10  --bmc1_pre_inst_reach_state             false
% 2.01/1.10  --bmc1_out_unsat_core                   false
% 2.01/1.10  --bmc1_aig_witness_out                  false
% 2.01/1.10  --bmc1_verbose                          false
% 2.01/1.10  --bmc1_dump_clauses_tptp                false
% 2.01/1.10  --bmc1_dump_unsat_core_tptp             false
% 2.01/1.10  --bmc1_dump_file                        -
% 2.01/1.10  --bmc1_ucm_expand_uc_limit              128
% 2.01/1.10  --bmc1_ucm_n_expand_iterations          6
% 2.01/1.10  --bmc1_ucm_extend_mode                  1
% 2.01/1.10  --bmc1_ucm_init_mode                    2
% 2.01/1.10  --bmc1_ucm_cone_mode                    none
% 2.01/1.10  --bmc1_ucm_reduced_relation_type        0
% 2.01/1.10  --bmc1_ucm_relax_model                  4
% 2.01/1.10  --bmc1_ucm_full_tr_after_sat            true
% 2.01/1.10  --bmc1_ucm_expand_neg_assumptions       false
% 2.01/1.10  --bmc1_ucm_layered_model                none
% 2.01/1.10  --bmc1_ucm_max_lemma_size               10
% 2.01/1.10  
% 2.01/1.10  ------ AIG Options
% 2.01/1.10  
% 2.01/1.10  --aig_mode                              false
% 2.01/1.10  
% 2.01/1.10  ------ Instantiation Options
% 2.01/1.10  
% 2.01/1.10  --instantiation_flag                    true
% 2.01/1.10  --inst_sos_flag                         false
% 2.01/1.10  --inst_sos_phase                        true
% 2.01/1.10  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.01/1.10  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.01/1.10  --inst_lit_sel_side                     num_symb
% 2.01/1.10  --inst_solver_per_active                1400
% 2.01/1.10  --inst_solver_calls_frac                1.
% 2.01/1.10  --inst_passive_queue_type               priority_queues
% 2.01/1.10  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.01/1.10  --inst_passive_queues_freq              [25;2]
% 2.01/1.10  --inst_dismatching                      true
% 2.01/1.10  --inst_eager_unprocessed_to_passive     true
% 2.01/1.10  --inst_prop_sim_given                   true
% 2.01/1.10  --inst_prop_sim_new                     false
% 2.01/1.10  --inst_subs_new                         false
% 2.01/1.10  --inst_eq_res_simp                      false
% 2.01/1.10  --inst_subs_given                       false
% 2.01/1.10  --inst_orphan_elimination               true
% 2.01/1.10  --inst_learning_loop_flag               true
% 2.01/1.10  --inst_learning_start                   3000
% 2.01/1.10  --inst_learning_factor                  2
% 2.01/1.10  --inst_start_prop_sim_after_learn       3
% 2.01/1.10  --inst_sel_renew                        solver
% 2.01/1.10  --inst_lit_activity_flag                true
% 2.01/1.10  --inst_restr_to_given                   false
% 2.01/1.10  --inst_activity_threshold               500
% 2.01/1.10  --inst_out_proof                        true
% 2.01/1.10  
% 2.01/1.10  ------ Resolution Options
% 2.01/1.10  
% 2.01/1.10  --resolution_flag                       true
% 2.01/1.10  --res_lit_sel                           adaptive
% 2.01/1.10  --res_lit_sel_side                      none
% 2.01/1.10  --res_ordering                          kbo
% 2.01/1.10  --res_to_prop_solver                    active
% 2.01/1.10  --res_prop_simpl_new                    false
% 2.01/1.10  --res_prop_simpl_given                  true
% 2.01/1.10  --res_passive_queue_type                priority_queues
% 2.01/1.10  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.01/1.10  --res_passive_queues_freq               [15;5]
% 2.01/1.10  --res_forward_subs                      full
% 2.01/1.10  --res_backward_subs                     full
% 2.01/1.10  --res_forward_subs_resolution           true
% 2.01/1.10  --res_backward_subs_resolution          true
% 2.01/1.10  --res_orphan_elimination                true
% 2.01/1.10  --res_time_limit                        2.
% 2.01/1.10  --res_out_proof                         true
% 2.01/1.10  
% 2.01/1.10  ------ Superposition Options
% 2.01/1.10  
% 2.01/1.10  --superposition_flag                    true
% 2.01/1.10  --sup_passive_queue_type                priority_queues
% 2.01/1.10  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.01/1.10  --sup_passive_queues_freq               [8;1;4]
% 2.01/1.10  --demod_completeness_check              fast
% 2.01/1.10  --demod_use_ground                      true
% 2.01/1.10  --sup_to_prop_solver                    passive
% 2.01/1.10  --sup_prop_simpl_new                    true
% 2.01/1.10  --sup_prop_simpl_given                  true
% 2.01/1.10  --sup_fun_splitting                     false
% 2.01/1.10  --sup_smt_interval                      50000
% 2.01/1.10  
% 2.01/1.10  ------ Superposition Simplification Setup
% 2.01/1.10  
% 2.01/1.10  --sup_indices_passive                   []
% 2.01/1.10  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.01/1.10  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.01/1.10  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.01/1.10  --sup_full_triv                         [TrivRules;PropSubs]
% 2.01/1.10  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.01/1.10  --sup_full_bw                           [BwDemod]
% 2.01/1.10  --sup_immed_triv                        [TrivRules]
% 2.01/1.10  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.01/1.10  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.01/1.10  --sup_immed_bw_main                     []
% 2.01/1.10  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.01/1.10  --sup_input_triv                        [Unflattening;TrivRules]
% 2.01/1.10  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.01/1.10  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.01/1.10  
% 2.01/1.10  ------ Combination Options
% 2.01/1.10  
% 2.01/1.10  --comb_res_mult                         3
% 2.01/1.10  --comb_sup_mult                         2
% 2.01/1.10  --comb_inst_mult                        10
% 2.01/1.10  
% 2.01/1.10  ------ Debug Options
% 2.01/1.10  
% 2.01/1.10  --dbg_backtrace                         false
% 2.01/1.10  --dbg_dump_prop_clauses                 false
% 2.01/1.10  --dbg_dump_prop_clauses_file            -
% 2.01/1.10  --dbg_out_stat                          false
% 2.01/1.10  ------ Parsing...
% 2.01/1.10  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.01/1.10  
% 2.01/1.10  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.01/1.10  
% 2.01/1.10  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.01/1.10  
% 2.01/1.10  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.01/1.10  ------ Proving...
% 2.01/1.10  ------ Problem Properties 
% 2.01/1.10  
% 2.01/1.10  
% 2.01/1.10  clauses                                 21
% 2.01/1.10  conjectures                             6
% 2.01/1.10  EPR                                     8
% 2.01/1.10  Horn                                    16
% 2.01/1.10  unary                                   2
% 2.01/1.10  binary                                  9
% 2.01/1.10  lits                                    54
% 2.01/1.10  lits eq                                 10
% 2.01/1.10  fd_pure                                 0
% 2.01/1.10  fd_pseudo                               0
% 2.01/1.10  fd_cond                                 0
% 2.01/1.10  fd_pseudo_cond                          2
% 2.01/1.10  AC symbols                              0
% 2.01/1.10  
% 2.01/1.10  ------ Schedule dynamic 5 is on 
% 2.01/1.10  
% 2.01/1.10  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.01/1.10  
% 2.01/1.10  
% 2.01/1.10  ------ 
% 2.01/1.10  Current options:
% 2.01/1.10  ------ 
% 2.01/1.10  
% 2.01/1.10  ------ Input Options
% 2.01/1.10  
% 2.01/1.10  --out_options                           all
% 2.01/1.10  --tptp_safe_out                         true
% 2.01/1.10  --problem_path                          ""
% 2.01/1.10  --include_path                          ""
% 2.01/1.10  --clausifier                            res/vclausify_rel
% 2.01/1.10  --clausifier_options                    --mode clausify
% 2.01/1.10  --stdin                                 false
% 2.01/1.10  --stats_out                             all
% 2.01/1.10  
% 2.01/1.10  ------ General Options
% 2.01/1.10  
% 2.01/1.10  --fof                                   false
% 2.01/1.10  --time_out_real                         305.
% 2.01/1.10  --time_out_virtual                      -1.
% 2.01/1.10  --symbol_type_check                     false
% 2.01/1.10  --clausify_out                          false
% 2.01/1.10  --sig_cnt_out                           false
% 2.01/1.10  --trig_cnt_out                          false
% 2.01/1.10  --trig_cnt_out_tolerance                1.
% 2.01/1.10  --trig_cnt_out_sk_spl                   false
% 2.01/1.10  --abstr_cl_out                          false
% 2.01/1.10  
% 2.01/1.10  ------ Global Options
% 2.01/1.10  
% 2.01/1.10  --schedule                              default
% 2.01/1.10  --add_important_lit                     false
% 2.01/1.10  --prop_solver_per_cl                    1000
% 2.01/1.10  --min_unsat_core                        false
% 2.01/1.10  --soft_assumptions                      false
% 2.01/1.10  --soft_lemma_size                       3
% 2.01/1.10  --prop_impl_unit_size                   0
% 2.01/1.10  --prop_impl_unit                        []
% 2.01/1.10  --share_sel_clauses                     true
% 2.01/1.10  --reset_solvers                         false
% 2.01/1.10  --bc_imp_inh                            [conj_cone]
% 2.01/1.10  --conj_cone_tolerance                   3.
% 2.01/1.10  --extra_neg_conj                        none
% 2.01/1.10  --large_theory_mode                     true
% 2.01/1.10  --prolific_symb_bound                   200
% 2.01/1.10  --lt_threshold                          2000
% 2.01/1.10  --clause_weak_htbl                      true
% 2.01/1.10  --gc_record_bc_elim                     false
% 2.01/1.10  
% 2.01/1.10  ------ Preprocessing Options
% 2.01/1.10  
% 2.01/1.10  --preprocessing_flag                    true
% 2.01/1.10  --time_out_prep_mult                    0.1
% 2.01/1.10  --splitting_mode                        input
% 2.01/1.10  --splitting_grd                         true
% 2.01/1.10  --splitting_cvd                         false
% 2.01/1.10  --splitting_cvd_svl                     false
% 2.01/1.10  --splitting_nvd                         32
% 2.01/1.10  --sub_typing                            true
% 2.01/1.10  --prep_gs_sim                           true
% 2.01/1.10  --prep_unflatten                        true
% 2.01/1.10  --prep_res_sim                          true
% 2.01/1.10  --prep_upred                            true
% 2.01/1.10  --prep_sem_filter                       exhaustive
% 2.01/1.10  --prep_sem_filter_out                   false
% 2.01/1.10  --pred_elim                             true
% 2.01/1.10  --res_sim_input                         true
% 2.01/1.10  --eq_ax_congr_red                       true
% 2.01/1.10  --pure_diseq_elim                       true
% 2.01/1.10  --brand_transform                       false
% 2.01/1.10  --non_eq_to_eq                          false
% 2.01/1.10  --prep_def_merge                        true
% 2.01/1.10  --prep_def_merge_prop_impl              false
% 2.01/1.10  --prep_def_merge_mbd                    true
% 2.01/1.10  --prep_def_merge_tr_red                 false
% 2.01/1.10  --prep_def_merge_tr_cl                  false
% 2.01/1.10  --smt_preprocessing                     true
% 2.01/1.10  --smt_ac_axioms                         fast
% 2.01/1.10  --preprocessed_out                      false
% 2.01/1.10  --preprocessed_stats                    false
% 2.01/1.10  
% 2.01/1.10  ------ Abstraction refinement Options
% 2.01/1.10  
% 2.01/1.10  --abstr_ref                             []
% 2.01/1.10  --abstr_ref_prep                        false
% 2.01/1.10  --abstr_ref_until_sat                   false
% 2.01/1.10  --abstr_ref_sig_restrict                funpre
% 2.01/1.10  --abstr_ref_af_restrict_to_split_sk     false
% 2.01/1.10  --abstr_ref_under                       []
% 2.01/1.10  
% 2.01/1.10  ------ SAT Options
% 2.01/1.10  
% 2.01/1.10  --sat_mode                              false
% 2.01/1.10  --sat_fm_restart_options                ""
% 2.01/1.10  --sat_gr_def                            false
% 2.01/1.10  --sat_epr_types                         true
% 2.01/1.10  --sat_non_cyclic_types                  false
% 2.01/1.10  --sat_finite_models                     false
% 2.01/1.10  --sat_fm_lemmas                         false
% 2.01/1.10  --sat_fm_prep                           false
% 2.01/1.10  --sat_fm_uc_incr                        true
% 2.01/1.10  --sat_out_model                         small
% 2.01/1.10  --sat_out_clauses                       false
% 2.01/1.10  
% 2.01/1.10  ------ QBF Options
% 2.01/1.10  
% 2.01/1.10  --qbf_mode                              false
% 2.01/1.10  --qbf_elim_univ                         false
% 2.01/1.10  --qbf_dom_inst                          none
% 2.01/1.10  --qbf_dom_pre_inst                      false
% 2.01/1.10  --qbf_sk_in                             false
% 2.01/1.10  --qbf_pred_elim                         true
% 2.01/1.10  --qbf_split                             512
% 2.01/1.10  
% 2.01/1.10  ------ BMC1 Options
% 2.01/1.10  
% 2.01/1.10  --bmc1_incremental                      false
% 2.01/1.10  --bmc1_axioms                           reachable_all
% 2.01/1.10  --bmc1_min_bound                        0
% 2.01/1.10  --bmc1_max_bound                        -1
% 2.01/1.10  --bmc1_max_bound_default                -1
% 2.01/1.10  --bmc1_symbol_reachability              true
% 2.01/1.10  --bmc1_property_lemmas                  false
% 2.01/1.10  --bmc1_k_induction                      false
% 2.01/1.10  --bmc1_non_equiv_states                 false
% 2.01/1.10  --bmc1_deadlock                         false
% 2.01/1.10  --bmc1_ucm                              false
% 2.01/1.10  --bmc1_add_unsat_core                   none
% 2.01/1.10  --bmc1_unsat_core_children              false
% 2.01/1.10  --bmc1_unsat_core_extrapolate_axioms    false
% 2.01/1.10  --bmc1_out_stat                         full
% 2.01/1.10  --bmc1_ground_init                      false
% 2.01/1.10  --bmc1_pre_inst_next_state              false
% 2.01/1.10  --bmc1_pre_inst_state                   false
% 2.01/1.10  --bmc1_pre_inst_reach_state             false
% 2.01/1.10  --bmc1_out_unsat_core                   false
% 2.01/1.10  --bmc1_aig_witness_out                  false
% 2.01/1.10  --bmc1_verbose                          false
% 2.01/1.10  --bmc1_dump_clauses_tptp                false
% 2.01/1.10  --bmc1_dump_unsat_core_tptp             false
% 2.01/1.10  --bmc1_dump_file                        -
% 2.01/1.10  --bmc1_ucm_expand_uc_limit              128
% 2.01/1.10  --bmc1_ucm_n_expand_iterations          6
% 2.01/1.10  --bmc1_ucm_extend_mode                  1
% 2.01/1.10  --bmc1_ucm_init_mode                    2
% 2.01/1.10  --bmc1_ucm_cone_mode                    none
% 2.01/1.10  --bmc1_ucm_reduced_relation_type        0
% 2.01/1.10  --bmc1_ucm_relax_model                  4
% 2.01/1.10  --bmc1_ucm_full_tr_after_sat            true
% 2.01/1.10  --bmc1_ucm_expand_neg_assumptions       false
% 2.01/1.10  --bmc1_ucm_layered_model                none
% 2.01/1.10  --bmc1_ucm_max_lemma_size               10
% 2.01/1.10  
% 2.01/1.10  ------ AIG Options
% 2.01/1.10  
% 2.01/1.10  --aig_mode                              false
% 2.01/1.10  
% 2.01/1.10  ------ Instantiation Options
% 2.01/1.10  
% 2.01/1.10  --instantiation_flag                    true
% 2.01/1.10  --inst_sos_flag                         false
% 2.01/1.10  --inst_sos_phase                        true
% 2.01/1.10  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.01/1.10  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.01/1.10  --inst_lit_sel_side                     none
% 2.01/1.10  --inst_solver_per_active                1400
% 2.01/1.10  --inst_solver_calls_frac                1.
% 2.01/1.10  --inst_passive_queue_type               priority_queues
% 2.01/1.10  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.01/1.10  --inst_passive_queues_freq              [25;2]
% 2.01/1.10  --inst_dismatching                      true
% 2.01/1.10  --inst_eager_unprocessed_to_passive     true
% 2.01/1.10  --inst_prop_sim_given                   true
% 2.01/1.10  --inst_prop_sim_new                     false
% 2.01/1.10  --inst_subs_new                         false
% 2.01/1.10  --inst_eq_res_simp                      false
% 2.01/1.10  --inst_subs_given                       false
% 2.01/1.10  --inst_orphan_elimination               true
% 2.01/1.10  --inst_learning_loop_flag               true
% 2.01/1.10  --inst_learning_start                   3000
% 2.01/1.10  --inst_learning_factor                  2
% 2.01/1.10  --inst_start_prop_sim_after_learn       3
% 2.01/1.10  --inst_sel_renew                        solver
% 2.01/1.10  --inst_lit_activity_flag                true
% 2.01/1.10  --inst_restr_to_given                   false
% 2.01/1.10  --inst_activity_threshold               500
% 2.01/1.10  --inst_out_proof                        true
% 2.01/1.10  
% 2.01/1.10  ------ Resolution Options
% 2.01/1.10  
% 2.01/1.10  --resolution_flag                       false
% 2.01/1.10  --res_lit_sel                           adaptive
% 2.01/1.10  --res_lit_sel_side                      none
% 2.01/1.10  --res_ordering                          kbo
% 2.01/1.10  --res_to_prop_solver                    active
% 2.01/1.10  --res_prop_simpl_new                    false
% 2.01/1.10  --res_prop_simpl_given                  true
% 2.01/1.10  --res_passive_queue_type                priority_queues
% 2.01/1.10  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.01/1.10  --res_passive_queues_freq               [15;5]
% 2.01/1.10  --res_forward_subs                      full
% 2.01/1.10  --res_backward_subs                     full
% 2.01/1.10  --res_forward_subs_resolution           true
% 2.01/1.10  --res_backward_subs_resolution          true
% 2.01/1.10  --res_orphan_elimination                true
% 2.01/1.10  --res_time_limit                        2.
% 2.01/1.10  --res_out_proof                         true
% 2.01/1.10  
% 2.01/1.10  ------ Superposition Options
% 2.01/1.10  
% 2.01/1.10  --superposition_flag                    true
% 2.01/1.10  --sup_passive_queue_type                priority_queues
% 2.01/1.10  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.01/1.10  --sup_passive_queues_freq               [8;1;4]
% 2.01/1.10  --demod_completeness_check              fast
% 2.01/1.10  --demod_use_ground                      true
% 2.01/1.10  --sup_to_prop_solver                    passive
% 2.01/1.10  --sup_prop_simpl_new                    true
% 2.01/1.10  --sup_prop_simpl_given                  true
% 2.01/1.10  --sup_fun_splitting                     false
% 2.01/1.10  --sup_smt_interval                      50000
% 2.01/1.10  
% 2.01/1.10  ------ Superposition Simplification Setup
% 2.01/1.10  
% 2.01/1.10  --sup_indices_passive                   []
% 2.01/1.10  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.01/1.10  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.01/1.10  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.01/1.10  --sup_full_triv                         [TrivRules;PropSubs]
% 2.01/1.10  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.01/1.10  --sup_full_bw                           [BwDemod]
% 2.01/1.10  --sup_immed_triv                        [TrivRules]
% 2.01/1.10  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.01/1.10  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.01/1.10  --sup_immed_bw_main                     []
% 2.01/1.10  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.01/1.10  --sup_input_triv                        [Unflattening;TrivRules]
% 2.01/1.10  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.01/1.10  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.01/1.10  
% 2.01/1.10  ------ Combination Options
% 2.01/1.10  
% 2.01/1.10  --comb_res_mult                         3
% 2.01/1.10  --comb_sup_mult                         2
% 2.01/1.10  --comb_inst_mult                        10
% 2.01/1.10  
% 2.01/1.10  ------ Debug Options
% 2.01/1.10  
% 2.01/1.10  --dbg_backtrace                         false
% 2.01/1.10  --dbg_dump_prop_clauses                 false
% 2.01/1.10  --dbg_dump_prop_clauses_file            -
% 2.01/1.10  --dbg_out_stat                          false
% 2.01/1.10  
% 2.01/1.10  
% 2.01/1.10  
% 2.01/1.10  
% 2.01/1.10  ------ Proving...
% 2.01/1.10  
% 2.01/1.10  
% 2.01/1.10  % SZS status Theorem for theBenchmark.p
% 2.01/1.10  
% 2.01/1.10   Resolution empty clause
% 2.01/1.10  
% 2.01/1.10  % SZS output start CNFRefutation for theBenchmark.p
% 2.01/1.10  
% 2.01/1.10  fof(f9,axiom,(
% 2.01/1.10    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 2.01/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.01/1.10  
% 2.01/1.10  fof(f20,plain,(
% 2.01/1.10    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.01/1.10    inference(ennf_transformation,[],[f9])).
% 2.01/1.10  
% 2.01/1.10  fof(f21,plain,(
% 2.01/1.10    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.01/1.10    inference(flattening,[],[f20])).
% 2.01/1.10  
% 2.01/1.10  fof(f50,plain,(
% 2.01/1.10    ( ! [X2,X0,X3,X1] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.01/1.10    inference(cnf_transformation,[],[f21])).
% 2.01/1.10  
% 2.01/1.10  fof(f10,conjecture,(
% 2.01/1.10    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 2.01/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.01/1.10  
% 2.01/1.10  fof(f11,negated_conjecture,(
% 2.01/1.10    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 2.01/1.10    inference(negated_conjecture,[],[f10])).
% 2.01/1.10  
% 2.01/1.10  fof(f22,plain,(
% 2.01/1.10    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.01/1.10    inference(ennf_transformation,[],[f11])).
% 2.01/1.10  
% 2.01/1.10  fof(f23,plain,(
% 2.01/1.10    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.01/1.10    inference(flattening,[],[f22])).
% 2.01/1.10  
% 2.01/1.10  fof(f30,plain,(
% 2.01/1.10    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.01/1.10    inference(nnf_transformation,[],[f23])).
% 2.01/1.10  
% 2.01/1.10  fof(f31,plain,(
% 2.01/1.10    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.01/1.10    inference(flattening,[],[f30])).
% 2.01/1.10  
% 2.01/1.10  fof(f32,plain,(
% 2.01/1.10    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.01/1.10    inference(rectify,[],[f31])).
% 2.01/1.10  
% 2.01/1.10  fof(f34,plain,(
% 2.01/1.10    ( ! [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (sK4 != sK5 & k1_funct_1(X1,sK4) = k1_funct_1(X1,sK5) & r2_hidden(sK5,X0) & r2_hidden(sK4,X0))) )),
% 2.01/1.10    introduced(choice_axiom,[])).
% 2.01/1.10  
% 2.01/1.10  fof(f33,plain,(
% 2.01/1.10    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3) & r2_hidden(X3,sK2) & r2_hidden(X2,sK2)) | ~v2_funct_1(sK3)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 2.01/1.10    introduced(choice_axiom,[])).
% 2.01/1.10  
% 2.01/1.10  fof(f35,plain,(
% 2.01/1.10    ((sK4 != sK5 & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) & r2_hidden(sK5,sK2) & r2_hidden(sK4,sK2)) | ~v2_funct_1(sK3)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 2.01/1.10    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f32,f34,f33])).
% 2.01/1.10  
% 2.01/1.10  fof(f52,plain,(
% 2.01/1.10    v1_funct_2(sK3,sK2,sK2)),
% 2.01/1.10    inference(cnf_transformation,[],[f35])).
% 2.01/1.10  
% 2.01/1.10  fof(f51,plain,(
% 2.01/1.10    v1_funct_1(sK3)),
% 2.01/1.10    inference(cnf_transformation,[],[f35])).
% 2.01/1.10  
% 2.01/1.10  fof(f53,plain,(
% 2.01/1.10    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 2.01/1.10    inference(cnf_transformation,[],[f35])).
% 2.01/1.10  
% 2.01/1.10  fof(f5,axiom,(
% 2.01/1.10    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 2.01/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.01/1.10  
% 2.01/1.10  fof(f15,plain,(
% 2.01/1.10    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.01/1.10    inference(ennf_transformation,[],[f5])).
% 2.01/1.10  
% 2.01/1.10  fof(f16,plain,(
% 2.01/1.10    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.01/1.10    inference(flattening,[],[f15])).
% 2.01/1.10  
% 2.01/1.10  fof(f26,plain,(
% 2.01/1.10    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.01/1.10    inference(nnf_transformation,[],[f16])).
% 2.01/1.10  
% 2.01/1.10  fof(f27,plain,(
% 2.01/1.10    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.01/1.10    inference(rectify,[],[f26])).
% 2.01/1.10  
% 2.01/1.10  fof(f28,plain,(
% 2.01/1.10    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0))))),
% 2.01/1.10    introduced(choice_axiom,[])).
% 2.01/1.10  
% 2.01/1.10  fof(f29,plain,(
% 2.01/1.10    ! [X0] : (((v2_funct_1(X0) | (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.01/1.10    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).
% 2.01/1.10  
% 2.01/1.10  fof(f43,plain,(
% 2.01/1.10    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK0(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.01/1.10    inference(cnf_transformation,[],[f29])).
% 2.01/1.10  
% 2.01/1.10  fof(f44,plain,(
% 2.01/1.10    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK1(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.01/1.10    inference(cnf_transformation,[],[f29])).
% 2.01/1.10  
% 2.01/1.10  fof(f45,plain,(
% 2.01/1.10    ( ! [X0] : (v2_funct_1(X0) | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.01/1.10    inference(cnf_transformation,[],[f29])).
% 2.01/1.10  
% 2.01/1.10  fof(f46,plain,(
% 2.01/1.10    ( ! [X0] : (v2_funct_1(X0) | sK0(X0) != sK1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.01/1.10    inference(cnf_transformation,[],[f29])).
% 2.01/1.10  
% 2.01/1.10  fof(f7,axiom,(
% 2.01/1.10    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.01/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.01/1.10  
% 2.01/1.10  fof(f18,plain,(
% 2.01/1.10    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/1.10    inference(ennf_transformation,[],[f7])).
% 2.01/1.10  
% 2.01/1.10  fof(f48,plain,(
% 2.01/1.10    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.01/1.10    inference(cnf_transformation,[],[f18])).
% 2.01/1.10  
% 2.01/1.10  fof(f8,axiom,(
% 2.01/1.10    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.01/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.01/1.10  
% 2.01/1.10  fof(f12,plain,(
% 2.01/1.10    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.01/1.10    inference(pure_predicate_removal,[],[f8])).
% 2.01/1.10  
% 2.01/1.10  fof(f19,plain,(
% 2.01/1.10    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/1.10    inference(ennf_transformation,[],[f12])).
% 2.01/1.10  
% 2.01/1.10  fof(f49,plain,(
% 2.01/1.10    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.01/1.10    inference(cnf_transformation,[],[f19])).
% 2.01/1.10  
% 2.01/1.10  fof(f4,axiom,(
% 2.01/1.10    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.01/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.01/1.10  
% 2.01/1.10  fof(f14,plain,(
% 2.01/1.10    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.01/1.10    inference(ennf_transformation,[],[f4])).
% 2.01/1.10  
% 2.01/1.10  fof(f25,plain,(
% 2.01/1.10    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.01/1.10    inference(nnf_transformation,[],[f14])).
% 2.01/1.10  
% 2.01/1.10  fof(f40,plain,(
% 2.01/1.10    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.01/1.10    inference(cnf_transformation,[],[f25])).
% 2.01/1.10  
% 2.01/1.10  fof(f54,plain,(
% 2.01/1.10    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2) | v2_funct_1(sK3)) )),
% 2.01/1.10    inference(cnf_transformation,[],[f35])).
% 2.01/1.10  
% 2.01/1.10  fof(f2,axiom,(
% 2.01/1.10    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.01/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.01/1.10  
% 2.01/1.10  fof(f13,plain,(
% 2.01/1.10    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.01/1.10    inference(ennf_transformation,[],[f2])).
% 2.01/1.10  
% 2.01/1.10  fof(f37,plain,(
% 2.01/1.10    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.01/1.10    inference(cnf_transformation,[],[f13])).
% 2.01/1.10  
% 2.01/1.10  fof(f3,axiom,(
% 2.01/1.10    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.01/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.01/1.10  
% 2.01/1.10  fof(f24,plain,(
% 2.01/1.10    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.01/1.10    inference(nnf_transformation,[],[f3])).
% 2.01/1.10  
% 2.01/1.10  fof(f39,plain,(
% 2.01/1.10    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.01/1.10    inference(cnf_transformation,[],[f24])).
% 2.01/1.10  
% 2.01/1.10  fof(f55,plain,(
% 2.01/1.10    r2_hidden(sK4,sK2) | ~v2_funct_1(sK3)),
% 2.01/1.10    inference(cnf_transformation,[],[f35])).
% 2.01/1.10  
% 2.01/1.10  fof(f57,plain,(
% 2.01/1.10    k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) | ~v2_funct_1(sK3)),
% 2.01/1.10    inference(cnf_transformation,[],[f35])).
% 2.01/1.10  
% 2.01/1.10  fof(f56,plain,(
% 2.01/1.10    r2_hidden(sK5,sK2) | ~v2_funct_1(sK3)),
% 2.01/1.10    inference(cnf_transformation,[],[f35])).
% 2.01/1.10  
% 2.01/1.10  fof(f58,plain,(
% 2.01/1.10    sK4 != sK5 | ~v2_funct_1(sK3)),
% 2.01/1.10    inference(cnf_transformation,[],[f35])).
% 2.01/1.10  
% 2.01/1.10  fof(f42,plain,(
% 2.01/1.10    ( ! [X4,X0,X3] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.01/1.10    inference(cnf_transformation,[],[f29])).
% 2.01/1.10  
% 2.01/1.10  fof(f6,axiom,(
% 2.01/1.10    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.01/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.01/1.10  
% 2.01/1.10  fof(f17,plain,(
% 2.01/1.10    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.01/1.10    inference(ennf_transformation,[],[f6])).
% 2.01/1.10  
% 2.01/1.10  fof(f47,plain,(
% 2.01/1.10    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.01/1.10    inference(cnf_transformation,[],[f17])).
% 2.01/1.10  
% 2.01/1.10  fof(f1,axiom,(
% 2.01/1.10    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.01/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.01/1.10  
% 2.01/1.10  fof(f36,plain,(
% 2.01/1.10    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.01/1.10    inference(cnf_transformation,[],[f1])).
% 2.01/1.10  
% 2.01/1.10  cnf(c_14,plain,
% 2.01/1.10      ( ~ v1_funct_2(X0,X1,X2)
% 2.01/1.10      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.01/1.10      | ~ r2_hidden(X3,X1)
% 2.01/1.10      | ~ v1_funct_1(X0)
% 2.01/1.10      | ~ v2_funct_1(X0)
% 2.01/1.10      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
% 2.01/1.10      | k1_xboole_0 = X2 ),
% 2.01/1.10      inference(cnf_transformation,[],[f50]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_21,negated_conjecture,
% 2.01/1.10      ( v1_funct_2(sK3,sK2,sK2) ),
% 2.01/1.10      inference(cnf_transformation,[],[f52]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_312,plain,
% 2.01/1.10      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.01/1.10      | ~ r2_hidden(X3,X1)
% 2.01/1.10      | ~ v1_funct_1(X0)
% 2.01/1.10      | ~ v2_funct_1(X0)
% 2.01/1.10      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
% 2.01/1.10      | sK2 != X2
% 2.01/1.10      | sK2 != X1
% 2.01/1.10      | sK3 != X0
% 2.01/1.10      | k1_xboole_0 = X2 ),
% 2.01/1.10      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_313,plain,
% 2.01/1.10      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 2.01/1.10      | ~ r2_hidden(X0,sK2)
% 2.01/1.10      | ~ v1_funct_1(sK3)
% 2.01/1.10      | ~ v2_funct_1(sK3)
% 2.01/1.10      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 2.01/1.10      | k1_xboole_0 = sK2 ),
% 2.01/1.10      inference(unflattening,[status(thm)],[c_312]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_22,negated_conjecture,
% 2.01/1.10      ( v1_funct_1(sK3) ),
% 2.01/1.10      inference(cnf_transformation,[],[f51]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_20,negated_conjecture,
% 2.01/1.10      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 2.01/1.10      inference(cnf_transformation,[],[f53]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_317,plain,
% 2.01/1.10      ( ~ r2_hidden(X0,sK2)
% 2.01/1.10      | ~ v2_funct_1(sK3)
% 2.01/1.10      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 2.01/1.10      | k1_xboole_0 = sK2 ),
% 2.01/1.10      inference(global_propositional_subsumption,
% 2.01/1.10                [status(thm)],
% 2.01/1.10                [c_313,c_22,c_20]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_2400,plain,
% 2.01/1.10      ( ~ v2_funct_1(sK3) | sP1_iProver_split | k1_xboole_0 = sK2 ),
% 2.01/1.10      inference(splitting,
% 2.01/1.10                [splitting(split),new_symbols(definition,[])],
% 2.01/1.10                [c_317]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_2951,plain,
% 2.01/1.10      ( k1_xboole_0 = sK2
% 2.01/1.10      | v2_funct_1(sK3) != iProver_top
% 2.01/1.10      | sP1_iProver_split = iProver_top ),
% 2.01/1.10      inference(predicate_to_equality,[status(thm)],[c_2400]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_23,plain,
% 2.01/1.10      ( v1_funct_1(sK3) = iProver_top ),
% 2.01/1.10      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_25,plain,
% 2.01/1.10      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 2.01/1.10      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_9,plain,
% 2.01/1.10      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 2.01/1.10      | ~ v1_funct_1(X0)
% 2.01/1.10      | v2_funct_1(X0)
% 2.01/1.10      | ~ v1_relat_1(X0) ),
% 2.01/1.10      inference(cnf_transformation,[],[f43]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_48,plain,
% 2.01/1.10      ( r2_hidden(sK0(X0),k1_relat_1(X0)) = iProver_top
% 2.01/1.10      | v1_funct_1(X0) != iProver_top
% 2.01/1.10      | v2_funct_1(X0) = iProver_top
% 2.01/1.10      | v1_relat_1(X0) != iProver_top ),
% 2.01/1.10      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_50,plain,
% 2.01/1.10      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 2.01/1.10      | v1_funct_1(sK3) != iProver_top
% 2.01/1.10      | v2_funct_1(sK3) = iProver_top
% 2.01/1.10      | v1_relat_1(sK3) != iProver_top ),
% 2.01/1.10      inference(instantiation,[status(thm)],[c_48]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_8,plain,
% 2.01/1.10      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 2.01/1.10      | ~ v1_funct_1(X0)
% 2.01/1.10      | v2_funct_1(X0)
% 2.01/1.10      | ~ v1_relat_1(X0) ),
% 2.01/1.10      inference(cnf_transformation,[],[f44]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_51,plain,
% 2.01/1.10      ( r2_hidden(sK1(X0),k1_relat_1(X0)) = iProver_top
% 2.01/1.10      | v1_funct_1(X0) != iProver_top
% 2.01/1.10      | v2_funct_1(X0) = iProver_top
% 2.01/1.10      | v1_relat_1(X0) != iProver_top ),
% 2.01/1.10      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_53,plain,
% 2.01/1.10      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
% 2.01/1.10      | v1_funct_1(sK3) != iProver_top
% 2.01/1.10      | v2_funct_1(sK3) = iProver_top
% 2.01/1.10      | v1_relat_1(sK3) != iProver_top ),
% 2.01/1.10      inference(instantiation,[status(thm)],[c_51]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_7,plain,
% 2.01/1.10      ( ~ v1_funct_1(X0)
% 2.01/1.10      | v2_funct_1(X0)
% 2.01/1.10      | ~ v1_relat_1(X0)
% 2.01/1.10      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
% 2.01/1.10      inference(cnf_transformation,[],[f45]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_54,plain,
% 2.01/1.10      ( k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
% 2.01/1.10      | v1_funct_1(X0) != iProver_top
% 2.01/1.10      | v2_funct_1(X0) = iProver_top
% 2.01/1.10      | v1_relat_1(X0) != iProver_top ),
% 2.01/1.10      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_56,plain,
% 2.01/1.10      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
% 2.01/1.10      | v1_funct_1(sK3) != iProver_top
% 2.01/1.10      | v2_funct_1(sK3) = iProver_top
% 2.01/1.10      | v1_relat_1(sK3) != iProver_top ),
% 2.01/1.10      inference(instantiation,[status(thm)],[c_54]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_6,plain,
% 2.01/1.10      ( ~ v1_funct_1(X0)
% 2.01/1.10      | v2_funct_1(X0)
% 2.01/1.10      | ~ v1_relat_1(X0)
% 2.01/1.10      | sK1(X0) != sK0(X0) ),
% 2.01/1.10      inference(cnf_transformation,[],[f46]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_57,plain,
% 2.01/1.10      ( sK1(X0) != sK0(X0)
% 2.01/1.10      | v1_funct_1(X0) != iProver_top
% 2.01/1.10      | v2_funct_1(X0) = iProver_top
% 2.01/1.10      | v1_relat_1(X0) != iProver_top ),
% 2.01/1.10      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_59,plain,
% 2.01/1.10      ( sK1(sK3) != sK0(sK3)
% 2.01/1.10      | v1_funct_1(sK3) != iProver_top
% 2.01/1.10      | v2_funct_1(sK3) = iProver_top
% 2.01/1.10      | v1_relat_1(sK3) != iProver_top ),
% 2.01/1.10      inference(instantiation,[status(thm)],[c_57]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_2437,plain,
% 2.01/1.10      ( k1_xboole_0 = sK2
% 2.01/1.10      | v2_funct_1(sK3) != iProver_top
% 2.01/1.10      | sP1_iProver_split = iProver_top ),
% 2.01/1.10      inference(predicate_to_equality,[status(thm)],[c_2400]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_12,plain,
% 2.01/1.10      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.01/1.10      inference(cnf_transformation,[],[f48]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_3128,plain,
% 2.01/1.10      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 2.01/1.10      | v1_relat_1(sK3) ),
% 2.01/1.10      inference(instantiation,[status(thm)],[c_12]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_3129,plain,
% 2.01/1.10      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 2.01/1.10      | v1_relat_1(sK3) = iProver_top ),
% 2.01/1.10      inference(predicate_to_equality,[status(thm)],[c_3128]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_13,plain,
% 2.01/1.10      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.01/1.10      inference(cnf_transformation,[],[f49]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_5,plain,
% 2.01/1.10      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 2.01/1.10      inference(cnf_transformation,[],[f40]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_341,plain,
% 2.01/1.10      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.01/1.10      | r1_tarski(k1_relat_1(X0),X1)
% 2.01/1.10      | ~ v1_relat_1(X0) ),
% 2.01/1.10      inference(resolution,[status(thm)],[c_13,c_5]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_345,plain,
% 2.01/1.10      ( r1_tarski(k1_relat_1(X0),X1)
% 2.01/1.10      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.01/1.10      inference(global_propositional_subsumption,[status(thm)],[c_341,c_12]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_346,plain,
% 2.01/1.10      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.01/1.10      | r1_tarski(k1_relat_1(X0),X1) ),
% 2.01/1.10      inference(renaming,[status(thm)],[c_345]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_3140,plain,
% 2.01/1.10      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 2.01/1.10      | r1_tarski(k1_relat_1(sK3),sK2) ),
% 2.01/1.10      inference(instantiation,[status(thm)],[c_346]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_3141,plain,
% 2.01/1.10      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 2.01/1.10      | r1_tarski(k1_relat_1(sK3),sK2) = iProver_top ),
% 2.01/1.10      inference(predicate_to_equality,[status(thm)],[c_3140]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_19,negated_conjecture,
% 2.01/1.10      ( ~ r2_hidden(X0,sK2)
% 2.01/1.10      | ~ r2_hidden(X1,sK2)
% 2.01/1.10      | v2_funct_1(sK3)
% 2.01/1.10      | X1 = X0
% 2.01/1.10      | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
% 2.01/1.10      inference(cnf_transformation,[],[f54]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_3208,plain,
% 2.01/1.10      ( ~ r2_hidden(sK1(sK3),sK2)
% 2.01/1.10      | ~ r2_hidden(sK0(sK3),sK2)
% 2.01/1.10      | v2_funct_1(sK3)
% 2.01/1.10      | k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
% 2.01/1.10      | sK1(sK3) = sK0(sK3) ),
% 2.01/1.10      inference(instantiation,[status(thm)],[c_19]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_3209,plain,
% 2.01/1.10      ( k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
% 2.01/1.10      | sK1(sK3) = sK0(sK3)
% 2.01/1.10      | r2_hidden(sK1(sK3),sK2) != iProver_top
% 2.01/1.10      | r2_hidden(sK0(sK3),sK2) != iProver_top
% 2.01/1.10      | v2_funct_1(sK3) = iProver_top ),
% 2.01/1.10      inference(predicate_to_equality,[status(thm)],[c_3208]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_1,plain,
% 2.01/1.10      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.01/1.10      | ~ r2_hidden(X2,X0)
% 2.01/1.10      | r2_hidden(X2,X1) ),
% 2.01/1.10      inference(cnf_transformation,[],[f37]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_2,plain,
% 2.01/1.10      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.01/1.10      inference(cnf_transformation,[],[f39]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_179,plain,
% 2.01/1.10      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.01/1.10      inference(prop_impl,[status(thm)],[c_2]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_180,plain,
% 2.01/1.10      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.01/1.10      inference(renaming,[status(thm)],[c_179]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_228,plain,
% 2.01/1.10      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.01/1.10      inference(bin_hyper_res,[status(thm)],[c_1,c_180]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_3169,plain,
% 2.01/1.10      ( r2_hidden(sK0(sK3),X0)
% 2.01/1.10      | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 2.01/1.10      | ~ r1_tarski(k1_relat_1(sK3),X0) ),
% 2.01/1.10      inference(instantiation,[status(thm)],[c_228]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_3294,plain,
% 2.01/1.10      ( ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 2.01/1.10      | r2_hidden(sK0(sK3),sK2)
% 2.01/1.10      | ~ r1_tarski(k1_relat_1(sK3),sK2) ),
% 2.01/1.10      inference(instantiation,[status(thm)],[c_3169]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_3295,plain,
% 2.01/1.10      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) != iProver_top
% 2.01/1.10      | r2_hidden(sK0(sK3),sK2) = iProver_top
% 2.01/1.10      | r1_tarski(k1_relat_1(sK3),sK2) != iProver_top ),
% 2.01/1.10      inference(predicate_to_equality,[status(thm)],[c_3294]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_3182,plain,
% 2.01/1.10      ( r2_hidden(sK1(sK3),X0)
% 2.01/1.10      | ~ r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 2.01/1.10      | ~ r1_tarski(k1_relat_1(sK3),X0) ),
% 2.01/1.10      inference(instantiation,[status(thm)],[c_228]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_3303,plain,
% 2.01/1.10      ( ~ r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 2.01/1.10      | r2_hidden(sK1(sK3),sK2)
% 2.01/1.10      | ~ r1_tarski(k1_relat_1(sK3),sK2) ),
% 2.01/1.10      inference(instantiation,[status(thm)],[c_3182]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_3304,plain,
% 2.01/1.10      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) != iProver_top
% 2.01/1.10      | r2_hidden(sK1(sK3),sK2) = iProver_top
% 2.01/1.10      | r1_tarski(k1_relat_1(sK3),sK2) != iProver_top ),
% 2.01/1.10      inference(predicate_to_equality,[status(thm)],[c_3303]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_3630,plain,
% 2.01/1.10      ( k1_xboole_0 = sK2 | sP1_iProver_split = iProver_top ),
% 2.01/1.10      inference(global_propositional_subsumption,
% 2.01/1.10                [status(thm)],
% 2.01/1.10                [c_2951,c_23,c_25,c_50,c_53,c_56,c_59,c_2437,c_3129,c_3141,
% 2.01/1.10                 c_3209,c_3295,c_3304]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_18,negated_conjecture,
% 2.01/1.10      ( r2_hidden(sK4,sK2) | ~ v2_funct_1(sK3) ),
% 2.01/1.10      inference(cnf_transformation,[],[f55]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_2956,plain,
% 2.01/1.10      ( r2_hidden(sK4,sK2) = iProver_top | v2_funct_1(sK3) != iProver_top ),
% 2.01/1.10      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_2399,plain,
% 2.01/1.10      ( ~ r2_hidden(X0,sK2)
% 2.01/1.10      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 2.01/1.10      | ~ sP1_iProver_split ),
% 2.01/1.10      inference(splitting,
% 2.01/1.10                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.01/1.10                [c_317]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_2952,plain,
% 2.01/1.10      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 2.01/1.10      | r2_hidden(X0,sK2) != iProver_top
% 2.01/1.10      | sP1_iProver_split != iProver_top ),
% 2.01/1.10      inference(predicate_to_equality,[status(thm)],[c_2399]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_3573,plain,
% 2.01/1.10      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 2.01/1.10      | v2_funct_1(sK3) != iProver_top
% 2.01/1.10      | sP1_iProver_split != iProver_top ),
% 2.01/1.10      inference(superposition,[status(thm)],[c_2956,c_2952]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_3623,plain,
% 2.01/1.10      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 2.01/1.10      | sP1_iProver_split != iProver_top ),
% 2.01/1.10      inference(global_propositional_subsumption,
% 2.01/1.10                [status(thm)],
% 2.01/1.10                [c_3573,c_23,c_25,c_50,c_53,c_56,c_59,c_3129,c_3141,c_3209,
% 2.01/1.10                 c_3295,c_3304]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_3636,plain,
% 2.01/1.10      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 2.01/1.10      | sK2 = k1_xboole_0 ),
% 2.01/1.10      inference(superposition,[status(thm)],[c_3630,c_3623]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_566,plain,
% 2.01/1.10      ( v2_funct_1(X0)
% 2.01/1.10      | ~ v1_relat_1(X0)
% 2.01/1.10      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
% 2.01/1.10      | sK3 != X0 ),
% 2.01/1.10      inference(resolution_lifted,[status(thm)],[c_7,c_22]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_567,plain,
% 2.01/1.10      ( v2_funct_1(sK3)
% 2.01/1.10      | ~ v1_relat_1(sK3)
% 2.01/1.10      | k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
% 2.01/1.10      inference(unflattening,[status(thm)],[c_566]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_2947,plain,
% 2.01/1.10      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
% 2.01/1.10      | v2_funct_1(sK3) = iProver_top
% 2.01/1.10      | v1_relat_1(sK3) != iProver_top ),
% 2.01/1.10      inference(predicate_to_equality,[status(thm)],[c_567]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_3689,plain,
% 2.01/1.10      ( v2_funct_1(sK3) = iProver_top ),
% 2.01/1.10      inference(global_propositional_subsumption,
% 2.01/1.10                [status(thm)],
% 2.01/1.10                [c_2947,c_23,c_25,c_50,c_53,c_56,c_59,c_3129,c_3141,c_3209,
% 2.01/1.10                 c_3295,c_3304]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_16,negated_conjecture,
% 2.01/1.10      ( ~ v2_funct_1(sK3) | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
% 2.01/1.10      inference(cnf_transformation,[],[f57]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_2958,plain,
% 2.01/1.10      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
% 2.01/1.10      | v2_funct_1(sK3) != iProver_top ),
% 2.01/1.10      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_3695,plain,
% 2.01/1.10      ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
% 2.01/1.10      inference(superposition,[status(thm)],[c_3689,c_2958]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_17,negated_conjecture,
% 2.01/1.10      ( r2_hidden(sK5,sK2) | ~ v2_funct_1(sK3) ),
% 2.01/1.10      inference(cnf_transformation,[],[f56]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_2957,plain,
% 2.01/1.10      ( r2_hidden(sK5,sK2) = iProver_top | v2_funct_1(sK3) != iProver_top ),
% 2.01/1.10      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_3572,plain,
% 2.01/1.10      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
% 2.01/1.10      | v2_funct_1(sK3) != iProver_top
% 2.01/1.10      | sP1_iProver_split != iProver_top ),
% 2.01/1.10      inference(superposition,[status(thm)],[c_2957,c_2952]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_3589,plain,
% 2.01/1.10      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
% 2.01/1.10      | sP1_iProver_split != iProver_top ),
% 2.01/1.10      inference(global_propositional_subsumption,
% 2.01/1.10                [status(thm)],
% 2.01/1.10                [c_3572,c_23,c_25,c_50,c_53,c_56,c_59,c_3129,c_3141,c_3209,
% 2.01/1.10                 c_3295,c_3304]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_3733,plain,
% 2.01/1.10      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
% 2.01/1.10      | sP1_iProver_split != iProver_top ),
% 2.01/1.10      inference(demodulation,[status(thm)],[c_3695,c_3589]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_3810,plain,
% 2.01/1.10      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
% 2.01/1.10      | sK2 = k1_xboole_0 ),
% 2.01/1.10      inference(superposition,[status(thm)],[c_3630,c_3733]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_4124,plain,
% 2.01/1.10      ( sK2 = k1_xboole_0 | sK5 = sK4 ),
% 2.01/1.10      inference(superposition,[status(thm)],[c_3636,c_3810]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_579,plain,
% 2.01/1.10      ( v2_funct_1(X0) | ~ v1_relat_1(X0) | sK1(X0) != sK0(X0) | sK3 != X0 ),
% 2.01/1.10      inference(resolution_lifted,[status(thm)],[c_6,c_22]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_580,plain,
% 2.01/1.10      ( v2_funct_1(sK3) | ~ v1_relat_1(sK3) | sK1(sK3) != sK0(sK3) ),
% 2.01/1.10      inference(unflattening,[status(thm)],[c_579]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_15,negated_conjecture,
% 2.01/1.10      ( ~ v2_funct_1(sK3) | sK4 != sK5 ),
% 2.01/1.10      inference(cnf_transformation,[],[f58]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_818,plain,
% 2.01/1.10      ( ~ v1_relat_1(sK3) | sK1(sK3) != sK0(sK3) | sK5 != sK4 ),
% 2.01/1.10      inference(resolution,[status(thm)],[c_580,c_15]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_909,plain,
% 2.01/1.10      ( ~ v1_relat_1(sK3)
% 2.01/1.10      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 2.01/1.10      | sK5 != sK4 ),
% 2.01/1.10      inference(resolution,[status(thm)],[c_567,c_15]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_553,plain,
% 2.01/1.10      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 2.01/1.10      | v2_funct_1(X0)
% 2.01/1.10      | ~ v1_relat_1(X0)
% 2.01/1.10      | sK3 != X0 ),
% 2.01/1.10      inference(resolution_lifted,[status(thm)],[c_8,c_22]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_554,plain,
% 2.01/1.10      ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 2.01/1.10      | v2_funct_1(sK3)
% 2.01/1.10      | ~ v1_relat_1(sK3) ),
% 2.01/1.10      inference(unflattening,[status(thm)],[c_553]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_1000,plain,
% 2.01/1.10      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) | ~ v1_relat_1(sK3) | sK5 != sK4 ),
% 2.01/1.10      inference(resolution,[status(thm)],[c_554,c_15]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_540,plain,
% 2.01/1.10      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 2.01/1.10      | v2_funct_1(X0)
% 2.01/1.10      | ~ v1_relat_1(X0)
% 2.01/1.10      | sK3 != X0 ),
% 2.01/1.10      inference(resolution_lifted,[status(thm)],[c_9,c_22]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_541,plain,
% 2.01/1.10      ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 2.01/1.10      | v2_funct_1(sK3)
% 2.01/1.10      | ~ v1_relat_1(sK3) ),
% 2.01/1.10      inference(unflattening,[status(thm)],[c_540]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_1091,plain,
% 2.01/1.10      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) | ~ v1_relat_1(sK3) | sK5 != sK4 ),
% 2.01/1.10      inference(resolution,[status(thm)],[c_541,c_15]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_2412,plain,( X0 != X1 | sK1(X0) = sK1(X1) ),theory(equality) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_2424,plain,
% 2.01/1.10      ( sK1(sK3) = sK1(sK3) | sK3 != sK3 ),
% 2.01/1.10      inference(instantiation,[status(thm)],[c_2412]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_2402,plain,( X0 = X0 ),theory(equality) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_2429,plain,
% 2.01/1.10      ( sK3 = sK3 ),
% 2.01/1.10      inference(instantiation,[status(thm)],[c_2402]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_10,plain,
% 2.01/1.10      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.01/1.10      | ~ r2_hidden(X2,k1_relat_1(X1))
% 2.01/1.10      | ~ v1_funct_1(X1)
% 2.01/1.10      | ~ v2_funct_1(X1)
% 2.01/1.10      | ~ v1_relat_1(X1)
% 2.01/1.10      | X0 = X2
% 2.01/1.10      | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
% 2.01/1.10      inference(cnf_transformation,[],[f42]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_592,plain,
% 2.01/1.10      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.01/1.10      | ~ r2_hidden(X2,k1_relat_1(X1))
% 2.01/1.10      | ~ v2_funct_1(X1)
% 2.01/1.10      | ~ v1_relat_1(X1)
% 2.01/1.10      | X2 = X0
% 2.01/1.10      | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
% 2.01/1.10      | sK3 != X1 ),
% 2.01/1.10      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_593,plain,
% 2.01/1.10      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.01/1.10      | ~ r2_hidden(X1,k1_relat_1(sK3))
% 2.01/1.10      | ~ v2_funct_1(sK3)
% 2.01/1.10      | ~ v1_relat_1(sK3)
% 2.01/1.10      | X0 = X1
% 2.01/1.10      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
% 2.01/1.10      inference(unflattening,[status(thm)],[c_592]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_2398,plain,
% 2.01/1.10      ( ~ v2_funct_1(sK3) | ~ v1_relat_1(sK3) | sP0_iProver_split ),
% 2.01/1.10      inference(splitting,
% 2.01/1.10                [splitting(split),new_symbols(definition,[])],
% 2.01/1.10                [c_593]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_2403,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_3211,plain,
% 2.01/1.10      ( sK1(sK3) != X0 | sK1(sK3) = sK0(sK3) | sK0(sK3) != X0 ),
% 2.01/1.10      inference(instantiation,[status(thm)],[c_2403]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_3400,plain,
% 2.01/1.10      ( sK1(sK3) != sK1(sK3) | sK1(sK3) = sK0(sK3) | sK0(sK3) != sK1(sK3) ),
% 2.01/1.10      inference(instantiation,[status(thm)],[c_3211]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_3691,plain,
% 2.01/1.10      ( v2_funct_1(sK3) ),
% 2.01/1.10      inference(predicate_to_equality_rev,[status(thm)],[c_3689]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_2397,plain,
% 2.01/1.10      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.01/1.10      | ~ r2_hidden(X1,k1_relat_1(sK3))
% 2.01/1.10      | X0 = X1
% 2.01/1.10      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
% 2.01/1.10      | ~ sP0_iProver_split ),
% 2.01/1.10      inference(splitting,
% 2.01/1.10                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.01/1.10                [c_593]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_3721,plain,
% 2.01/1.10      ( ~ r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 2.01/1.10      | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 2.01/1.10      | ~ sP0_iProver_split
% 2.01/1.10      | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(sK3))
% 2.01/1.10      | sK0(sK3) = sK1(sK3) ),
% 2.01/1.10      inference(instantiation,[status(thm)],[c_2397]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_4140,plain,
% 2.01/1.10      ( sK2 = k1_xboole_0 ),
% 2.01/1.10      inference(global_propositional_subsumption,
% 2.01/1.10                [status(thm)],
% 2.01/1.10                [c_4124,c_20,c_818,c_909,c_1000,c_1091,c_2424,c_2429,c_2398,
% 2.01/1.10                 c_3128,c_3400,c_3691,c_3721]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_11,plain,
% 2.01/1.10      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.01/1.10      inference(cnf_transformation,[],[f47]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_2961,plain,
% 2.01/1.10      ( r2_hidden(X0,X1) != iProver_top | r1_tarski(X1,X0) != iProver_top ),
% 2.01/1.10      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_3320,plain,
% 2.01/1.10      ( r1_tarski(sK2,sK4) != iProver_top | v2_funct_1(sK3) != iProver_top ),
% 2.01/1.10      inference(superposition,[status(thm)],[c_2956,c_2961]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_3491,plain,
% 2.01/1.10      ( r1_tarski(sK2,sK4) != iProver_top ),
% 2.01/1.10      inference(global_propositional_subsumption,
% 2.01/1.10                [status(thm)],
% 2.01/1.10                [c_3320,c_23,c_25,c_50,c_53,c_56,c_59,c_3129,c_3141,c_3209,
% 2.01/1.10                 c_3295,c_3304]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_4146,plain,
% 2.01/1.10      ( r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 2.01/1.10      inference(demodulation,[status(thm)],[c_4140,c_3491]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_0,plain,
% 2.01/1.10      ( r1_tarski(k1_xboole_0,X0) ),
% 2.01/1.10      inference(cnf_transformation,[],[f36]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_2964,plain,
% 2.01/1.10      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.01/1.10      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.01/1.10  
% 2.01/1.10  cnf(c_4399,plain,
% 2.01/1.10      ( $false ),
% 2.01/1.10      inference(forward_subsumption_resolution,[status(thm)],[c_4146,c_2964]) ).
% 2.01/1.10  
% 2.01/1.10  
% 2.01/1.10  % SZS output end CNFRefutation for theBenchmark.p
% 2.01/1.10  
% 2.01/1.10  ------                               Statistics
% 2.01/1.10  
% 2.01/1.10  ------ General
% 2.01/1.10  
% 2.01/1.10  abstr_ref_over_cycles:                  0
% 2.01/1.10  abstr_ref_under_cycles:                 0
% 2.01/1.10  gc_basic_clause_elim:                   0
% 2.01/1.10  forced_gc_time:                         0
% 2.01/1.10  parsing_time:                           0.008
% 2.01/1.10  unif_index_cands_time:                  0.
% 2.01/1.10  unif_index_add_time:                    0.
% 2.01/1.10  orderings_time:                         0.
% 2.01/1.10  out_proof_time:                         0.019
% 2.01/1.10  total_time:                             0.188
% 2.01/1.10  num_of_symbols:                         53
% 2.01/1.10  num_of_terms:                           1535
% 2.01/1.10  
% 2.01/1.10  ------ Preprocessing
% 2.01/1.10  
% 2.01/1.10  num_of_splits:                          2
% 2.01/1.10  num_of_split_atoms:                     2
% 2.01/1.10  num_of_reused_defs:                     0
% 2.01/1.10  num_eq_ax_congr_red:                    10
% 2.01/1.10  num_of_sem_filtered_clauses:            1
% 2.01/1.10  num_of_subtypes:                        0
% 2.01/1.10  monotx_restored_types:                  0
% 2.01/1.10  sat_num_of_epr_types:                   0
% 2.01/1.10  sat_num_of_non_cyclic_types:            0
% 2.01/1.10  sat_guarded_non_collapsed_types:        0
% 2.01/1.10  num_pure_diseq_elim:                    0
% 2.01/1.10  simp_replaced_by:                       0
% 2.01/1.10  res_preprocessed:                       113
% 2.01/1.10  prep_upred:                             0
% 2.01/1.10  prep_unflattend:                        60
% 2.01/1.10  smt_new_axioms:                         0
% 2.01/1.10  pred_elim_cands:                        5
% 2.01/1.10  pred_elim:                              3
% 2.01/1.10  pred_elim_cl:                           4
% 2.01/1.10  pred_elim_cycles:                       11
% 2.01/1.10  merged_defs:                            8
% 2.01/1.10  merged_defs_ncl:                        0
% 2.01/1.10  bin_hyper_res:                          9
% 2.01/1.10  prep_cycles:                            4
% 2.01/1.10  pred_elim_time:                         0.036
% 2.01/1.10  splitting_time:                         0.
% 2.01/1.10  sem_filter_time:                        0.
% 2.01/1.10  monotx_time:                            0.
% 2.01/1.10  subtype_inf_time:                       0.
% 2.01/1.10  
% 2.01/1.10  ------ Problem properties
% 2.01/1.10  
% 2.01/1.10  clauses:                                21
% 2.01/1.10  conjectures:                            6
% 2.01/1.10  epr:                                    8
% 2.01/1.10  horn:                                   16
% 2.01/1.10  ground:                                 11
% 2.01/1.10  unary:                                  2
% 2.01/1.10  binary:                                 9
% 2.01/1.10  lits:                                   54
% 2.01/1.10  lits_eq:                                10
% 2.01/1.10  fd_pure:                                0
% 2.01/1.10  fd_pseudo:                              0
% 2.01/1.10  fd_cond:                                0
% 2.01/1.10  fd_pseudo_cond:                         2
% 2.01/1.10  ac_symbols:                             0
% 2.01/1.10  
% 2.01/1.10  ------ Propositional Solver
% 2.01/1.10  
% 2.01/1.10  prop_solver_calls:                      28
% 2.01/1.10  prop_fast_solver_calls:                 1095
% 2.01/1.10  smt_solver_calls:                       0
% 2.01/1.10  smt_fast_solver_calls:                  0
% 2.01/1.10  prop_num_of_clauses:                    854
% 2.01/1.10  prop_preprocess_simplified:             4031
% 2.01/1.10  prop_fo_subsumed:                       21
% 2.01/1.10  prop_solver_time:                       0.
% 2.01/1.10  smt_solver_time:                        0.
% 2.01/1.10  smt_fast_solver_time:                   0.
% 2.01/1.10  prop_fast_solver_time:                  0.
% 2.01/1.10  prop_unsat_core_time:                   0.
% 2.01/1.10  
% 2.01/1.10  ------ QBF
% 2.01/1.10  
% 2.01/1.10  qbf_q_res:                              0
% 2.01/1.10  qbf_num_tautologies:                    0
% 2.01/1.10  qbf_prep_cycles:                        0
% 2.01/1.10  
% 2.01/1.10  ------ BMC1
% 2.01/1.10  
% 2.01/1.10  bmc1_current_bound:                     -1
% 2.01/1.10  bmc1_last_solved_bound:                 -1
% 2.01/1.10  bmc1_unsat_core_size:                   -1
% 2.01/1.10  bmc1_unsat_core_parents_size:           -1
% 2.01/1.10  bmc1_merge_next_fun:                    0
% 2.01/1.10  bmc1_unsat_core_clauses_time:           0.
% 2.01/1.10  
% 2.01/1.10  ------ Instantiation
% 2.01/1.10  
% 2.01/1.10  inst_num_of_clauses:                    241
% 2.01/1.10  inst_num_in_passive:                    16
% 2.01/1.10  inst_num_in_active:                     183
% 2.01/1.10  inst_num_in_unprocessed:                42
% 2.01/1.10  inst_num_of_loops:                      210
% 2.01/1.10  inst_num_of_learning_restarts:          0
% 2.01/1.10  inst_num_moves_active_passive:          23
% 2.01/1.10  inst_lit_activity:                      0
% 2.01/1.10  inst_lit_activity_moves:                0
% 2.01/1.10  inst_num_tautologies:                   0
% 2.01/1.10  inst_num_prop_implied:                  0
% 2.01/1.10  inst_num_existing_simplified:           0
% 2.01/1.10  inst_num_eq_res_simplified:             0
% 2.01/1.10  inst_num_child_elim:                    0
% 2.01/1.10  inst_num_of_dismatching_blockings:      34
% 2.01/1.10  inst_num_of_non_proper_insts:           268
% 2.01/1.10  inst_num_of_duplicates:                 0
% 2.01/1.10  inst_inst_num_from_inst_to_res:         0
% 2.01/1.10  inst_dismatching_checking_time:         0.
% 2.01/1.10  
% 2.01/1.10  ------ Resolution
% 2.01/1.10  
% 2.01/1.10  res_num_of_clauses:                     0
% 2.01/1.10  res_num_in_passive:                     0
% 2.01/1.10  res_num_in_active:                      0
% 2.01/1.10  res_num_of_loops:                       117
% 2.01/1.10  res_forward_subset_subsumed:            20
% 2.01/1.10  res_backward_subset_subsumed:           0
% 2.01/1.10  res_forward_subsumed:                   0
% 2.01/1.10  res_backward_subsumed:                  0
% 2.01/1.10  res_forward_subsumption_resolution:     0
% 2.01/1.10  res_backward_subsumption_resolution:    0
% 2.01/1.10  res_clause_to_clause_subsumption:       79
% 2.01/1.10  res_orphan_elimination:                 0
% 2.01/1.10  res_tautology_del:                      58
% 2.01/1.10  res_num_eq_res_simplified:              0
% 2.01/1.10  res_num_sel_changes:                    0
% 2.01/1.10  res_moves_from_active_to_pass:          0
% 2.01/1.10  
% 2.01/1.10  ------ Superposition
% 2.01/1.10  
% 2.01/1.10  sup_time_total:                         0.
% 2.01/1.10  sup_time_generating:                    0.
% 2.01/1.10  sup_time_sim_full:                      0.
% 2.01/1.10  sup_time_sim_immed:                     0.
% 2.01/1.10  
% 2.01/1.10  sup_num_of_clauses:                     38
% 2.01/1.10  sup_num_in_active:                      28
% 2.01/1.10  sup_num_in_passive:                     10
% 2.01/1.10  sup_num_of_loops:                       40
% 2.01/1.10  sup_fw_superposition:                   16
% 2.01/1.10  sup_bw_superposition:                   15
% 2.01/1.10  sup_immediate_simplified:               2
% 2.01/1.10  sup_given_eliminated:                   0
% 2.01/1.10  comparisons_done:                       0
% 2.01/1.10  comparisons_avoided:                    6
% 2.01/1.10  
% 2.01/1.10  ------ Simplifications
% 2.01/1.10  
% 2.01/1.10  
% 2.01/1.10  sim_fw_subset_subsumed:                 2
% 2.01/1.10  sim_bw_subset_subsumed:                 0
% 2.01/1.10  sim_fw_subsumed:                        0
% 2.01/1.10  sim_bw_subsumed:                        0
% 2.01/1.10  sim_fw_subsumption_res:                 1
% 2.01/1.10  sim_bw_subsumption_res:                 0
% 2.01/1.10  sim_tautology_del:                      1
% 2.01/1.10  sim_eq_tautology_del:                   5
% 2.01/1.10  sim_eq_res_simp:                        0
% 2.01/1.10  sim_fw_demodulated:                     0
% 2.01/1.10  sim_bw_demodulated:                     12
% 2.01/1.10  sim_light_normalised:                   1
% 2.01/1.10  sim_joinable_taut:                      0
% 2.01/1.10  sim_joinable_simp:                      0
% 2.01/1.10  sim_ac_normalised:                      0
% 2.01/1.10  sim_smt_subsumption:                    0
% 2.01/1.10  
%------------------------------------------------------------------------------
