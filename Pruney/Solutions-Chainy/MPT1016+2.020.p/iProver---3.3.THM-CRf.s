%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:55 EST 2020

% Result     : Theorem 1.52s
% Output     : CNFRefutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  178 (1585 expanded)
%              Number of clauses        :  119 ( 518 expanded)
%              Number of leaves         :   20 ( 318 expanded)
%              Depth                    :   24
%              Number of atoms          :  642 (11468 expanded)
%              Number of equality atoms :  276 (3742 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
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

fof(f18,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f31,f32])).

fof(f52,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

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
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

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
    inference(nnf_transformation,[],[f24])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f38,plain,(
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

fof(f37,plain,
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

fof(f39,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f36,f38,f37])).

fof(f56,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK4,X4) != k1_funct_1(sK4,X5)
      | ~ r2_hidden(X5,sK3)
      | ~ r2_hidden(X4,sK3)
      | v2_funct_1(sK4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f50,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK1(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK2(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | sK1(X0) != sK2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
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

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,
    ( r2_hidden(sK5,sK3)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,(
    v1_funct_2(sK4,sK3,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f61,plain,
    ( r2_hidden(sK6,sK3)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f63,plain,
    ( sK5 != sK6
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_460,plain,
    ( v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_23])).

cnf(c_461,plain,
    ( v2_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK2(sK4)) ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_1920,plain,
    ( v2_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK2(sK4)) ),
    inference(subtyping,[status(esa)],[c_461])).

cnf(c_2350,plain,
    ( k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK2(sK4))
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1920])).

cnf(c_8,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1933,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1983,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1933])).

cnf(c_1985,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1983])).

cnf(c_2006,plain,
    ( k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK2(sK4))
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1920])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_306,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_21])).

cnf(c_307,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_1925,plain,
    ( ~ v1_relat_1(X0_50)
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_307])).

cnf(c_2510,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0_52,X1_52))
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)) ),
    inference(instantiation,[status(thm)],[c_1925])).

cnf(c_2511,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))
    | v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2510])).

cnf(c_2513,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | v1_relat_1(k2_zfmisc_1(sK3,sK3)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2511])).

cnf(c_1945,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_2539,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) = k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_1945])).

cnf(c_3055,plain,
    ( v2_funct_1(sK4) = iProver_top
    | k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK2(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2350,c_1985,c_2006,c_2513,c_2539])).

cnf(c_3056,plain,
    ( k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK2(sK4))
    | v2_funct_1(sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_3055])).

cnf(c_17,negated_conjecture,
    ( ~ v2_funct_1(sK4)
    | k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1931,negated_conjecture,
    ( ~ v2_funct_1(sK4)
    | k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2337,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1931])).

cnf(c_3065,plain,
    ( k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK2(sK4))
    | k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_3056,c_2337])).

cnf(c_20,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X1,sK3)
    | v2_funct_1(sK4)
    | X1 = X0
    | k1_funct_1(sK4,X1) != k1_funct_1(sK4,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1928,negated_conjecture,
    ( ~ r2_hidden(X0_51,sK3)
    | ~ r2_hidden(X1_51,sK3)
    | v2_funct_1(sK4)
    | X1_51 = X0_51
    | k1_funct_1(sK4,X1_51) != k1_funct_1(sK4,X0_51) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_2340,plain,
    ( X0_51 = X1_51
    | k1_funct_1(sK4,X0_51) != k1_funct_1(sK4,X1_51)
    | r2_hidden(X0_51,sK3) != iProver_top
    | r2_hidden(X1_51,sK3) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1928])).

cnf(c_3095,plain,
    ( k1_funct_1(sK4,sK1(sK4)) != k1_funct_1(sK4,X0_51)
    | k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
    | sK2(sK4) = X0_51
    | r2_hidden(X0_51,sK3) != iProver_top
    | r2_hidden(sK2(sK4),sK3) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3065,c_2340])).

cnf(c_24,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_12,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_43,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_45,plain,
    ( r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_11,plain,
    ( r2_hidden(sK2(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_46,plain,
    ( r2_hidden(sK2(X0),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_48,plain,
    ( r2_hidden(sK2(sK4),k1_relat_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_1957,plain,
    ( sK2(X0_50) = sK2(X1_50)
    | X0_50 != X1_50 ),
    theory(equality)).

cnf(c_1968,plain,
    ( sK2(sK4) = sK2(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1957])).

cnf(c_1942,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_1972,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1942])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_14,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_319,plain,
    ( v4_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_320,plain,
    ( v4_relat_1(sK4,X0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) ),
    inference(unflattening,[status(thm)],[c_319])).

cnf(c_339,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | X2 != X1
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_320])).

cnf(c_340,plain,
    ( r1_tarski(k1_relat_1(sK4),X0)
    | ~ v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_1924,plain,
    ( r1_tarski(k1_relat_1(sK4),X0_52)
    | ~ v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) ),
    inference(subtyping,[status(esa)],[c_340])).

cnf(c_1999,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | r1_tarski(k1_relat_1(sK4),X0_52) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1924])).

cnf(c_2001,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | r1_tarski(k1_relat_1(sK4),sK3) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1999])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK2(X0) != sK1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_473,plain,
    ( v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK2(X0) != sK1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_23])).

cnf(c_474,plain,
    ( v2_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | sK2(sK4) != sK1(sK4) ),
    inference(unflattening,[status(thm)],[c_473])).

cnf(c_1919,plain,
    ( v2_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | sK2(sK4) != sK1(sK4) ),
    inference(subtyping,[status(esa)],[c_474])).

cnf(c_2007,plain,
    ( sK2(sK4) != sK1(sK4)
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1919])).

cnf(c_1946,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_2736,plain,
    ( sK2(sK4) != X0_51
    | sK2(sK4) = sK1(sK4)
    | sK1(sK4) != X0_51 ),
    inference(instantiation,[status(thm)],[c_1946])).

cnf(c_2804,plain,
    ( sK2(sK4) != sK2(sK4)
    | sK2(sK4) = sK1(sK4)
    | sK1(sK4) != sK2(sK4) ),
    inference(instantiation,[status(thm)],[c_2736])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1934,plain,
    ( ~ r1_tarski(X0_52,X1_52)
    | ~ r2_hidden(X0_51,X0_52)
    | r2_hidden(X0_51,X1_52) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2881,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),X0_52)
    | r2_hidden(sK1(sK4),X0_52)
    | ~ r2_hidden(sK1(sK4),k1_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_1934])).

cnf(c_2882,plain,
    ( r1_tarski(k1_relat_1(sK4),X0_52) != iProver_top
    | r2_hidden(sK1(sK4),X0_52) = iProver_top
    | r2_hidden(sK1(sK4),k1_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2881])).

cnf(c_2884,plain,
    ( r1_tarski(k1_relat_1(sK4),sK3) != iProver_top
    | r2_hidden(sK1(sK4),k1_relat_1(sK4)) != iProver_top
    | r2_hidden(sK1(sK4),sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2882])).

cnf(c_2886,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),X0_52)
    | r2_hidden(sK2(sK4),X0_52)
    | ~ r2_hidden(sK2(sK4),k1_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_1934])).

cnf(c_2887,plain,
    ( r1_tarski(k1_relat_1(sK4),X0_52) != iProver_top
    | r2_hidden(sK2(sK4),X0_52) = iProver_top
    | r2_hidden(sK2(sK4),k1_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2886])).

cnf(c_2889,plain,
    ( r1_tarski(k1_relat_1(sK4),sK3) != iProver_top
    | r2_hidden(sK2(sK4),k1_relat_1(sK4)) != iProver_top
    | r2_hidden(sK2(sK4),sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2887])).

cnf(c_3157,plain,
    ( ~ r2_hidden(sK2(sK4),sK3)
    | ~ r2_hidden(sK1(sK4),sK3)
    | v2_funct_1(sK4)
    | k1_funct_1(sK4,sK1(sK4)) != k1_funct_1(sK4,sK2(sK4))
    | sK1(sK4) = sK2(sK4) ),
    inference(instantiation,[status(thm)],[c_1928])).

cnf(c_3158,plain,
    ( k1_funct_1(sK4,sK1(sK4)) != k1_funct_1(sK4,sK2(sK4))
    | sK1(sK4) = sK2(sK4)
    | r2_hidden(sK2(sK4),sK3) != iProver_top
    | r2_hidden(sK1(sK4),sK3) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3157])).

cnf(c_3323,plain,
    ( v2_funct_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3095,c_24,c_45,c_48,c_1968,c_1972,c_1985,c_2001,c_2006,c_2007,c_2513,c_2539,c_2804,c_2884,c_2889,c_3158])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK5,sK3)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1929,negated_conjecture,
    ( r2_hidden(sK5,sK3)
    | ~ v2_funct_1(sK4) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2339,plain,
    ( r2_hidden(sK5,sK3) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1929])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK4,sK3,sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_277,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
    | sK3 != X2
    | sK3 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_278,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    | ~ r2_hidden(X0,sK3)
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_277])).

cnf(c_282,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ v2_funct_1(sK4)
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_278,c_23,c_21])).

cnf(c_1926,plain,
    ( ~ r2_hidden(X0_51,sK3)
    | ~ v2_funct_1(sK4)
    | k1_xboole_0 = sK3
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_51)) = X0_51 ),
    inference(subtyping,[status(esa)],[c_282])).

cnf(c_1937,plain,
    ( ~ r2_hidden(X0_51,sK3)
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_51)) = X0_51
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1926])).

cnf(c_2343,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_51)) = X0_51
    | r2_hidden(X0_51,sK3) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1937])).

cnf(c_2647,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK5
    | v2_funct_1(sK4) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2339,c_2343])).

cnf(c_30,plain,
    ( r2_hidden(sK5,sK3) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1943,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_1973,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1943])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_4,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_266,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_267,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_266])).

cnf(c_1927,plain,
    ( ~ r2_hidden(X0_51,k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_267])).

cnf(c_1991,plain,
    ( r2_hidden(X0_51,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1927])).

cnf(c_1993,plain,
    ( r2_hidden(sK5,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1991])).

cnf(c_1938,plain,
    ( ~ v2_funct_1(sK4)
    | sP0_iProver_split
    | k1_xboole_0 = sK3 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1926])).

cnf(c_1994,plain,
    ( k1_xboole_0 = sK3
    | v2_funct_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1938])).

cnf(c_1995,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_51)) = X0_51
    | r2_hidden(X0_51,sK3) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1937])).

cnf(c_1997,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK5
    | r2_hidden(sK5,sK3) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_1995])).

cnf(c_1949,plain,
    ( ~ r2_hidden(X0_51,X0_52)
    | r2_hidden(X1_51,X1_52)
    | X1_52 != X0_52
    | X1_51 != X0_51 ),
    theory(equality)).

cnf(c_2575,plain,
    ( ~ r2_hidden(X0_51,X0_52)
    | r2_hidden(X1_51,k1_xboole_0)
    | k1_xboole_0 != X0_52
    | X1_51 != X0_51 ),
    inference(instantiation,[status(thm)],[c_1949])).

cnf(c_2576,plain,
    ( k1_xboole_0 != X0_52
    | X0_51 != X1_51
    | r2_hidden(X1_51,X0_52) != iProver_top
    | r2_hidden(X0_51,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2575])).

cnf(c_2578,plain,
    ( k1_xboole_0 != sK3
    | sK5 != sK5
    | r2_hidden(sK5,sK3) != iProver_top
    | r2_hidden(sK5,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2576])).

cnf(c_2724,plain,
    ( v2_funct_1(sK4) != iProver_top
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2647,c_30,c_1973,c_1993,c_1994,c_1997,c_2578])).

cnf(c_2725,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK5
    | v2_funct_1(sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_2724])).

cnf(c_3329,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK5 ),
    inference(superposition,[status(thm)],[c_3323,c_2725])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK6,sK3)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1930,negated_conjecture,
    ( r2_hidden(sK6,sK3)
    | ~ v2_funct_1(sK4) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2338,plain,
    ( r2_hidden(sK6,sK3) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1930])).

cnf(c_2646,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK6)) = sK6
    | v2_funct_1(sK4) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2338,c_2343])).

cnf(c_2717,plain,
    ( v2_funct_1(sK4) != iProver_top
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK6)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2646,c_30,c_1973,c_1993,c_1994,c_2578])).

cnf(c_2718,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK6)) = sK6
    | v2_funct_1(sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_2717])).

cnf(c_3330,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK6)) = sK6 ),
    inference(superposition,[status(thm)],[c_3323,c_2718])).

cnf(c_3332,plain,
    ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_3323,c_2337])).

cnf(c_3339,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK6 ),
    inference(light_normalisation,[status(thm)],[c_3330,c_3332])).

cnf(c_3343,plain,
    ( sK6 = sK5 ),
    inference(demodulation,[status(thm)],[c_3329,c_3339])).

cnf(c_2560,plain,
    ( sK6 != X0_51
    | sK5 != X0_51
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_1946])).

cnf(c_2561,plain,
    ( sK6 != sK5
    | sK5 = sK6
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2560])).

cnf(c_16,negated_conjecture,
    ( ~ v2_funct_1(sK4)
    | sK5 != sK6 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1932,negated_conjecture,
    ( ~ v2_funct_1(sK4)
    | sK5 != sK6 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1986,plain,
    ( sK5 != sK6
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1932])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3343,c_3323,c_2561,c_1986,c_1973])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:09:47 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.52/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.52/0.98  
% 1.52/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.52/0.98  
% 1.52/0.98  ------  iProver source info
% 1.52/0.98  
% 1.52/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.52/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.52/0.98  git: non_committed_changes: false
% 1.52/0.98  git: last_make_outside_of_git: false
% 1.52/0.98  
% 1.52/0.98  ------ 
% 1.52/0.98  
% 1.52/0.98  ------ Input Options
% 1.52/0.98  
% 1.52/0.98  --out_options                           all
% 1.52/0.98  --tptp_safe_out                         true
% 1.52/0.98  --problem_path                          ""
% 1.52/0.98  --include_path                          ""
% 1.52/0.98  --clausifier                            res/vclausify_rel
% 1.52/0.98  --clausifier_options                    --mode clausify
% 1.52/0.98  --stdin                                 false
% 1.52/0.98  --stats_out                             all
% 1.52/0.98  
% 1.52/0.98  ------ General Options
% 1.52/0.98  
% 1.52/0.98  --fof                                   false
% 1.52/0.98  --time_out_real                         305.
% 1.52/0.98  --time_out_virtual                      -1.
% 1.52/0.98  --symbol_type_check                     false
% 1.52/0.98  --clausify_out                          false
% 1.52/0.98  --sig_cnt_out                           false
% 1.52/0.98  --trig_cnt_out                          false
% 1.52/0.98  --trig_cnt_out_tolerance                1.
% 1.52/0.98  --trig_cnt_out_sk_spl                   false
% 1.52/0.98  --abstr_cl_out                          false
% 1.52/0.98  
% 1.52/0.98  ------ Global Options
% 1.52/0.98  
% 1.52/0.98  --schedule                              default
% 1.52/0.98  --add_important_lit                     false
% 1.52/0.98  --prop_solver_per_cl                    1000
% 1.52/0.98  --min_unsat_core                        false
% 1.52/0.98  --soft_assumptions                      false
% 1.52/0.98  --soft_lemma_size                       3
% 1.52/0.98  --prop_impl_unit_size                   0
% 1.52/0.98  --prop_impl_unit                        []
% 1.52/0.98  --share_sel_clauses                     true
% 1.52/0.98  --reset_solvers                         false
% 1.52/0.98  --bc_imp_inh                            [conj_cone]
% 1.52/0.98  --conj_cone_tolerance                   3.
% 1.52/0.98  --extra_neg_conj                        none
% 1.52/0.98  --large_theory_mode                     true
% 1.52/0.98  --prolific_symb_bound                   200
% 1.52/0.98  --lt_threshold                          2000
% 1.52/0.98  --clause_weak_htbl                      true
% 1.52/0.98  --gc_record_bc_elim                     false
% 1.52/0.98  
% 1.52/0.98  ------ Preprocessing Options
% 1.52/0.98  
% 1.52/0.98  --preprocessing_flag                    true
% 1.52/0.98  --time_out_prep_mult                    0.1
% 1.52/0.98  --splitting_mode                        input
% 1.52/0.98  --splitting_grd                         true
% 1.52/0.98  --splitting_cvd                         false
% 1.52/0.98  --splitting_cvd_svl                     false
% 1.52/0.98  --splitting_nvd                         32
% 1.52/0.98  --sub_typing                            true
% 1.52/0.98  --prep_gs_sim                           true
% 1.52/0.98  --prep_unflatten                        true
% 1.52/0.98  --prep_res_sim                          true
% 1.52/0.98  --prep_upred                            true
% 1.52/0.98  --prep_sem_filter                       exhaustive
% 1.52/0.98  --prep_sem_filter_out                   false
% 1.52/0.98  --pred_elim                             true
% 1.52/0.98  --res_sim_input                         true
% 1.52/0.98  --eq_ax_congr_red                       true
% 1.52/0.98  --pure_diseq_elim                       true
% 1.52/0.98  --brand_transform                       false
% 1.52/0.98  --non_eq_to_eq                          false
% 1.52/0.98  --prep_def_merge                        true
% 1.52/0.98  --prep_def_merge_prop_impl              false
% 1.52/0.98  --prep_def_merge_mbd                    true
% 1.52/0.98  --prep_def_merge_tr_red                 false
% 1.52/0.98  --prep_def_merge_tr_cl                  false
% 1.52/0.98  --smt_preprocessing                     true
% 1.52/0.98  --smt_ac_axioms                         fast
% 1.52/0.98  --preprocessed_out                      false
% 1.52/0.98  --preprocessed_stats                    false
% 1.52/0.98  
% 1.52/0.98  ------ Abstraction refinement Options
% 1.52/0.98  
% 1.52/0.98  --abstr_ref                             []
% 1.52/0.98  --abstr_ref_prep                        false
% 1.52/0.98  --abstr_ref_until_sat                   false
% 1.52/0.98  --abstr_ref_sig_restrict                funpre
% 1.52/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.52/0.98  --abstr_ref_under                       []
% 1.52/0.98  
% 1.52/0.98  ------ SAT Options
% 1.52/0.98  
% 1.52/0.98  --sat_mode                              false
% 1.52/0.98  --sat_fm_restart_options                ""
% 1.52/0.98  --sat_gr_def                            false
% 1.52/0.98  --sat_epr_types                         true
% 1.52/0.98  --sat_non_cyclic_types                  false
% 1.52/0.98  --sat_finite_models                     false
% 1.52/0.98  --sat_fm_lemmas                         false
% 1.52/0.98  --sat_fm_prep                           false
% 1.52/0.98  --sat_fm_uc_incr                        true
% 1.52/0.98  --sat_out_model                         small
% 1.52/0.98  --sat_out_clauses                       false
% 1.52/0.98  
% 1.52/0.98  ------ QBF Options
% 1.52/0.98  
% 1.52/0.98  --qbf_mode                              false
% 1.52/0.98  --qbf_elim_univ                         false
% 1.52/0.98  --qbf_dom_inst                          none
% 1.52/0.98  --qbf_dom_pre_inst                      false
% 1.52/0.98  --qbf_sk_in                             false
% 1.52/0.98  --qbf_pred_elim                         true
% 1.52/0.98  --qbf_split                             512
% 1.52/0.98  
% 1.52/0.98  ------ BMC1 Options
% 1.52/0.98  
% 1.52/0.98  --bmc1_incremental                      false
% 1.52/0.98  --bmc1_axioms                           reachable_all
% 1.52/0.98  --bmc1_min_bound                        0
% 1.52/0.98  --bmc1_max_bound                        -1
% 1.52/0.98  --bmc1_max_bound_default                -1
% 1.52/0.98  --bmc1_symbol_reachability              true
% 1.52/0.98  --bmc1_property_lemmas                  false
% 1.52/0.98  --bmc1_k_induction                      false
% 1.52/0.98  --bmc1_non_equiv_states                 false
% 1.52/0.98  --bmc1_deadlock                         false
% 1.52/0.98  --bmc1_ucm                              false
% 1.52/0.98  --bmc1_add_unsat_core                   none
% 1.52/0.98  --bmc1_unsat_core_children              false
% 1.52/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.52/0.98  --bmc1_out_stat                         full
% 1.52/0.98  --bmc1_ground_init                      false
% 1.52/0.98  --bmc1_pre_inst_next_state              false
% 1.52/0.98  --bmc1_pre_inst_state                   false
% 1.52/0.98  --bmc1_pre_inst_reach_state             false
% 1.52/0.98  --bmc1_out_unsat_core                   false
% 1.52/0.98  --bmc1_aig_witness_out                  false
% 1.52/0.98  --bmc1_verbose                          false
% 1.52/0.98  --bmc1_dump_clauses_tptp                false
% 1.52/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.52/0.98  --bmc1_dump_file                        -
% 1.52/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.52/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.52/0.98  --bmc1_ucm_extend_mode                  1
% 1.52/0.98  --bmc1_ucm_init_mode                    2
% 1.52/0.98  --bmc1_ucm_cone_mode                    none
% 1.52/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.52/0.98  --bmc1_ucm_relax_model                  4
% 1.52/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.52/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.52/0.98  --bmc1_ucm_layered_model                none
% 1.52/0.98  --bmc1_ucm_max_lemma_size               10
% 1.52/0.98  
% 1.52/0.98  ------ AIG Options
% 1.52/0.98  
% 1.52/0.98  --aig_mode                              false
% 1.52/0.98  
% 1.52/0.98  ------ Instantiation Options
% 1.52/0.98  
% 1.52/0.98  --instantiation_flag                    true
% 1.52/0.98  --inst_sos_flag                         false
% 1.52/0.98  --inst_sos_phase                        true
% 1.52/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.52/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.52/0.98  --inst_lit_sel_side                     num_symb
% 1.52/0.98  --inst_solver_per_active                1400
% 1.52/0.98  --inst_solver_calls_frac                1.
% 1.52/0.98  --inst_passive_queue_type               priority_queues
% 1.52/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.52/0.98  --inst_passive_queues_freq              [25;2]
% 1.52/0.98  --inst_dismatching                      true
% 1.52/0.98  --inst_eager_unprocessed_to_passive     true
% 1.52/0.98  --inst_prop_sim_given                   true
% 1.52/0.98  --inst_prop_sim_new                     false
% 1.52/0.98  --inst_subs_new                         false
% 1.52/0.98  --inst_eq_res_simp                      false
% 1.52/0.98  --inst_subs_given                       false
% 1.52/0.98  --inst_orphan_elimination               true
% 1.52/0.98  --inst_learning_loop_flag               true
% 1.52/0.98  --inst_learning_start                   3000
% 1.52/0.98  --inst_learning_factor                  2
% 1.52/0.98  --inst_start_prop_sim_after_learn       3
% 1.52/0.98  --inst_sel_renew                        solver
% 1.52/0.98  --inst_lit_activity_flag                true
% 1.52/0.98  --inst_restr_to_given                   false
% 1.52/0.98  --inst_activity_threshold               500
% 1.52/0.98  --inst_out_proof                        true
% 1.52/0.98  
% 1.52/0.98  ------ Resolution Options
% 1.52/0.98  
% 1.52/0.98  --resolution_flag                       true
% 1.52/0.98  --res_lit_sel                           adaptive
% 1.52/0.98  --res_lit_sel_side                      none
% 1.52/0.98  --res_ordering                          kbo
% 1.52/0.98  --res_to_prop_solver                    active
% 1.52/0.98  --res_prop_simpl_new                    false
% 1.52/0.98  --res_prop_simpl_given                  true
% 1.52/0.98  --res_passive_queue_type                priority_queues
% 1.52/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.52/0.98  --res_passive_queues_freq               [15;5]
% 1.52/0.98  --res_forward_subs                      full
% 1.52/0.98  --res_backward_subs                     full
% 1.52/0.98  --res_forward_subs_resolution           true
% 1.52/0.98  --res_backward_subs_resolution          true
% 1.52/0.98  --res_orphan_elimination                true
% 1.52/0.98  --res_time_limit                        2.
% 1.52/0.98  --res_out_proof                         true
% 1.52/0.98  
% 1.52/0.98  ------ Superposition Options
% 1.52/0.98  
% 1.52/0.98  --superposition_flag                    true
% 1.52/0.98  --sup_passive_queue_type                priority_queues
% 1.52/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.52/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.52/0.98  --demod_completeness_check              fast
% 1.52/0.98  --demod_use_ground                      true
% 1.52/0.98  --sup_to_prop_solver                    passive
% 1.52/0.98  --sup_prop_simpl_new                    true
% 1.52/0.98  --sup_prop_simpl_given                  true
% 1.52/0.98  --sup_fun_splitting                     false
% 1.52/0.98  --sup_smt_interval                      50000
% 1.52/0.98  
% 1.52/0.98  ------ Superposition Simplification Setup
% 1.52/0.98  
% 1.52/0.98  --sup_indices_passive                   []
% 1.52/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.52/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.98  --sup_full_bw                           [BwDemod]
% 1.52/0.98  --sup_immed_triv                        [TrivRules]
% 1.52/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.52/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.98  --sup_immed_bw_main                     []
% 1.52/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.52/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.52/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.52/0.98  
% 1.52/0.98  ------ Combination Options
% 1.52/0.98  
% 1.52/0.98  --comb_res_mult                         3
% 1.52/0.98  --comb_sup_mult                         2
% 1.52/0.98  --comb_inst_mult                        10
% 1.52/0.98  
% 1.52/0.98  ------ Debug Options
% 1.52/0.98  
% 1.52/0.98  --dbg_backtrace                         false
% 1.52/0.98  --dbg_dump_prop_clauses                 false
% 1.52/0.98  --dbg_dump_prop_clauses_file            -
% 1.52/0.98  --dbg_out_stat                          false
% 1.52/0.98  ------ Parsing...
% 1.52/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.52/0.98  
% 1.52/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.52/0.98  
% 1.52/0.98  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.52/0.98  
% 1.52/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.52/0.98  ------ Proving...
% 1.52/0.98  ------ Problem Properties 
% 1.52/0.98  
% 1.52/0.98  
% 1.52/0.98  clauses                                 20
% 1.52/0.98  conjectures                             5
% 1.52/0.98  EPR                                     7
% 1.52/0.98  Horn                                    14
% 1.52/0.98  unary                                   2
% 1.52/0.98  binary                                  6
% 1.52/0.98  lits                                    54
% 1.52/0.98  lits eq                                 12
% 1.52/0.98  fd_pure                                 0
% 1.52/0.98  fd_pseudo                               0
% 1.52/0.98  fd_cond                                 0
% 1.52/0.98  fd_pseudo_cond                          2
% 1.52/0.98  AC symbols                              0
% 1.52/0.98  
% 1.52/0.98  ------ Schedule dynamic 5 is on 
% 1.52/0.98  
% 1.52/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.52/0.98  
% 1.52/0.98  
% 1.52/0.98  ------ 
% 1.52/0.98  Current options:
% 1.52/0.98  ------ 
% 1.52/0.98  
% 1.52/0.98  ------ Input Options
% 1.52/0.98  
% 1.52/0.98  --out_options                           all
% 1.52/0.98  --tptp_safe_out                         true
% 1.52/0.98  --problem_path                          ""
% 1.52/0.98  --include_path                          ""
% 1.52/0.98  --clausifier                            res/vclausify_rel
% 1.52/0.98  --clausifier_options                    --mode clausify
% 1.52/0.98  --stdin                                 false
% 1.52/0.98  --stats_out                             all
% 1.52/0.98  
% 1.52/0.98  ------ General Options
% 1.52/0.98  
% 1.52/0.98  --fof                                   false
% 1.52/0.98  --time_out_real                         305.
% 1.52/0.98  --time_out_virtual                      -1.
% 1.52/0.98  --symbol_type_check                     false
% 1.52/0.98  --clausify_out                          false
% 1.52/0.98  --sig_cnt_out                           false
% 1.52/0.98  --trig_cnt_out                          false
% 1.52/0.98  --trig_cnt_out_tolerance                1.
% 1.52/0.98  --trig_cnt_out_sk_spl                   false
% 1.52/0.98  --abstr_cl_out                          false
% 1.52/0.98  
% 1.52/0.98  ------ Global Options
% 1.52/0.98  
% 1.52/0.98  --schedule                              default
% 1.52/0.98  --add_important_lit                     false
% 1.52/0.98  --prop_solver_per_cl                    1000
% 1.52/0.98  --min_unsat_core                        false
% 1.52/0.98  --soft_assumptions                      false
% 1.52/0.98  --soft_lemma_size                       3
% 1.52/0.98  --prop_impl_unit_size                   0
% 1.52/0.98  --prop_impl_unit                        []
% 1.52/0.98  --share_sel_clauses                     true
% 1.52/0.98  --reset_solvers                         false
% 1.52/0.98  --bc_imp_inh                            [conj_cone]
% 1.52/0.98  --conj_cone_tolerance                   3.
% 1.52/0.98  --extra_neg_conj                        none
% 1.52/0.98  --large_theory_mode                     true
% 1.52/0.98  --prolific_symb_bound                   200
% 1.52/0.98  --lt_threshold                          2000
% 1.52/0.98  --clause_weak_htbl                      true
% 1.52/0.98  --gc_record_bc_elim                     false
% 1.52/0.98  
% 1.52/0.98  ------ Preprocessing Options
% 1.52/0.98  
% 1.52/0.98  --preprocessing_flag                    true
% 1.52/0.98  --time_out_prep_mult                    0.1
% 1.52/0.98  --splitting_mode                        input
% 1.52/0.98  --splitting_grd                         true
% 1.52/0.98  --splitting_cvd                         false
% 1.52/0.98  --splitting_cvd_svl                     false
% 1.52/0.98  --splitting_nvd                         32
% 1.52/0.98  --sub_typing                            true
% 1.52/0.98  --prep_gs_sim                           true
% 1.52/0.98  --prep_unflatten                        true
% 1.52/0.98  --prep_res_sim                          true
% 1.52/0.98  --prep_upred                            true
% 1.52/0.98  --prep_sem_filter                       exhaustive
% 1.52/0.98  --prep_sem_filter_out                   false
% 1.52/0.98  --pred_elim                             true
% 1.52/0.98  --res_sim_input                         true
% 1.52/0.98  --eq_ax_congr_red                       true
% 1.52/0.98  --pure_diseq_elim                       true
% 1.52/0.98  --brand_transform                       false
% 1.52/0.98  --non_eq_to_eq                          false
% 1.52/0.98  --prep_def_merge                        true
% 1.52/0.98  --prep_def_merge_prop_impl              false
% 1.52/0.98  --prep_def_merge_mbd                    true
% 1.52/0.98  --prep_def_merge_tr_red                 false
% 1.52/0.98  --prep_def_merge_tr_cl                  false
% 1.52/0.98  --smt_preprocessing                     true
% 1.52/0.98  --smt_ac_axioms                         fast
% 1.52/0.98  --preprocessed_out                      false
% 1.52/0.98  --preprocessed_stats                    false
% 1.52/0.98  
% 1.52/0.98  ------ Abstraction refinement Options
% 1.52/0.98  
% 1.52/0.98  --abstr_ref                             []
% 1.52/0.98  --abstr_ref_prep                        false
% 1.52/0.98  --abstr_ref_until_sat                   false
% 1.52/0.98  --abstr_ref_sig_restrict                funpre
% 1.52/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.52/0.98  --abstr_ref_under                       []
% 1.52/0.98  
% 1.52/0.98  ------ SAT Options
% 1.52/0.98  
% 1.52/0.98  --sat_mode                              false
% 1.52/0.98  --sat_fm_restart_options                ""
% 1.52/0.98  --sat_gr_def                            false
% 1.52/0.98  --sat_epr_types                         true
% 1.52/0.98  --sat_non_cyclic_types                  false
% 1.52/0.98  --sat_finite_models                     false
% 1.52/0.98  --sat_fm_lemmas                         false
% 1.52/0.98  --sat_fm_prep                           false
% 1.52/0.98  --sat_fm_uc_incr                        true
% 1.52/0.98  --sat_out_model                         small
% 1.52/0.98  --sat_out_clauses                       false
% 1.52/0.98  
% 1.52/0.98  ------ QBF Options
% 1.52/0.98  
% 1.52/0.98  --qbf_mode                              false
% 1.52/0.98  --qbf_elim_univ                         false
% 1.52/0.98  --qbf_dom_inst                          none
% 1.52/0.98  --qbf_dom_pre_inst                      false
% 1.52/0.98  --qbf_sk_in                             false
% 1.52/0.98  --qbf_pred_elim                         true
% 1.52/0.98  --qbf_split                             512
% 1.52/0.98  
% 1.52/0.98  ------ BMC1 Options
% 1.52/0.98  
% 1.52/0.98  --bmc1_incremental                      false
% 1.52/0.98  --bmc1_axioms                           reachable_all
% 1.52/0.98  --bmc1_min_bound                        0
% 1.52/0.98  --bmc1_max_bound                        -1
% 1.52/0.98  --bmc1_max_bound_default                -1
% 1.52/0.98  --bmc1_symbol_reachability              true
% 1.52/0.98  --bmc1_property_lemmas                  false
% 1.52/0.98  --bmc1_k_induction                      false
% 1.52/0.98  --bmc1_non_equiv_states                 false
% 1.52/0.98  --bmc1_deadlock                         false
% 1.52/0.98  --bmc1_ucm                              false
% 1.52/0.98  --bmc1_add_unsat_core                   none
% 1.52/0.98  --bmc1_unsat_core_children              false
% 1.52/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.52/0.98  --bmc1_out_stat                         full
% 1.52/0.98  --bmc1_ground_init                      false
% 1.52/0.98  --bmc1_pre_inst_next_state              false
% 1.52/0.98  --bmc1_pre_inst_state                   false
% 1.52/0.98  --bmc1_pre_inst_reach_state             false
% 1.52/0.98  --bmc1_out_unsat_core                   false
% 1.52/0.98  --bmc1_aig_witness_out                  false
% 1.52/0.98  --bmc1_verbose                          false
% 1.52/0.98  --bmc1_dump_clauses_tptp                false
% 1.52/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.52/0.98  --bmc1_dump_file                        -
% 1.52/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.52/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.52/0.98  --bmc1_ucm_extend_mode                  1
% 1.52/0.98  --bmc1_ucm_init_mode                    2
% 1.52/0.98  --bmc1_ucm_cone_mode                    none
% 1.52/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.52/0.98  --bmc1_ucm_relax_model                  4
% 1.52/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.52/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.52/0.98  --bmc1_ucm_layered_model                none
% 1.52/0.98  --bmc1_ucm_max_lemma_size               10
% 1.52/0.98  
% 1.52/0.98  ------ AIG Options
% 1.52/0.98  
% 1.52/0.98  --aig_mode                              false
% 1.52/0.98  
% 1.52/0.98  ------ Instantiation Options
% 1.52/0.98  
% 1.52/0.98  --instantiation_flag                    true
% 1.52/0.98  --inst_sos_flag                         false
% 1.52/0.98  --inst_sos_phase                        true
% 1.52/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.52/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.52/0.98  --inst_lit_sel_side                     none
% 1.52/0.98  --inst_solver_per_active                1400
% 1.52/0.98  --inst_solver_calls_frac                1.
% 1.52/0.98  --inst_passive_queue_type               priority_queues
% 1.52/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.52/0.98  --inst_passive_queues_freq              [25;2]
% 1.52/0.98  --inst_dismatching                      true
% 1.52/0.98  --inst_eager_unprocessed_to_passive     true
% 1.52/0.98  --inst_prop_sim_given                   true
% 1.52/0.98  --inst_prop_sim_new                     false
% 1.52/0.98  --inst_subs_new                         false
% 1.52/0.98  --inst_eq_res_simp                      false
% 1.52/0.98  --inst_subs_given                       false
% 1.52/0.98  --inst_orphan_elimination               true
% 1.52/0.98  --inst_learning_loop_flag               true
% 1.52/0.98  --inst_learning_start                   3000
% 1.52/0.98  --inst_learning_factor                  2
% 1.52/0.98  --inst_start_prop_sim_after_learn       3
% 1.52/0.98  --inst_sel_renew                        solver
% 1.52/0.98  --inst_lit_activity_flag                true
% 1.52/0.98  --inst_restr_to_given                   false
% 1.52/0.98  --inst_activity_threshold               500
% 1.52/0.98  --inst_out_proof                        true
% 1.52/0.98  
% 1.52/0.98  ------ Resolution Options
% 1.52/0.98  
% 1.52/0.98  --resolution_flag                       false
% 1.52/0.98  --res_lit_sel                           adaptive
% 1.52/0.98  --res_lit_sel_side                      none
% 1.52/0.98  --res_ordering                          kbo
% 1.52/0.98  --res_to_prop_solver                    active
% 1.52/0.98  --res_prop_simpl_new                    false
% 1.52/0.98  --res_prop_simpl_given                  true
% 1.52/0.98  --res_passive_queue_type                priority_queues
% 1.52/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.52/0.98  --res_passive_queues_freq               [15;5]
% 1.52/0.98  --res_forward_subs                      full
% 1.52/0.98  --res_backward_subs                     full
% 1.52/0.98  --res_forward_subs_resolution           true
% 1.52/0.98  --res_backward_subs_resolution          true
% 1.52/0.98  --res_orphan_elimination                true
% 1.52/0.98  --res_time_limit                        2.
% 1.52/0.98  --res_out_proof                         true
% 1.52/0.98  
% 1.52/0.98  ------ Superposition Options
% 1.52/0.98  
% 1.52/0.98  --superposition_flag                    true
% 1.52/0.98  --sup_passive_queue_type                priority_queues
% 1.52/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.52/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.52/0.98  --demod_completeness_check              fast
% 1.52/0.98  --demod_use_ground                      true
% 1.52/0.98  --sup_to_prop_solver                    passive
% 1.52/0.98  --sup_prop_simpl_new                    true
% 1.52/0.98  --sup_prop_simpl_given                  true
% 1.52/0.98  --sup_fun_splitting                     false
% 1.52/0.98  --sup_smt_interval                      50000
% 1.52/0.98  
% 1.52/0.98  ------ Superposition Simplification Setup
% 1.52/0.98  
% 1.52/0.98  --sup_indices_passive                   []
% 1.52/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.52/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.98  --sup_full_bw                           [BwDemod]
% 1.52/0.98  --sup_immed_triv                        [TrivRules]
% 1.52/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.52/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.98  --sup_immed_bw_main                     []
% 1.52/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.52/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.52/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.52/0.98  
% 1.52/0.98  ------ Combination Options
% 1.52/0.98  
% 1.52/0.98  --comb_res_mult                         3
% 1.52/0.98  --comb_sup_mult                         2
% 1.52/0.98  --comb_inst_mult                        10
% 1.52/0.98  
% 1.52/0.98  ------ Debug Options
% 1.52/0.98  
% 1.52/0.98  --dbg_backtrace                         false
% 1.52/0.98  --dbg_dump_prop_clauses                 false
% 1.52/0.98  --dbg_dump_prop_clauses_file            -
% 1.52/0.98  --dbg_out_stat                          false
% 1.52/0.98  
% 1.52/0.98  
% 1.52/0.98  
% 1.52/0.98  
% 1.52/0.98  ------ Proving...
% 1.52/0.98  
% 1.52/0.98  
% 1.52/0.98  % SZS status Theorem for theBenchmark.p
% 1.52/0.98  
% 1.52/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.52/0.98  
% 1.52/0.98  fof(f7,axiom,(
% 1.52/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 1.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.98  
% 1.52/0.98  fof(f18,plain,(
% 1.52/0.98    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.52/0.98    inference(ennf_transformation,[],[f7])).
% 1.52/0.98  
% 1.52/0.98  fof(f19,plain,(
% 1.52/0.98    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.52/0.98    inference(flattening,[],[f18])).
% 1.52/0.98  
% 1.52/0.98  fof(f30,plain,(
% 1.52/0.98    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.52/0.98    inference(nnf_transformation,[],[f19])).
% 1.52/0.98  
% 1.52/0.98  fof(f31,plain,(
% 1.52/0.98    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.52/0.98    inference(rectify,[],[f30])).
% 1.52/0.98  
% 1.52/0.98  fof(f32,plain,(
% 1.52/0.98    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK1(X0) != sK2(X0) & k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0)) & r2_hidden(sK2(X0),k1_relat_1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0))))),
% 1.52/0.98    introduced(choice_axiom,[])).
% 1.52/0.98  
% 1.52/0.98  fof(f33,plain,(
% 1.52/0.98    ! [X0] : (((v2_funct_1(X0) | (sK1(X0) != sK2(X0) & k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0)) & r2_hidden(sK2(X0),k1_relat_1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.52/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f31,f32])).
% 1.52/0.98  
% 1.52/0.98  fof(f52,plain,(
% 1.52/0.98    ( ! [X0] : (v2_funct_1(X0) | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.52/0.98    inference(cnf_transformation,[],[f33])).
% 1.52/0.98  
% 1.52/0.98  fof(f10,conjecture,(
% 1.52/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 1.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.98  
% 1.52/0.98  fof(f11,negated_conjecture,(
% 1.52/0.98    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 1.52/0.98    inference(negated_conjecture,[],[f10])).
% 1.52/0.98  
% 1.52/0.98  fof(f23,plain,(
% 1.52/0.98    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.52/0.98    inference(ennf_transformation,[],[f11])).
% 1.52/0.98  
% 1.52/0.98  fof(f24,plain,(
% 1.52/0.98    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.52/0.98    inference(flattening,[],[f23])).
% 1.52/0.98  
% 1.52/0.98  fof(f34,plain,(
% 1.52/0.98    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.52/0.98    inference(nnf_transformation,[],[f24])).
% 1.52/0.98  
% 1.52/0.98  fof(f35,plain,(
% 1.52/0.98    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.52/0.98    inference(flattening,[],[f34])).
% 1.52/0.98  
% 1.52/0.98  fof(f36,plain,(
% 1.52/0.98    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.52/0.98    inference(rectify,[],[f35])).
% 1.52/0.98  
% 1.52/0.98  fof(f38,plain,(
% 1.52/0.98    ( ! [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (sK5 != sK6 & k1_funct_1(X1,sK5) = k1_funct_1(X1,sK6) & r2_hidden(sK6,X0) & r2_hidden(sK5,X0))) )),
% 1.52/0.98    introduced(choice_axiom,[])).
% 1.52/0.98  
% 1.52/0.98  fof(f37,plain,(
% 1.52/0.98    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK4,X2) = k1_funct_1(sK4,X3) & r2_hidden(X3,sK3) & r2_hidden(X2,sK3)) | ~v2_funct_1(sK4)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK4,X4) != k1_funct_1(sK4,X5) | ~r2_hidden(X5,sK3) | ~r2_hidden(X4,sK3)) | v2_funct_1(sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) & v1_funct_2(sK4,sK3,sK3) & v1_funct_1(sK4))),
% 1.52/0.98    introduced(choice_axiom,[])).
% 1.52/0.98  
% 1.52/0.98  fof(f39,plain,(
% 1.52/0.98    ((sK5 != sK6 & k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) & r2_hidden(sK6,sK3) & r2_hidden(sK5,sK3)) | ~v2_funct_1(sK4)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK4,X4) != k1_funct_1(sK4,X5) | ~r2_hidden(X5,sK3) | ~r2_hidden(X4,sK3)) | v2_funct_1(sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) & v1_funct_2(sK4,sK3,sK3) & v1_funct_1(sK4)),
% 1.52/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f36,f38,f37])).
% 1.52/0.98  
% 1.52/0.98  fof(f56,plain,(
% 1.52/0.98    v1_funct_1(sK4)),
% 1.52/0.98    inference(cnf_transformation,[],[f39])).
% 1.52/0.98  
% 1.52/0.98  fof(f6,axiom,(
% 1.52/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.98  
% 1.52/0.98  fof(f48,plain,(
% 1.52/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.52/0.98    inference(cnf_transformation,[],[f6])).
% 1.52/0.98  
% 1.52/0.98  fof(f4,axiom,(
% 1.52/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.98  
% 1.52/0.98  fof(f16,plain,(
% 1.52/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.52/0.98    inference(ennf_transformation,[],[f4])).
% 1.52/0.98  
% 1.52/0.98  fof(f45,plain,(
% 1.52/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.52/0.98    inference(cnf_transformation,[],[f16])).
% 1.52/0.98  
% 1.52/0.98  fof(f58,plain,(
% 1.52/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))),
% 1.52/0.98    inference(cnf_transformation,[],[f39])).
% 1.52/0.98  
% 1.52/0.98  fof(f62,plain,(
% 1.52/0.98    k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) | ~v2_funct_1(sK4)),
% 1.52/0.98    inference(cnf_transformation,[],[f39])).
% 1.52/0.98  
% 1.52/0.98  fof(f59,plain,(
% 1.52/0.98    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK4,X4) != k1_funct_1(sK4,X5) | ~r2_hidden(X5,sK3) | ~r2_hidden(X4,sK3) | v2_funct_1(sK4)) )),
% 1.52/0.98    inference(cnf_transformation,[],[f39])).
% 1.52/0.98  
% 1.52/0.98  fof(f50,plain,(
% 1.52/0.98    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK1(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.52/0.98    inference(cnf_transformation,[],[f33])).
% 1.52/0.98  
% 1.52/0.98  fof(f51,plain,(
% 1.52/0.98    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK2(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.52/0.98    inference(cnf_transformation,[],[f33])).
% 1.52/0.98  
% 1.52/0.98  fof(f5,axiom,(
% 1.52/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.98  
% 1.52/0.98  fof(f17,plain,(
% 1.52/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.52/0.98    inference(ennf_transformation,[],[f5])).
% 1.52/0.98  
% 1.52/0.98  fof(f29,plain,(
% 1.52/0.98    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.52/0.98    inference(nnf_transformation,[],[f17])).
% 1.52/0.98  
% 1.52/0.98  fof(f46,plain,(
% 1.52/0.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.52/0.98    inference(cnf_transformation,[],[f29])).
% 1.52/0.98  
% 1.52/0.98  fof(f8,axiom,(
% 1.52/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.98  
% 1.52/0.98  fof(f13,plain,(
% 1.52/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.52/0.98    inference(pure_predicate_removal,[],[f8])).
% 1.52/0.98  
% 1.52/0.98  fof(f20,plain,(
% 1.52/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.98    inference(ennf_transformation,[],[f13])).
% 1.52/0.98  
% 1.52/0.98  fof(f54,plain,(
% 1.52/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.52/0.98    inference(cnf_transformation,[],[f20])).
% 1.52/0.98  
% 1.52/0.98  fof(f53,plain,(
% 1.52/0.98    ( ! [X0] : (v2_funct_1(X0) | sK1(X0) != sK2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.52/0.98    inference(cnf_transformation,[],[f33])).
% 1.52/0.98  
% 1.52/0.98  fof(f2,axiom,(
% 1.52/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.98  
% 1.52/0.98  fof(f15,plain,(
% 1.52/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.52/0.98    inference(ennf_transformation,[],[f2])).
% 1.52/0.98  
% 1.52/0.98  fof(f25,plain,(
% 1.52/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.98    inference(nnf_transformation,[],[f15])).
% 1.52/0.98  
% 1.52/0.98  fof(f26,plain,(
% 1.52/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.98    inference(rectify,[],[f25])).
% 1.52/0.98  
% 1.52/0.98  fof(f27,plain,(
% 1.52/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.52/0.98    introduced(choice_axiom,[])).
% 1.52/0.98  
% 1.52/0.98  fof(f28,plain,(
% 1.52/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 1.52/0.98  
% 1.52/0.98  fof(f41,plain,(
% 1.52/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.52/0.98    inference(cnf_transformation,[],[f28])).
% 1.52/0.98  
% 1.52/0.98  fof(f60,plain,(
% 1.52/0.98    r2_hidden(sK5,sK3) | ~v2_funct_1(sK4)),
% 1.52/0.98    inference(cnf_transformation,[],[f39])).
% 1.52/0.98  
% 1.52/0.98  fof(f9,axiom,(
% 1.52/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 1.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.98  
% 1.52/0.98  fof(f21,plain,(
% 1.52/0.98    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.52/0.98    inference(ennf_transformation,[],[f9])).
% 1.52/0.98  
% 1.52/0.98  fof(f22,plain,(
% 1.52/0.98    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.52/0.98    inference(flattening,[],[f21])).
% 1.52/0.98  
% 1.52/0.98  fof(f55,plain,(
% 1.52/0.98    ( ! [X2,X0,X3,X1] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.52/0.98    inference(cnf_transformation,[],[f22])).
% 1.52/0.98  
% 1.52/0.98  fof(f57,plain,(
% 1.52/0.98    v1_funct_2(sK4,sK3,sK3)),
% 1.52/0.98    inference(cnf_transformation,[],[f39])).
% 1.52/0.98  
% 1.52/0.98  fof(f1,axiom,(
% 1.52/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.98  
% 1.52/0.98  fof(f12,plain,(
% 1.52/0.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.52/0.98    inference(unused_predicate_definition_removal,[],[f1])).
% 1.52/0.98  
% 1.52/0.98  fof(f14,plain,(
% 1.52/0.98    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.52/0.98    inference(ennf_transformation,[],[f12])).
% 1.52/0.98  
% 1.52/0.98  fof(f40,plain,(
% 1.52/0.98    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.52/0.98    inference(cnf_transformation,[],[f14])).
% 1.52/0.98  
% 1.52/0.98  fof(f3,axiom,(
% 1.52/0.98    v1_xboole_0(k1_xboole_0)),
% 1.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.98  
% 1.52/0.98  fof(f44,plain,(
% 1.52/0.98    v1_xboole_0(k1_xboole_0)),
% 1.52/0.98    inference(cnf_transformation,[],[f3])).
% 1.52/0.98  
% 1.52/0.98  fof(f61,plain,(
% 1.52/0.98    r2_hidden(sK6,sK3) | ~v2_funct_1(sK4)),
% 1.52/0.98    inference(cnf_transformation,[],[f39])).
% 1.52/0.98  
% 1.52/0.98  fof(f63,plain,(
% 1.52/0.98    sK5 != sK6 | ~v2_funct_1(sK4)),
% 1.52/0.98    inference(cnf_transformation,[],[f39])).
% 1.52/0.98  
% 1.52/0.98  cnf(c_10,plain,
% 1.52/0.98      ( ~ v1_funct_1(X0)
% 1.52/0.98      | v2_funct_1(X0)
% 1.52/0.98      | ~ v1_relat_1(X0)
% 1.52/0.98      | k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK1(X0)) ),
% 1.52/0.98      inference(cnf_transformation,[],[f52]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_23,negated_conjecture,
% 1.52/0.99      ( v1_funct_1(sK4) ),
% 1.52/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_460,plain,
% 1.52/0.99      ( v2_funct_1(X0)
% 1.52/0.99      | ~ v1_relat_1(X0)
% 1.52/0.99      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0))
% 1.52/0.99      | sK4 != X0 ),
% 1.52/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_23]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_461,plain,
% 1.52/0.99      ( v2_funct_1(sK4)
% 1.52/0.99      | ~ v1_relat_1(sK4)
% 1.52/0.99      | k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK2(sK4)) ),
% 1.52/0.99      inference(unflattening,[status(thm)],[c_460]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1920,plain,
% 1.52/0.99      ( v2_funct_1(sK4)
% 1.52/0.99      | ~ v1_relat_1(sK4)
% 1.52/0.99      | k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK2(sK4)) ),
% 1.52/0.99      inference(subtyping,[status(esa)],[c_461]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2350,plain,
% 1.52/0.99      ( k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK2(sK4))
% 1.52/0.99      | v2_funct_1(sK4) = iProver_top
% 1.52/0.99      | v1_relat_1(sK4) != iProver_top ),
% 1.52/0.99      inference(predicate_to_equality,[status(thm)],[c_1920]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_8,plain,
% 1.52/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.52/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1933,plain,
% 1.52/0.99      ( v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
% 1.52/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1983,plain,
% 1.52/0.99      ( v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) = iProver_top ),
% 1.52/0.99      inference(predicate_to_equality,[status(thm)],[c_1933]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1985,plain,
% 1.52/0.99      ( v1_relat_1(k2_zfmisc_1(sK3,sK3)) = iProver_top ),
% 1.52/0.99      inference(instantiation,[status(thm)],[c_1983]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2006,plain,
% 1.52/0.99      ( k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK2(sK4))
% 1.52/0.99      | v2_funct_1(sK4) = iProver_top
% 1.52/0.99      | v1_relat_1(sK4) != iProver_top ),
% 1.52/0.99      inference(predicate_to_equality,[status(thm)],[c_1920]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_5,plain,
% 1.52/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.52/0.99      | ~ v1_relat_1(X1)
% 1.52/0.99      | v1_relat_1(X0) ),
% 1.52/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_21,negated_conjecture,
% 1.52/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) ),
% 1.52/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_306,plain,
% 1.52/0.99      ( ~ v1_relat_1(X0)
% 1.52/0.99      | v1_relat_1(X1)
% 1.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(X0)
% 1.52/0.99      | sK4 != X1 ),
% 1.52/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_21]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_307,plain,
% 1.52/0.99      ( ~ v1_relat_1(X0)
% 1.52/0.99      | v1_relat_1(sK4)
% 1.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(X0) ),
% 1.52/0.99      inference(unflattening,[status(thm)],[c_306]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1925,plain,
% 1.52/0.99      ( ~ v1_relat_1(X0_50)
% 1.52/0.99      | v1_relat_1(sK4)
% 1.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(X0_50) ),
% 1.52/0.99      inference(subtyping,[status(esa)],[c_307]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2510,plain,
% 1.52/0.99      ( ~ v1_relat_1(k2_zfmisc_1(X0_52,X1_52))
% 1.52/0.99      | v1_relat_1(sK4)
% 1.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)) ),
% 1.52/0.99      inference(instantiation,[status(thm)],[c_1925]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2511,plain,
% 1.52/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))
% 1.52/0.99      | v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) != iProver_top
% 1.52/0.99      | v1_relat_1(sK4) = iProver_top ),
% 1.52/0.99      inference(predicate_to_equality,[status(thm)],[c_2510]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2513,plain,
% 1.52/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.52/0.99      | v1_relat_1(k2_zfmisc_1(sK3,sK3)) != iProver_top
% 1.52/0.99      | v1_relat_1(sK4) = iProver_top ),
% 1.52/0.99      inference(instantiation,[status(thm)],[c_2511]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1945,plain,( X0_53 = X0_53 ),theory(equality) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2539,plain,
% 1.52/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) = k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) ),
% 1.52/0.99      inference(instantiation,[status(thm)],[c_1945]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_3055,plain,
% 1.52/0.99      ( v2_funct_1(sK4) = iProver_top
% 1.52/0.99      | k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK2(sK4)) ),
% 1.52/0.99      inference(global_propositional_subsumption,
% 1.52/0.99                [status(thm)],
% 1.52/0.99                [c_2350,c_1985,c_2006,c_2513,c_2539]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_3056,plain,
% 1.52/0.99      ( k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK2(sK4))
% 1.52/0.99      | v2_funct_1(sK4) = iProver_top ),
% 1.52/0.99      inference(renaming,[status(thm)],[c_3055]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_17,negated_conjecture,
% 1.52/0.99      ( ~ v2_funct_1(sK4) | k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
% 1.52/0.99      inference(cnf_transformation,[],[f62]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1931,negated_conjecture,
% 1.52/0.99      ( ~ v2_funct_1(sK4) | k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
% 1.52/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2337,plain,
% 1.52/0.99      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
% 1.52/0.99      | v2_funct_1(sK4) != iProver_top ),
% 1.52/0.99      inference(predicate_to_equality,[status(thm)],[c_1931]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_3065,plain,
% 1.52/0.99      ( k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK2(sK4))
% 1.52/0.99      | k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5) ),
% 1.52/0.99      inference(superposition,[status(thm)],[c_3056,c_2337]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_20,negated_conjecture,
% 1.52/0.99      ( ~ r2_hidden(X0,sK3)
% 1.52/0.99      | ~ r2_hidden(X1,sK3)
% 1.52/0.99      | v2_funct_1(sK4)
% 1.52/0.99      | X1 = X0
% 1.52/0.99      | k1_funct_1(sK4,X1) != k1_funct_1(sK4,X0) ),
% 1.52/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1928,negated_conjecture,
% 1.52/0.99      ( ~ r2_hidden(X0_51,sK3)
% 1.52/0.99      | ~ r2_hidden(X1_51,sK3)
% 1.52/0.99      | v2_funct_1(sK4)
% 1.52/0.99      | X1_51 = X0_51
% 1.52/0.99      | k1_funct_1(sK4,X1_51) != k1_funct_1(sK4,X0_51) ),
% 1.52/0.99      inference(subtyping,[status(esa)],[c_20]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2340,plain,
% 1.52/0.99      ( X0_51 = X1_51
% 1.52/0.99      | k1_funct_1(sK4,X0_51) != k1_funct_1(sK4,X1_51)
% 1.52/0.99      | r2_hidden(X0_51,sK3) != iProver_top
% 1.52/0.99      | r2_hidden(X1_51,sK3) != iProver_top
% 1.52/0.99      | v2_funct_1(sK4) = iProver_top ),
% 1.52/0.99      inference(predicate_to_equality,[status(thm)],[c_1928]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_3095,plain,
% 1.52/0.99      ( k1_funct_1(sK4,sK1(sK4)) != k1_funct_1(sK4,X0_51)
% 1.52/0.99      | k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
% 1.52/0.99      | sK2(sK4) = X0_51
% 1.52/0.99      | r2_hidden(X0_51,sK3) != iProver_top
% 1.52/0.99      | r2_hidden(sK2(sK4),sK3) != iProver_top
% 1.52/0.99      | v2_funct_1(sK4) = iProver_top ),
% 1.52/0.99      inference(superposition,[status(thm)],[c_3065,c_2340]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_24,plain,
% 1.52/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 1.52/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_12,plain,
% 1.52/0.99      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 1.52/0.99      | ~ v1_funct_1(X0)
% 1.52/0.99      | v2_funct_1(X0)
% 1.52/0.99      | ~ v1_relat_1(X0) ),
% 1.52/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_43,plain,
% 1.52/0.99      ( r2_hidden(sK1(X0),k1_relat_1(X0)) = iProver_top
% 1.52/0.99      | v1_funct_1(X0) != iProver_top
% 1.52/0.99      | v2_funct_1(X0) = iProver_top
% 1.52/0.99      | v1_relat_1(X0) != iProver_top ),
% 1.52/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_45,plain,
% 1.52/0.99      ( r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top
% 1.52/0.99      | v1_funct_1(sK4) != iProver_top
% 1.52/0.99      | v2_funct_1(sK4) = iProver_top
% 1.52/0.99      | v1_relat_1(sK4) != iProver_top ),
% 1.52/0.99      inference(instantiation,[status(thm)],[c_43]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_11,plain,
% 1.52/0.99      ( r2_hidden(sK2(X0),k1_relat_1(X0))
% 1.52/0.99      | ~ v1_funct_1(X0)
% 1.52/0.99      | v2_funct_1(X0)
% 1.52/0.99      | ~ v1_relat_1(X0) ),
% 1.52/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_46,plain,
% 1.52/0.99      ( r2_hidden(sK2(X0),k1_relat_1(X0)) = iProver_top
% 1.52/0.99      | v1_funct_1(X0) != iProver_top
% 1.52/0.99      | v2_funct_1(X0) = iProver_top
% 1.52/0.99      | v1_relat_1(X0) != iProver_top ),
% 1.52/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_48,plain,
% 1.52/0.99      ( r2_hidden(sK2(sK4),k1_relat_1(sK4)) = iProver_top
% 1.52/0.99      | v1_funct_1(sK4) != iProver_top
% 1.52/0.99      | v2_funct_1(sK4) = iProver_top
% 1.52/0.99      | v1_relat_1(sK4) != iProver_top ),
% 1.52/0.99      inference(instantiation,[status(thm)],[c_46]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1957,plain,
% 1.52/0.99      ( sK2(X0_50) = sK2(X1_50) | X0_50 != X1_50 ),
% 1.52/0.99      theory(equality) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1968,plain,
% 1.52/0.99      ( sK2(sK4) = sK2(sK4) | sK4 != sK4 ),
% 1.52/0.99      inference(instantiation,[status(thm)],[c_1957]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1942,plain,( X0_50 = X0_50 ),theory(equality) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1972,plain,
% 1.52/0.99      ( sK4 = sK4 ),
% 1.52/0.99      inference(instantiation,[status(thm)],[c_1942]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_7,plain,
% 1.52/0.99      ( ~ v4_relat_1(X0,X1)
% 1.52/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 1.52/0.99      | ~ v1_relat_1(X0) ),
% 1.52/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_14,plain,
% 1.52/0.99      ( v4_relat_1(X0,X1)
% 1.52/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.52/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_319,plain,
% 1.52/0.99      ( v4_relat_1(X0,X1)
% 1.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.52/0.99      | sK4 != X0 ),
% 1.52/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_320,plain,
% 1.52/0.99      ( v4_relat_1(sK4,X0)
% 1.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) ),
% 1.52/0.99      inference(unflattening,[status(thm)],[c_319]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_339,plain,
% 1.52/0.99      ( r1_tarski(k1_relat_1(X0),X1)
% 1.52/0.99      | ~ v1_relat_1(X0)
% 1.52/0.99      | X2 != X1
% 1.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.52/0.99      | sK4 != X0 ),
% 1.52/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_320]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_340,plain,
% 1.52/0.99      ( r1_tarski(k1_relat_1(sK4),X0)
% 1.52/0.99      | ~ v1_relat_1(sK4)
% 1.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) ),
% 1.52/0.99      inference(unflattening,[status(thm)],[c_339]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1924,plain,
% 1.52/0.99      ( r1_tarski(k1_relat_1(sK4),X0_52)
% 1.52/0.99      | ~ v1_relat_1(sK4)
% 1.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) ),
% 1.52/0.99      inference(subtyping,[status(esa)],[c_340]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1999,plain,
% 1.52/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.52/0.99      | r1_tarski(k1_relat_1(sK4),X0_52) = iProver_top
% 1.52/0.99      | v1_relat_1(sK4) != iProver_top ),
% 1.52/0.99      inference(predicate_to_equality,[status(thm)],[c_1924]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2001,plain,
% 1.52/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.52/0.99      | r1_tarski(k1_relat_1(sK4),sK3) = iProver_top
% 1.52/0.99      | v1_relat_1(sK4) != iProver_top ),
% 1.52/0.99      inference(instantiation,[status(thm)],[c_1999]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_9,plain,
% 1.52/0.99      ( ~ v1_funct_1(X0)
% 1.52/0.99      | v2_funct_1(X0)
% 1.52/0.99      | ~ v1_relat_1(X0)
% 1.52/0.99      | sK2(X0) != sK1(X0) ),
% 1.52/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_473,plain,
% 1.52/0.99      ( v2_funct_1(X0)
% 1.52/0.99      | ~ v1_relat_1(X0)
% 1.52/0.99      | sK2(X0) != sK1(X0)
% 1.52/0.99      | sK4 != X0 ),
% 1.52/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_23]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_474,plain,
% 1.52/0.99      ( v2_funct_1(sK4) | ~ v1_relat_1(sK4) | sK2(sK4) != sK1(sK4) ),
% 1.52/0.99      inference(unflattening,[status(thm)],[c_473]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1919,plain,
% 1.52/0.99      ( v2_funct_1(sK4) | ~ v1_relat_1(sK4) | sK2(sK4) != sK1(sK4) ),
% 1.52/0.99      inference(subtyping,[status(esa)],[c_474]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2007,plain,
% 1.52/0.99      ( sK2(sK4) != sK1(sK4)
% 1.52/0.99      | v2_funct_1(sK4) = iProver_top
% 1.52/0.99      | v1_relat_1(sK4) != iProver_top ),
% 1.52/0.99      inference(predicate_to_equality,[status(thm)],[c_1919]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1946,plain,
% 1.52/0.99      ( X0_51 != X1_51 | X2_51 != X1_51 | X2_51 = X0_51 ),
% 1.52/0.99      theory(equality) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2736,plain,
% 1.52/0.99      ( sK2(sK4) != X0_51 | sK2(sK4) = sK1(sK4) | sK1(sK4) != X0_51 ),
% 1.52/0.99      inference(instantiation,[status(thm)],[c_1946]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2804,plain,
% 1.52/0.99      ( sK2(sK4) != sK2(sK4)
% 1.52/0.99      | sK2(sK4) = sK1(sK4)
% 1.52/0.99      | sK1(sK4) != sK2(sK4) ),
% 1.52/0.99      inference(instantiation,[status(thm)],[c_2736]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_3,plain,
% 1.52/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 1.52/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1934,plain,
% 1.52/0.99      ( ~ r1_tarski(X0_52,X1_52)
% 1.52/0.99      | ~ r2_hidden(X0_51,X0_52)
% 1.52/0.99      | r2_hidden(X0_51,X1_52) ),
% 1.52/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2881,plain,
% 1.52/0.99      ( ~ r1_tarski(k1_relat_1(sK4),X0_52)
% 1.52/0.99      | r2_hidden(sK1(sK4),X0_52)
% 1.52/0.99      | ~ r2_hidden(sK1(sK4),k1_relat_1(sK4)) ),
% 1.52/0.99      inference(instantiation,[status(thm)],[c_1934]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2882,plain,
% 1.52/0.99      ( r1_tarski(k1_relat_1(sK4),X0_52) != iProver_top
% 1.52/0.99      | r2_hidden(sK1(sK4),X0_52) = iProver_top
% 1.52/0.99      | r2_hidden(sK1(sK4),k1_relat_1(sK4)) != iProver_top ),
% 1.52/0.99      inference(predicate_to_equality,[status(thm)],[c_2881]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2884,plain,
% 1.52/0.99      ( r1_tarski(k1_relat_1(sK4),sK3) != iProver_top
% 1.52/0.99      | r2_hidden(sK1(sK4),k1_relat_1(sK4)) != iProver_top
% 1.52/0.99      | r2_hidden(sK1(sK4),sK3) = iProver_top ),
% 1.52/0.99      inference(instantiation,[status(thm)],[c_2882]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2886,plain,
% 1.52/0.99      ( ~ r1_tarski(k1_relat_1(sK4),X0_52)
% 1.52/0.99      | r2_hidden(sK2(sK4),X0_52)
% 1.52/0.99      | ~ r2_hidden(sK2(sK4),k1_relat_1(sK4)) ),
% 1.52/0.99      inference(instantiation,[status(thm)],[c_1934]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2887,plain,
% 1.52/0.99      ( r1_tarski(k1_relat_1(sK4),X0_52) != iProver_top
% 1.52/0.99      | r2_hidden(sK2(sK4),X0_52) = iProver_top
% 1.52/0.99      | r2_hidden(sK2(sK4),k1_relat_1(sK4)) != iProver_top ),
% 1.52/0.99      inference(predicate_to_equality,[status(thm)],[c_2886]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2889,plain,
% 1.52/0.99      ( r1_tarski(k1_relat_1(sK4),sK3) != iProver_top
% 1.52/0.99      | r2_hidden(sK2(sK4),k1_relat_1(sK4)) != iProver_top
% 1.52/0.99      | r2_hidden(sK2(sK4),sK3) = iProver_top ),
% 1.52/0.99      inference(instantiation,[status(thm)],[c_2887]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_3157,plain,
% 1.52/0.99      ( ~ r2_hidden(sK2(sK4),sK3)
% 1.52/0.99      | ~ r2_hidden(sK1(sK4),sK3)
% 1.52/0.99      | v2_funct_1(sK4)
% 1.52/0.99      | k1_funct_1(sK4,sK1(sK4)) != k1_funct_1(sK4,sK2(sK4))
% 1.52/0.99      | sK1(sK4) = sK2(sK4) ),
% 1.52/0.99      inference(instantiation,[status(thm)],[c_1928]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_3158,plain,
% 1.52/0.99      ( k1_funct_1(sK4,sK1(sK4)) != k1_funct_1(sK4,sK2(sK4))
% 1.52/0.99      | sK1(sK4) = sK2(sK4)
% 1.52/0.99      | r2_hidden(sK2(sK4),sK3) != iProver_top
% 1.52/0.99      | r2_hidden(sK1(sK4),sK3) != iProver_top
% 1.52/0.99      | v2_funct_1(sK4) = iProver_top ),
% 1.52/0.99      inference(predicate_to_equality,[status(thm)],[c_3157]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_3323,plain,
% 1.52/0.99      ( v2_funct_1(sK4) = iProver_top ),
% 1.52/0.99      inference(global_propositional_subsumption,
% 1.52/0.99                [status(thm)],
% 1.52/0.99                [c_3095,c_24,c_45,c_48,c_1968,c_1972,c_1985,c_2001,
% 1.52/0.99                 c_2006,c_2007,c_2513,c_2539,c_2804,c_2884,c_2889,c_3158]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_19,negated_conjecture,
% 1.52/0.99      ( r2_hidden(sK5,sK3) | ~ v2_funct_1(sK4) ),
% 1.52/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1929,negated_conjecture,
% 1.52/0.99      ( r2_hidden(sK5,sK3) | ~ v2_funct_1(sK4) ),
% 1.52/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2339,plain,
% 1.52/0.99      ( r2_hidden(sK5,sK3) = iProver_top
% 1.52/0.99      | v2_funct_1(sK4) != iProver_top ),
% 1.52/0.99      inference(predicate_to_equality,[status(thm)],[c_1929]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_15,plain,
% 1.52/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 1.52/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.52/0.99      | ~ r2_hidden(X3,X1)
% 1.52/0.99      | ~ v1_funct_1(X0)
% 1.52/0.99      | ~ v2_funct_1(X0)
% 1.52/0.99      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
% 1.52/0.99      | k1_xboole_0 = X2 ),
% 1.52/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_22,negated_conjecture,
% 1.52/0.99      ( v1_funct_2(sK4,sK3,sK3) ),
% 1.52/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_277,plain,
% 1.52/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.52/0.99      | ~ r2_hidden(X3,X1)
% 1.52/0.99      | ~ v1_funct_1(X0)
% 1.52/0.99      | ~ v2_funct_1(X0)
% 1.52/0.99      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
% 1.52/0.99      | sK3 != X2
% 1.52/0.99      | sK3 != X1
% 1.52/0.99      | sK4 != X0
% 1.52/0.99      | k1_xboole_0 = X2 ),
% 1.52/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_278,plain,
% 1.52/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
% 1.52/0.99      | ~ r2_hidden(X0,sK3)
% 1.52/0.99      | ~ v1_funct_1(sK4)
% 1.52/0.99      | ~ v2_funct_1(sK4)
% 1.52/0.99      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0
% 1.52/0.99      | k1_xboole_0 = sK3 ),
% 1.52/0.99      inference(unflattening,[status(thm)],[c_277]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_282,plain,
% 1.52/0.99      ( ~ r2_hidden(X0,sK3)
% 1.52/0.99      | ~ v2_funct_1(sK4)
% 1.52/0.99      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0
% 1.52/0.99      | k1_xboole_0 = sK3 ),
% 1.52/0.99      inference(global_propositional_subsumption,
% 1.52/0.99                [status(thm)],
% 1.52/0.99                [c_278,c_23,c_21]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1926,plain,
% 1.52/0.99      ( ~ r2_hidden(X0_51,sK3)
% 1.52/0.99      | ~ v2_funct_1(sK4)
% 1.52/0.99      | k1_xboole_0 = sK3
% 1.52/0.99      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_51)) = X0_51 ),
% 1.52/0.99      inference(subtyping,[status(esa)],[c_282]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1937,plain,
% 1.52/0.99      ( ~ r2_hidden(X0_51,sK3)
% 1.52/0.99      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_51)) = X0_51
% 1.52/0.99      | ~ sP0_iProver_split ),
% 1.52/0.99      inference(splitting,
% 1.52/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.52/0.99                [c_1926]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2343,plain,
% 1.52/0.99      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_51)) = X0_51
% 1.52/0.99      | r2_hidden(X0_51,sK3) != iProver_top
% 1.52/0.99      | sP0_iProver_split != iProver_top ),
% 1.52/0.99      inference(predicate_to_equality,[status(thm)],[c_1937]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2647,plain,
% 1.52/0.99      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK5
% 1.52/0.99      | v2_funct_1(sK4) != iProver_top
% 1.52/0.99      | sP0_iProver_split != iProver_top ),
% 1.52/0.99      inference(superposition,[status(thm)],[c_2339,c_2343]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_30,plain,
% 1.52/0.99      ( r2_hidden(sK5,sK3) = iProver_top
% 1.52/0.99      | v2_funct_1(sK4) != iProver_top ),
% 1.52/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1943,plain,( X0_51 = X0_51 ),theory(equality) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1973,plain,
% 1.52/0.99      ( sK5 = sK5 ),
% 1.52/0.99      inference(instantiation,[status(thm)],[c_1943]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_0,plain,
% 1.52/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 1.52/0.99      inference(cnf_transformation,[],[f40]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_4,plain,
% 1.52/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 1.52/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_266,plain,
% 1.52/0.99      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 1.52/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_267,plain,
% 1.52/0.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 1.52/0.99      inference(unflattening,[status(thm)],[c_266]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1927,plain,
% 1.52/0.99      ( ~ r2_hidden(X0_51,k1_xboole_0) ),
% 1.52/0.99      inference(subtyping,[status(esa)],[c_267]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1991,plain,
% 1.52/0.99      ( r2_hidden(X0_51,k1_xboole_0) != iProver_top ),
% 1.52/0.99      inference(predicate_to_equality,[status(thm)],[c_1927]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1993,plain,
% 1.52/0.99      ( r2_hidden(sK5,k1_xboole_0) != iProver_top ),
% 1.52/0.99      inference(instantiation,[status(thm)],[c_1991]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1938,plain,
% 1.52/0.99      ( ~ v2_funct_1(sK4) | sP0_iProver_split | k1_xboole_0 = sK3 ),
% 1.52/0.99      inference(splitting,
% 1.52/0.99                [splitting(split),new_symbols(definition,[])],
% 1.52/0.99                [c_1926]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1994,plain,
% 1.52/0.99      ( k1_xboole_0 = sK3
% 1.52/0.99      | v2_funct_1(sK4) != iProver_top
% 1.52/0.99      | sP0_iProver_split = iProver_top ),
% 1.52/0.99      inference(predicate_to_equality,[status(thm)],[c_1938]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1995,plain,
% 1.52/0.99      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_51)) = X0_51
% 1.52/0.99      | r2_hidden(X0_51,sK3) != iProver_top
% 1.52/0.99      | sP0_iProver_split != iProver_top ),
% 1.52/0.99      inference(predicate_to_equality,[status(thm)],[c_1937]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1997,plain,
% 1.52/0.99      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK5
% 1.52/0.99      | r2_hidden(sK5,sK3) != iProver_top
% 1.52/0.99      | sP0_iProver_split != iProver_top ),
% 1.52/0.99      inference(instantiation,[status(thm)],[c_1995]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1949,plain,
% 1.52/0.99      ( ~ r2_hidden(X0_51,X0_52)
% 1.52/0.99      | r2_hidden(X1_51,X1_52)
% 1.52/0.99      | X1_52 != X0_52
% 1.52/0.99      | X1_51 != X0_51 ),
% 1.52/0.99      theory(equality) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2575,plain,
% 1.52/0.99      ( ~ r2_hidden(X0_51,X0_52)
% 1.52/0.99      | r2_hidden(X1_51,k1_xboole_0)
% 1.52/0.99      | k1_xboole_0 != X0_52
% 1.52/0.99      | X1_51 != X0_51 ),
% 1.52/0.99      inference(instantiation,[status(thm)],[c_1949]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2576,plain,
% 1.52/0.99      ( k1_xboole_0 != X0_52
% 1.52/0.99      | X0_51 != X1_51
% 1.52/0.99      | r2_hidden(X1_51,X0_52) != iProver_top
% 1.52/0.99      | r2_hidden(X0_51,k1_xboole_0) = iProver_top ),
% 1.52/0.99      inference(predicate_to_equality,[status(thm)],[c_2575]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2578,plain,
% 1.52/0.99      ( k1_xboole_0 != sK3
% 1.52/0.99      | sK5 != sK5
% 1.52/0.99      | r2_hidden(sK5,sK3) != iProver_top
% 1.52/0.99      | r2_hidden(sK5,k1_xboole_0) = iProver_top ),
% 1.52/0.99      inference(instantiation,[status(thm)],[c_2576]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2724,plain,
% 1.52/0.99      ( v2_funct_1(sK4) != iProver_top
% 1.52/0.99      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK5 ),
% 1.52/0.99      inference(global_propositional_subsumption,
% 1.52/0.99                [status(thm)],
% 1.52/0.99                [c_2647,c_30,c_1973,c_1993,c_1994,c_1997,c_2578]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2725,plain,
% 1.52/0.99      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK5
% 1.52/0.99      | v2_funct_1(sK4) != iProver_top ),
% 1.52/0.99      inference(renaming,[status(thm)],[c_2724]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_3329,plain,
% 1.52/0.99      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK5 ),
% 1.52/0.99      inference(superposition,[status(thm)],[c_3323,c_2725]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_18,negated_conjecture,
% 1.52/0.99      ( r2_hidden(sK6,sK3) | ~ v2_funct_1(sK4) ),
% 1.52/0.99      inference(cnf_transformation,[],[f61]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1930,negated_conjecture,
% 1.52/0.99      ( r2_hidden(sK6,sK3) | ~ v2_funct_1(sK4) ),
% 1.52/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2338,plain,
% 1.52/0.99      ( r2_hidden(sK6,sK3) = iProver_top
% 1.52/0.99      | v2_funct_1(sK4) != iProver_top ),
% 1.52/0.99      inference(predicate_to_equality,[status(thm)],[c_1930]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2646,plain,
% 1.52/0.99      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK6)) = sK6
% 1.52/0.99      | v2_funct_1(sK4) != iProver_top
% 1.52/0.99      | sP0_iProver_split != iProver_top ),
% 1.52/0.99      inference(superposition,[status(thm)],[c_2338,c_2343]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2717,plain,
% 1.52/0.99      ( v2_funct_1(sK4) != iProver_top
% 1.52/0.99      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK6)) = sK6 ),
% 1.52/0.99      inference(global_propositional_subsumption,
% 1.52/0.99                [status(thm)],
% 1.52/0.99                [c_2646,c_30,c_1973,c_1993,c_1994,c_2578]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2718,plain,
% 1.52/0.99      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK6)) = sK6
% 1.52/0.99      | v2_funct_1(sK4) != iProver_top ),
% 1.52/0.99      inference(renaming,[status(thm)],[c_2717]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_3330,plain,
% 1.52/0.99      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK6)) = sK6 ),
% 1.52/0.99      inference(superposition,[status(thm)],[c_3323,c_2718]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_3332,plain,
% 1.52/0.99      ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5) ),
% 1.52/0.99      inference(superposition,[status(thm)],[c_3323,c_2337]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_3339,plain,
% 1.52/0.99      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK6 ),
% 1.52/0.99      inference(light_normalisation,[status(thm)],[c_3330,c_3332]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_3343,plain,
% 1.52/0.99      ( sK6 = sK5 ),
% 1.52/0.99      inference(demodulation,[status(thm)],[c_3329,c_3339]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2560,plain,
% 1.52/0.99      ( sK6 != X0_51 | sK5 != X0_51 | sK5 = sK6 ),
% 1.52/0.99      inference(instantiation,[status(thm)],[c_1946]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_2561,plain,
% 1.52/0.99      ( sK6 != sK5 | sK5 = sK6 | sK5 != sK5 ),
% 1.52/0.99      inference(instantiation,[status(thm)],[c_2560]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_16,negated_conjecture,
% 1.52/0.99      ( ~ v2_funct_1(sK4) | sK5 != sK6 ),
% 1.52/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1932,negated_conjecture,
% 1.52/0.99      ( ~ v2_funct_1(sK4) | sK5 != sK6 ),
% 1.52/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(c_1986,plain,
% 1.52/0.99      ( sK5 != sK6 | v2_funct_1(sK4) != iProver_top ),
% 1.52/0.99      inference(predicate_to_equality,[status(thm)],[c_1932]) ).
% 1.52/0.99  
% 1.52/0.99  cnf(contradiction,plain,
% 1.52/0.99      ( $false ),
% 1.52/0.99      inference(minisat,
% 1.52/0.99                [status(thm)],
% 1.52/0.99                [c_3343,c_3323,c_2561,c_1986,c_1973]) ).
% 1.52/0.99  
% 1.52/0.99  
% 1.52/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.52/0.99  
% 1.52/0.99  ------                               Statistics
% 1.52/0.99  
% 1.52/0.99  ------ General
% 1.52/0.99  
% 1.52/0.99  abstr_ref_over_cycles:                  0
% 1.52/0.99  abstr_ref_under_cycles:                 0
% 1.52/0.99  gc_basic_clause_elim:                   0
% 1.52/0.99  forced_gc_time:                         0
% 1.52/0.99  parsing_time:                           0.007
% 1.52/0.99  unif_index_cands_time:                  0.
% 1.52/0.99  unif_index_add_time:                    0.
% 1.52/0.99  orderings_time:                         0.
% 1.52/0.99  out_proof_time:                         0.012
% 1.52/0.99  total_time:                             0.13
% 1.52/0.99  num_of_symbols:                         56
% 1.52/0.99  num_of_terms:                           1393
% 1.52/0.99  
% 1.52/0.99  ------ Preprocessing
% 1.52/0.99  
% 1.52/0.99  num_of_splits:                          2
% 1.52/0.99  num_of_split_atoms:                     2
% 1.52/0.99  num_of_reused_defs:                     0
% 1.52/0.99  num_eq_ax_congr_red:                    15
% 1.52/0.99  num_of_sem_filtered_clauses:            1
% 1.52/0.99  num_of_subtypes:                        4
% 1.52/0.99  monotx_restored_types:                  1
% 1.52/0.99  sat_num_of_epr_types:                   0
% 1.52/0.99  sat_num_of_non_cyclic_types:            0
% 1.52/0.99  sat_guarded_non_collapsed_types:        0
% 1.52/0.99  num_pure_diseq_elim:                    0
% 1.52/0.99  simp_replaced_by:                       0
% 1.52/0.99  res_preprocessed:                       119
% 1.52/0.99  prep_upred:                             0
% 1.52/0.99  prep_unflattend:                        17
% 1.52/0.99  smt_new_axioms:                         0
% 1.52/0.99  pred_elim_cands:                        4
% 1.52/0.99  pred_elim:                              5
% 1.52/0.99  pred_elim_cl:                           6
% 1.52/0.99  pred_elim_cycles:                       9
% 1.52/0.99  merged_defs:                            0
% 1.52/0.99  merged_defs_ncl:                        0
% 1.52/0.99  bin_hyper_res:                          0
% 1.52/0.99  prep_cycles:                            4
% 1.52/0.99  pred_elim_time:                         0.038
% 1.52/0.99  splitting_time:                         0.
% 1.52/0.99  sem_filter_time:                        0.
% 1.52/0.99  monotx_time:                            0.001
% 1.52/0.99  subtype_inf_time:                       0.001
% 1.52/0.99  
% 1.52/0.99  ------ Problem properties
% 1.52/0.99  
% 1.52/0.99  clauses:                                20
% 1.52/0.99  conjectures:                            5
% 1.52/0.99  epr:                                    7
% 1.52/0.99  horn:                                   14
% 1.52/0.99  ground:                                 10
% 1.52/0.99  unary:                                  2
% 1.52/0.99  binary:                                 6
% 1.52/0.99  lits:                                   54
% 1.52/0.99  lits_eq:                                12
% 1.52/0.99  fd_pure:                                0
% 1.52/0.99  fd_pseudo:                              0
% 1.52/0.99  fd_cond:                                0
% 1.52/0.99  fd_pseudo_cond:                         2
% 1.52/0.99  ac_symbols:                             0
% 1.52/0.99  
% 1.52/0.99  ------ Propositional Solver
% 1.52/0.99  
% 1.52/0.99  prop_solver_calls:                      28
% 1.52/0.99  prop_fast_solver_calls:                 1043
% 1.52/0.99  smt_solver_calls:                       0
% 1.52/0.99  smt_fast_solver_calls:                  0
% 1.52/0.99  prop_num_of_clauses:                    649
% 1.52/0.99  prop_preprocess_simplified:             3682
% 1.52/0.99  prop_fo_subsumed:                       20
% 1.52/0.99  prop_solver_time:                       0.
% 1.52/0.99  smt_solver_time:                        0.
% 1.52/0.99  smt_fast_solver_time:                   0.
% 1.52/0.99  prop_fast_solver_time:                  0.
% 1.52/0.99  prop_unsat_core_time:                   0.
% 1.52/0.99  
% 1.52/0.99  ------ QBF
% 1.52/0.99  
% 1.52/0.99  qbf_q_res:                              0
% 1.52/0.99  qbf_num_tautologies:                    0
% 1.52/0.99  qbf_prep_cycles:                        0
% 1.52/0.99  
% 1.52/0.99  ------ BMC1
% 1.52/0.99  
% 1.52/0.99  bmc1_current_bound:                     -1
% 1.52/0.99  bmc1_last_solved_bound:                 -1
% 1.52/0.99  bmc1_unsat_core_size:                   -1
% 1.52/0.99  bmc1_unsat_core_parents_size:           -1
% 1.52/0.99  bmc1_merge_next_fun:                    0
% 1.52/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.52/0.99  
% 1.52/0.99  ------ Instantiation
% 1.52/0.99  
% 1.52/0.99  inst_num_of_clauses:                    160
% 1.52/0.99  inst_num_in_passive:                    68
% 1.52/0.99  inst_num_in_active:                     92
% 1.52/0.99  inst_num_in_unprocessed:                0
% 1.52/0.99  inst_num_of_loops:                      150
% 1.52/0.99  inst_num_of_learning_restarts:          0
% 1.52/0.99  inst_num_moves_active_passive:          54
% 1.52/0.99  inst_lit_activity:                      0
% 1.52/0.99  inst_lit_activity_moves:                0
% 1.52/0.99  inst_num_tautologies:                   0
% 1.52/0.99  inst_num_prop_implied:                  0
% 1.52/0.99  inst_num_existing_simplified:           0
% 1.52/0.99  inst_num_eq_res_simplified:             0
% 1.52/0.99  inst_num_child_elim:                    0
% 1.52/0.99  inst_num_of_dismatching_blockings:      9
% 1.52/0.99  inst_num_of_non_proper_insts:           116
% 1.52/0.99  inst_num_of_duplicates:                 0
% 1.52/0.99  inst_inst_num_from_inst_to_res:         0
% 1.52/0.99  inst_dismatching_checking_time:         0.
% 1.52/0.99  
% 1.52/0.99  ------ Resolution
% 1.52/0.99  
% 1.52/0.99  res_num_of_clauses:                     0
% 1.52/0.99  res_num_in_passive:                     0
% 1.52/0.99  res_num_in_active:                      0
% 1.52/0.99  res_num_of_loops:                       123
% 1.52/0.99  res_forward_subset_subsumed:            14
% 1.52/0.99  res_backward_subset_subsumed:           0
% 1.52/0.99  res_forward_subsumed:                   0
% 1.52/0.99  res_backward_subsumed:                  0
% 1.52/0.99  res_forward_subsumption_resolution:     0
% 1.52/0.99  res_backward_subsumption_resolution:    0
% 1.52/0.99  res_clause_to_clause_subsumption:       79
% 1.52/0.99  res_orphan_elimination:                 0
% 1.52/0.99  res_tautology_del:                      15
% 1.52/0.99  res_num_eq_res_simplified:              0
% 1.52/0.99  res_num_sel_changes:                    0
% 1.52/0.99  res_moves_from_active_to_pass:          0
% 1.52/0.99  
% 1.52/0.99  ------ Superposition
% 1.52/0.99  
% 1.52/0.99  sup_time_total:                         0.
% 1.52/0.99  sup_time_generating:                    0.
% 1.52/0.99  sup_time_sim_full:                      0.
% 1.52/0.99  sup_time_sim_immed:                     0.
% 1.52/0.99  
% 1.52/0.99  sup_num_of_clauses:                     44
% 1.52/0.99  sup_num_in_active:                      28
% 1.52/0.99  sup_num_in_passive:                     16
% 1.52/0.99  sup_num_of_loops:                       28
% 1.52/0.99  sup_fw_superposition:                   7
% 1.52/0.99  sup_bw_superposition:                   24
% 1.52/0.99  sup_immediate_simplified:               6
% 1.52/0.99  sup_given_eliminated:                   0
% 1.52/0.99  comparisons_done:                       0
% 1.52/0.99  comparisons_avoided:                    3
% 1.52/0.99  
% 1.52/0.99  ------ Simplifications
% 1.52/0.99  
% 1.52/0.99  
% 1.52/0.99  sim_fw_subset_subsumed:                 1
% 1.52/0.99  sim_bw_subset_subsumed:                 2
% 1.52/0.99  sim_fw_subsumed:                        2
% 1.52/0.99  sim_bw_subsumed:                        0
% 1.52/0.99  sim_fw_subsumption_res:                 0
% 1.52/0.99  sim_bw_subsumption_res:                 0
% 1.52/0.99  sim_tautology_del:                      1
% 1.52/0.99  sim_eq_tautology_del:                   2
% 1.52/0.99  sim_eq_res_simp:                        0
% 1.52/0.99  sim_fw_demodulated:                     0
% 1.52/0.99  sim_bw_demodulated:                     2
% 1.52/0.99  sim_light_normalised:                   1
% 1.52/0.99  sim_joinable_taut:                      0
% 1.52/0.99  sim_joinable_simp:                      0
% 1.52/0.99  sim_ac_normalised:                      0
% 1.52/0.99  sim_smt_subsumption:                    0
% 1.52/0.99  
%------------------------------------------------------------------------------
