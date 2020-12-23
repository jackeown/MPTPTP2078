%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:55 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_35)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
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

fof(f20,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f20])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f33])).

fof(f56,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

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
    inference(nnf_transformation,[],[f26])).

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
    inference(flattening,[],[f35])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f39,plain,(
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

fof(f38,plain,
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

fof(f40,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f37,f39,f38])).

fof(f60,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f66,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f53,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK1(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | sK0(X0) != sK1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK0(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK2)
      | v2_funct_1(sK3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f23])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f67,plain,
    ( sK4 != sK5
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_427,plain,
    ( v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_26])).

cnf(c_428,plain,
    ( v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_2530,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_428])).

cnf(c_27,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_29,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_52,plain,
    ( k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_54,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2795,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2861,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | r1_tarski(sK3,k2_zfmisc_1(sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_2795])).

cnf(c_2862,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(sK2,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2861])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_204,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_205,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_204])).

cnf(c_261,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_205])).

cnf(c_2766,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_261])).

cnf(c_2965,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK2,sK2))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK2))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2766])).

cnf(c_2966,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK2,sK2)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK2,sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2965])).

cnf(c_11,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3291,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3292,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3291])).

cnf(c_3595,plain,
    ( v2_funct_1(sK3) = iProver_top
    | k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2530,c_27,c_29,c_54,c_2862,c_2966,c_3292])).

cnf(c_3596,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3595])).

cnf(c_20,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2542,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3605,plain,
    ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_3596,c_2542])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_453,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | X2 = X0
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_454,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_1932,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_454])).

cnf(c_2528,plain,
    ( X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1932])).

cnf(c_3853,plain,
    ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
    | sK1(sK3) = X0
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK1(sK3),k1_relat_1(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3605,c_2528])).

cnf(c_14,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_414,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_415,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_749,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_415,c_20])).

cnf(c_750,plain,
    ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
    | r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_749])).

cnf(c_4371,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | sK1(sK3) = X0
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
    | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
    | sP0_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3853,c_29,c_750,c_2862,c_2966,c_3292])).

cnf(c_4372,plain,
    ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
    | sK1(sK3) = X0
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(renaming,[status(thm)],[c_4371])).

cnf(c_4383,plain,
    ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
    | sK1(sK3) = sK0(sK3)
    | r2_hidden(sK0(sK3),k1_relat_1(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4372])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK1(X0) != sK0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_440,plain,
    ( v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK1(X0) != sK0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_26])).

cnf(c_441,plain,
    ( v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK1(sK3) != sK0(sK3) ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_567,plain,
    ( ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
    | sK1(sK3) != sK0(sK3) ),
    inference(resolution,[status(thm)],[c_441,c_20])).

cnf(c_15,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_401,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_402,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_401])).

cnf(c_840,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_402,c_20])).

cnf(c_1933,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_454])).

cnf(c_17,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_382,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_17,c_10])).

cnf(c_3816,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | r1_tarski(k1_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_382])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(X1,sK2)
    | v2_funct_1(sK3)
    | X1 = X0
    | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2539,plain,
    ( X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
    | r2_hidden(X1,sK2) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3854,plain,
    ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
    | sK1(sK3) = X0
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(sK1(sK3),sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3605,c_2539])).

cnf(c_3893,plain,
    ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
    | sK1(sK3) = sK0(sK3)
    | r2_hidden(sK1(sK3),sK2) != iProver_top
    | r2_hidden(sK0(sK3),sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3854])).

cnf(c_55,plain,
    ( sK1(X0) != sK0(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_57,plain,
    ( sK1(sK3) != sK0(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_55])).

cnf(c_3589,plain,
    ( ~ r2_hidden(sK1(sK3),sK2)
    | ~ r2_hidden(sK0(sK3),sK2)
    | v2_funct_1(sK3)
    | k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
    | sK1(sK3) = sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_3590,plain,
    ( k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
    | sK1(sK3) = sK0(sK3)
    | r2_hidden(sK1(sK3),sK2) != iProver_top
    | r2_hidden(sK0(sK3),sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3589])).

cnf(c_4363,plain,
    ( r2_hidden(sK1(sK3),sK2) != iProver_top
    | r2_hidden(sK0(sK3),sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3893,c_27,c_29,c_54,c_57,c_2862,c_2966,c_3292,c_3590])).

cnf(c_4365,plain,
    ( ~ r2_hidden(sK1(sK3),sK2)
    | ~ r2_hidden(sK0(sK3),sK2)
    | v2_funct_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4363])).

cnf(c_4392,plain,
    ( ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ sP0_iProver_split
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
    | sK1(sK3) = sK0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4383])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_258,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_205])).

cnf(c_3557,plain,
    ( r2_hidden(sK0(sK3),X0)
    | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ r1_tarski(k1_relat_1(sK3),X0) ),
    inference(instantiation,[status(thm)],[c_258])).

cnf(c_4422,plain,
    ( ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | r2_hidden(sK0(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_3557])).

cnf(c_3572,plain,
    ( r2_hidden(sK1(sK3),X0)
    | ~ r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | ~ r1_tarski(k1_relat_1(sK3),X0) ),
    inference(instantiation,[status(thm)],[c_258])).

cnf(c_4437,plain,
    ( ~ r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | r2_hidden(sK1(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_3572])).

cnf(c_4628,plain,
    ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4383,c_24,c_567,c_749,c_840,c_1933,c_2861,c_2965,c_3291,c_3816,c_4365,c_4392,c_4422,c_4437])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_353,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
    | sK2 != X2
    | sK2 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_354,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ r2_hidden(X0,sK2)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_358,plain,
    ( ~ r2_hidden(X0,sK2)
    | ~ v2_funct_1(sK3)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_354,c_26,c_24])).

cnf(c_1935,plain,
    ( ~ v2_funct_1(sK3)
    | sP1_iProver_split
    | k1_xboole_0 = sK2 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_358])).

cnf(c_2534,plain,
    ( k1_xboole_0 = sK2
    | v2_funct_1(sK3) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1935])).

cnf(c_3601,plain,
    ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sK2 = k1_xboole_0
    | sP1_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_3596,c_2534])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2541,plain,
    ( r2_hidden(sK5,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1934,plain,
    ( ~ r2_hidden(X0,sK2)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_358])).

cnf(c_2535,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | r2_hidden(X0,sK2) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1934])).

cnf(c_3215,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
    | v2_funct_1(sK3) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2541,c_2535])).

cnf(c_3603,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3596,c_3215])).

cnf(c_4311,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3601,c_3603])).

cnf(c_4631,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4628,c_4311])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_82,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_86,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_19,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | sK4 != sK5 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_579,plain,
    ( ~ v1_relat_1(sK3)
    | sK1(sK3) != sK0(sK3)
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_441,c_19])).

cnf(c_670,plain,
    ( ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_428,c_19])).

cnf(c_761,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_415,c_19])).

cnf(c_852,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_402,c_19])).

cnf(c_1948,plain,
    ( X0 != X1
    | sK1(X0) = sK1(X1) ),
    theory(equality)).

cnf(c_1960,plain,
    ( sK1(sK3) = sK1(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1948])).

cnf(c_1938,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3592,plain,
    ( sK1(sK3) != X0
    | sK1(sK3) = sK0(sK3)
    | sK0(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_1938])).

cnf(c_4485,plain,
    ( sK1(sK3) != sK1(sK3)
    | sK1(sK3) = sK0(sK3)
    | sK0(sK3) != sK1(sK3) ),
    inference(instantiation,[status(thm)],[c_3592])).

cnf(c_4660,plain,
    ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4)
    | sK5 = X0
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(sK5,sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4628,c_2539])).

cnf(c_46,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_48,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_49,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_51,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_49])).

cnf(c_3817,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3816])).

cnf(c_4423,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK0(sK3),sK2) = iProver_top
    | r1_tarski(k1_relat_1(sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4422])).

cnf(c_4438,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK1(sK3),sK2) = iProver_top
    | r1_tarski(k1_relat_1(sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4437])).

cnf(c_4688,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4660,c_27,c_29,c_48,c_51,c_54,c_57,c_2862,c_2966,c_3292,c_3590,c_3817,c_4423,c_4438])).

cnf(c_4690,plain,
    ( v2_funct_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4688])).

cnf(c_5457,plain,
    ( ~ r2_hidden(sK1(X0),k1_relat_1(sK3))
    | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ sP0_iProver_split
    | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(X0))
    | sK0(sK3) = sK1(X0) ),
    inference(instantiation,[status(thm)],[c_1932])).

cnf(c_5464,plain,
    ( ~ r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ sP0_iProver_split
    | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(sK3))
    | sK0(sK3) = sK1(sK3) ),
    inference(instantiation,[status(thm)],[c_5457])).

cnf(c_4693,plain,
    ( sK2 = k1_xboole_0
    | sP1_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_4688,c_2534])).

cnf(c_2549,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2537,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_258])).

cnf(c_4840,plain,
    ( r2_hidden(sK5,X0) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2541,c_2537])).

cnf(c_5153,plain,
    ( r1_tarski(sK2,X0) != iProver_top
    | r2_hidden(sK5,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4840,c_27,c_29,c_48,c_51,c_54,c_57,c_2862,c_2966,c_3292,c_3590,c_3817,c_4423,c_4438])).

cnf(c_5154,plain,
    ( r2_hidden(sK5,X0) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5153])).

cnf(c_5161,plain,
    ( r2_hidden(sK5,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2549,c_5154])).

cnf(c_5166,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_5161,c_2535])).

cnf(c_5169,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
    | sP1_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5166,c_4628])).

cnf(c_6060,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4693,c_5169])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2540,plain,
    ( r2_hidden(sK4,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3216,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | v2_funct_1(sK3) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2540,c_2535])).

cnf(c_4694,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_4688,c_3216])).

cnf(c_5485,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4693,c_4694])).

cnf(c_6172,plain,
    ( sK2 = k1_xboole_0
    | sK5 = sK4 ),
    inference(superposition,[status(thm)],[c_6060,c_5485])).

cnf(c_6297,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4631,c_24,c_82,c_86,c_579,c_670,c_761,c_852,c_1960,c_1933,c_2861,c_2965,c_3291,c_4485,c_4690,c_5464,c_6172])).

cnf(c_2538,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2533,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_382])).

cnf(c_4189,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2538,c_2533])).

cnf(c_4205,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4189,c_29,c_2862,c_2966,c_3292,c_3817])).

cnf(c_6310,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6297,c_4205])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2548,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2550,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3698,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2548,c_2550])).

cnf(c_6691,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6310,c_3698])).

cnf(c_4659,plain,
    ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4)
    | sK5 = X0
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_4628,c_2528])).

cnf(c_1965,plain,
    ( v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1933])).

cnf(c_5394,plain,
    ( r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | sK5 = X0
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4659,c_27,c_29,c_48,c_51,c_54,c_57,c_1965,c_2862,c_2966,c_3292,c_3590,c_3817,c_4423,c_4438])).

cnf(c_5395,plain,
    ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4)
    | sK5 = X0
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5394])).

cnf(c_5406,plain,
    ( sK5 = sK4
    | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5395])).

cnf(c_6067,plain,
    ( r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5406,c_27,c_29,c_35,c_36,c_48,c_51,c_54,c_57,c_1965,c_2862,c_2966,c_3292,c_3590,c_3817,c_4423,c_4438,c_5179])).

cnf(c_7154,plain,
    ( r2_hidden(sK5,k1_xboole_0) != iProver_top
    | r2_hidden(sK4,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6691,c_6067])).

cnf(c_6306,plain,
    ( r2_hidden(sK5,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6297,c_5161])).

cnf(c_4841,plain,
    ( r2_hidden(sK4,X0) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2540,c_2537])).

cnf(c_5266,plain,
    ( r1_tarski(sK2,X0) != iProver_top
    | r2_hidden(sK4,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4841,c_27,c_29,c_48,c_51,c_54,c_57,c_2862,c_2966,c_3292,c_3590,c_3817,c_4423,c_4438])).

cnf(c_5267,plain,
    ( r2_hidden(sK4,X0) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5266])).

cnf(c_5274,plain,
    ( r2_hidden(sK4,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2549,c_5267])).

cnf(c_6304,plain,
    ( r2_hidden(sK4,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6297,c_5274])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7154,c_6306,c_6304])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:19:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.86/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/0.98  
% 2.86/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.86/0.98  
% 2.86/0.98  ------  iProver source info
% 2.86/0.98  
% 2.86/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.86/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.86/0.98  git: non_committed_changes: false
% 2.86/0.98  git: last_make_outside_of_git: false
% 2.86/0.98  
% 2.86/0.98  ------ 
% 2.86/0.98  
% 2.86/0.98  ------ Input Options
% 2.86/0.98  
% 2.86/0.98  --out_options                           all
% 2.86/0.98  --tptp_safe_out                         true
% 2.86/0.98  --problem_path                          ""
% 2.86/0.98  --include_path                          ""
% 2.86/0.98  --clausifier                            res/vclausify_rel
% 2.86/0.98  --clausifier_options                    --mode clausify
% 2.86/0.98  --stdin                                 false
% 2.86/0.98  --stats_out                             all
% 2.86/0.98  
% 2.86/0.98  ------ General Options
% 2.86/0.98  
% 2.86/0.98  --fof                                   false
% 2.86/0.98  --time_out_real                         305.
% 2.86/0.98  --time_out_virtual                      -1.
% 2.86/0.98  --symbol_type_check                     false
% 2.86/0.98  --clausify_out                          false
% 2.86/0.98  --sig_cnt_out                           false
% 2.86/0.98  --trig_cnt_out                          false
% 2.86/0.98  --trig_cnt_out_tolerance                1.
% 2.86/0.98  --trig_cnt_out_sk_spl                   false
% 2.86/0.98  --abstr_cl_out                          false
% 2.86/0.98  
% 2.86/0.98  ------ Global Options
% 2.86/0.98  
% 2.86/0.98  --schedule                              default
% 2.86/0.98  --add_important_lit                     false
% 2.86/0.98  --prop_solver_per_cl                    1000
% 2.86/0.98  --min_unsat_core                        false
% 2.86/0.98  --soft_assumptions                      false
% 2.86/0.98  --soft_lemma_size                       3
% 2.86/0.98  --prop_impl_unit_size                   0
% 2.86/0.98  --prop_impl_unit                        []
% 2.86/0.98  --share_sel_clauses                     true
% 2.86/0.98  --reset_solvers                         false
% 2.86/0.98  --bc_imp_inh                            [conj_cone]
% 2.86/0.98  --conj_cone_tolerance                   3.
% 2.86/0.98  --extra_neg_conj                        none
% 2.86/0.98  --large_theory_mode                     true
% 2.86/0.98  --prolific_symb_bound                   200
% 2.86/0.98  --lt_threshold                          2000
% 2.86/0.98  --clause_weak_htbl                      true
% 2.86/0.98  --gc_record_bc_elim                     false
% 2.86/0.98  
% 2.86/0.98  ------ Preprocessing Options
% 2.86/0.98  
% 2.86/0.98  --preprocessing_flag                    true
% 2.86/0.98  --time_out_prep_mult                    0.1
% 2.86/0.98  --splitting_mode                        input
% 2.86/0.98  --splitting_grd                         true
% 2.86/0.98  --splitting_cvd                         false
% 2.86/0.98  --splitting_cvd_svl                     false
% 2.86/0.98  --splitting_nvd                         32
% 2.86/0.98  --sub_typing                            true
% 2.86/0.98  --prep_gs_sim                           true
% 2.86/0.98  --prep_unflatten                        true
% 2.86/0.98  --prep_res_sim                          true
% 2.86/0.98  --prep_upred                            true
% 2.86/0.98  --prep_sem_filter                       exhaustive
% 2.86/0.98  --prep_sem_filter_out                   false
% 2.86/0.98  --pred_elim                             true
% 2.86/0.98  --res_sim_input                         true
% 2.86/0.98  --eq_ax_congr_red                       true
% 2.86/0.98  --pure_diseq_elim                       true
% 2.86/0.98  --brand_transform                       false
% 2.86/0.98  --non_eq_to_eq                          false
% 2.86/0.98  --prep_def_merge                        true
% 2.86/0.98  --prep_def_merge_prop_impl              false
% 2.86/0.98  --prep_def_merge_mbd                    true
% 2.86/0.98  --prep_def_merge_tr_red                 false
% 2.86/0.98  --prep_def_merge_tr_cl                  false
% 2.86/0.98  --smt_preprocessing                     true
% 2.86/0.98  --smt_ac_axioms                         fast
% 2.86/0.98  --preprocessed_out                      false
% 2.86/0.98  --preprocessed_stats                    false
% 2.86/0.98  
% 2.86/0.98  ------ Abstraction refinement Options
% 2.86/0.98  
% 2.86/0.98  --abstr_ref                             []
% 2.86/0.98  --abstr_ref_prep                        false
% 2.86/0.98  --abstr_ref_until_sat                   false
% 2.86/0.98  --abstr_ref_sig_restrict                funpre
% 2.86/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.86/0.98  --abstr_ref_under                       []
% 2.86/0.98  
% 2.86/0.98  ------ SAT Options
% 2.86/0.98  
% 2.86/0.98  --sat_mode                              false
% 2.86/0.98  --sat_fm_restart_options                ""
% 2.86/0.98  --sat_gr_def                            false
% 2.86/0.98  --sat_epr_types                         true
% 2.86/0.98  --sat_non_cyclic_types                  false
% 2.86/0.98  --sat_finite_models                     false
% 2.86/0.98  --sat_fm_lemmas                         false
% 2.86/0.98  --sat_fm_prep                           false
% 2.86/0.98  --sat_fm_uc_incr                        true
% 2.86/0.98  --sat_out_model                         small
% 2.86/0.98  --sat_out_clauses                       false
% 2.86/0.98  
% 2.86/0.98  ------ QBF Options
% 2.86/0.98  
% 2.86/0.98  --qbf_mode                              false
% 2.86/0.98  --qbf_elim_univ                         false
% 2.86/0.98  --qbf_dom_inst                          none
% 2.86/0.98  --qbf_dom_pre_inst                      false
% 2.86/0.98  --qbf_sk_in                             false
% 2.86/0.98  --qbf_pred_elim                         true
% 2.86/0.98  --qbf_split                             512
% 2.86/0.98  
% 2.86/0.98  ------ BMC1 Options
% 2.86/0.98  
% 2.86/0.98  --bmc1_incremental                      false
% 2.86/0.98  --bmc1_axioms                           reachable_all
% 2.86/0.98  --bmc1_min_bound                        0
% 2.86/0.98  --bmc1_max_bound                        -1
% 2.86/0.98  --bmc1_max_bound_default                -1
% 2.86/0.98  --bmc1_symbol_reachability              true
% 2.86/0.98  --bmc1_property_lemmas                  false
% 2.86/0.98  --bmc1_k_induction                      false
% 2.86/0.98  --bmc1_non_equiv_states                 false
% 2.86/0.98  --bmc1_deadlock                         false
% 2.86/0.98  --bmc1_ucm                              false
% 2.86/0.98  --bmc1_add_unsat_core                   none
% 2.86/0.98  --bmc1_unsat_core_children              false
% 2.86/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.86/0.98  --bmc1_out_stat                         full
% 2.86/0.98  --bmc1_ground_init                      false
% 2.86/0.98  --bmc1_pre_inst_next_state              false
% 2.86/0.98  --bmc1_pre_inst_state                   false
% 2.86/0.98  --bmc1_pre_inst_reach_state             false
% 2.86/0.98  --bmc1_out_unsat_core                   false
% 2.86/0.98  --bmc1_aig_witness_out                  false
% 2.86/0.98  --bmc1_verbose                          false
% 2.86/0.98  --bmc1_dump_clauses_tptp                false
% 2.86/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.86/0.98  --bmc1_dump_file                        -
% 2.86/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.86/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.86/0.98  --bmc1_ucm_extend_mode                  1
% 2.86/0.98  --bmc1_ucm_init_mode                    2
% 2.86/0.98  --bmc1_ucm_cone_mode                    none
% 2.86/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.86/0.98  --bmc1_ucm_relax_model                  4
% 2.86/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.86/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.86/0.98  --bmc1_ucm_layered_model                none
% 2.86/0.98  --bmc1_ucm_max_lemma_size               10
% 2.86/0.98  
% 2.86/0.98  ------ AIG Options
% 2.86/0.98  
% 2.86/0.98  --aig_mode                              false
% 2.86/0.98  
% 2.86/0.98  ------ Instantiation Options
% 2.86/0.98  
% 2.86/0.98  --instantiation_flag                    true
% 2.86/0.98  --inst_sos_flag                         false
% 2.86/0.98  --inst_sos_phase                        true
% 2.86/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.86/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.86/0.98  --inst_lit_sel_side                     num_symb
% 2.86/0.98  --inst_solver_per_active                1400
% 2.86/0.98  --inst_solver_calls_frac                1.
% 2.86/0.98  --inst_passive_queue_type               priority_queues
% 2.86/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.86/0.98  --inst_passive_queues_freq              [25;2]
% 2.86/0.98  --inst_dismatching                      true
% 2.86/0.98  --inst_eager_unprocessed_to_passive     true
% 2.86/0.98  --inst_prop_sim_given                   true
% 2.86/0.98  --inst_prop_sim_new                     false
% 2.86/0.98  --inst_subs_new                         false
% 2.86/0.98  --inst_eq_res_simp                      false
% 2.86/0.98  --inst_subs_given                       false
% 2.86/0.98  --inst_orphan_elimination               true
% 2.86/0.98  --inst_learning_loop_flag               true
% 2.86/0.98  --inst_learning_start                   3000
% 2.86/0.98  --inst_learning_factor                  2
% 2.86/0.98  --inst_start_prop_sim_after_learn       3
% 2.86/0.98  --inst_sel_renew                        solver
% 2.86/0.98  --inst_lit_activity_flag                true
% 2.86/0.98  --inst_restr_to_given                   false
% 2.86/0.98  --inst_activity_threshold               500
% 2.86/0.98  --inst_out_proof                        true
% 2.86/0.98  
% 2.86/0.98  ------ Resolution Options
% 2.86/0.98  
% 2.86/0.98  --resolution_flag                       true
% 2.86/0.98  --res_lit_sel                           adaptive
% 2.86/0.98  --res_lit_sel_side                      none
% 2.86/0.98  --res_ordering                          kbo
% 2.86/0.98  --res_to_prop_solver                    active
% 2.86/0.98  --res_prop_simpl_new                    false
% 2.86/0.98  --res_prop_simpl_given                  true
% 2.86/0.98  --res_passive_queue_type                priority_queues
% 2.86/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.86/0.98  --res_passive_queues_freq               [15;5]
% 2.86/0.98  --res_forward_subs                      full
% 2.86/0.98  --res_backward_subs                     full
% 2.86/0.98  --res_forward_subs_resolution           true
% 2.86/0.98  --res_backward_subs_resolution          true
% 2.86/0.98  --res_orphan_elimination                true
% 2.86/0.98  --res_time_limit                        2.
% 2.86/0.98  --res_out_proof                         true
% 2.86/0.98  
% 2.86/0.98  ------ Superposition Options
% 2.86/0.98  
% 2.86/0.98  --superposition_flag                    true
% 2.86/0.98  --sup_passive_queue_type                priority_queues
% 2.86/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.86/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.86/0.98  --demod_completeness_check              fast
% 2.86/0.98  --demod_use_ground                      true
% 2.86/0.98  --sup_to_prop_solver                    passive
% 2.86/0.98  --sup_prop_simpl_new                    true
% 2.86/0.98  --sup_prop_simpl_given                  true
% 2.86/0.98  --sup_fun_splitting                     false
% 2.86/0.98  --sup_smt_interval                      50000
% 2.86/0.98  
% 2.86/0.98  ------ Superposition Simplification Setup
% 2.86/0.98  
% 2.86/0.98  --sup_indices_passive                   []
% 2.86/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.86/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/0.98  --sup_full_bw                           [BwDemod]
% 2.86/0.98  --sup_immed_triv                        [TrivRules]
% 2.86/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.86/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/0.98  --sup_immed_bw_main                     []
% 2.86/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.86/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.86/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.86/0.98  
% 2.86/0.98  ------ Combination Options
% 2.86/0.98  
% 2.86/0.98  --comb_res_mult                         3
% 2.86/0.98  --comb_sup_mult                         2
% 2.86/0.98  --comb_inst_mult                        10
% 2.86/0.98  
% 2.86/0.98  ------ Debug Options
% 2.86/0.98  
% 2.86/0.98  --dbg_backtrace                         false
% 2.86/0.98  --dbg_dump_prop_clauses                 false
% 2.86/0.98  --dbg_dump_prop_clauses_file            -
% 2.86/0.98  --dbg_out_stat                          false
% 2.86/0.98  ------ Parsing...
% 2.86/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.86/0.98  
% 2.86/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.86/0.98  
% 2.86/0.98  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.86/0.98  
% 2.86/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.86/0.98  ------ Proving...
% 2.86/0.98  ------ Problem Properties 
% 2.86/0.98  
% 2.86/0.98  
% 2.86/0.98  clauses                                 24
% 2.86/0.98  conjectures                             6
% 2.86/0.98  EPR                                     10
% 2.86/0.98  Horn                                    19
% 2.86/0.98  unary                                   4
% 2.86/0.98  binary                                  6
% 2.86/0.98  lits                                    62
% 2.86/0.98  lits eq                                 11
% 2.86/0.98  fd_pure                                 0
% 2.86/0.98  fd_pseudo                               0
% 2.86/0.98  fd_cond                                 0
% 2.86/0.98  fd_pseudo_cond                          3
% 2.86/0.98  AC symbols                              0
% 2.86/0.98  
% 2.86/0.98  ------ Schedule dynamic 5 is on 
% 2.86/0.98  
% 2.86/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.86/0.98  
% 2.86/0.98  
% 2.86/0.98  ------ 
% 2.86/0.98  Current options:
% 2.86/0.98  ------ 
% 2.86/0.98  
% 2.86/0.98  ------ Input Options
% 2.86/0.98  
% 2.86/0.98  --out_options                           all
% 2.86/0.98  --tptp_safe_out                         true
% 2.86/0.98  --problem_path                          ""
% 2.86/0.98  --include_path                          ""
% 2.86/0.98  --clausifier                            res/vclausify_rel
% 2.86/0.98  --clausifier_options                    --mode clausify
% 2.86/0.98  --stdin                                 false
% 2.86/0.98  --stats_out                             all
% 2.86/0.98  
% 2.86/0.98  ------ General Options
% 2.86/0.98  
% 2.86/0.98  --fof                                   false
% 2.86/0.98  --time_out_real                         305.
% 2.86/0.98  --time_out_virtual                      -1.
% 2.86/0.98  --symbol_type_check                     false
% 2.86/0.98  --clausify_out                          false
% 2.86/0.98  --sig_cnt_out                           false
% 2.86/0.98  --trig_cnt_out                          false
% 2.86/0.98  --trig_cnt_out_tolerance                1.
% 2.86/0.98  --trig_cnt_out_sk_spl                   false
% 2.86/0.98  --abstr_cl_out                          false
% 2.86/0.98  
% 2.86/0.98  ------ Global Options
% 2.86/0.98  
% 2.86/0.98  --schedule                              default
% 2.86/0.98  --add_important_lit                     false
% 2.86/0.98  --prop_solver_per_cl                    1000
% 2.86/0.98  --min_unsat_core                        false
% 2.86/0.98  --soft_assumptions                      false
% 2.86/0.98  --soft_lemma_size                       3
% 2.86/0.98  --prop_impl_unit_size                   0
% 2.86/0.98  --prop_impl_unit                        []
% 2.86/0.98  --share_sel_clauses                     true
% 2.86/0.98  --reset_solvers                         false
% 2.86/0.98  --bc_imp_inh                            [conj_cone]
% 2.86/0.98  --conj_cone_tolerance                   3.
% 2.86/0.98  --extra_neg_conj                        none
% 2.86/0.98  --large_theory_mode                     true
% 2.86/0.98  --prolific_symb_bound                   200
% 2.86/0.98  --lt_threshold                          2000
% 2.86/0.98  --clause_weak_htbl                      true
% 2.86/0.98  --gc_record_bc_elim                     false
% 2.86/0.98  
% 2.86/0.98  ------ Preprocessing Options
% 2.86/0.98  
% 2.86/0.98  --preprocessing_flag                    true
% 2.86/0.98  --time_out_prep_mult                    0.1
% 2.86/0.98  --splitting_mode                        input
% 2.86/0.98  --splitting_grd                         true
% 2.86/0.98  --splitting_cvd                         false
% 2.86/0.98  --splitting_cvd_svl                     false
% 2.86/0.98  --splitting_nvd                         32
% 2.86/0.98  --sub_typing                            true
% 2.86/0.98  --prep_gs_sim                           true
% 2.86/0.98  --prep_unflatten                        true
% 2.86/0.98  --prep_res_sim                          true
% 2.86/0.98  --prep_upred                            true
% 2.86/0.98  --prep_sem_filter                       exhaustive
% 2.86/0.98  --prep_sem_filter_out                   false
% 2.86/0.98  --pred_elim                             true
% 2.86/0.98  --res_sim_input                         true
% 2.86/0.98  --eq_ax_congr_red                       true
% 2.86/0.98  --pure_diseq_elim                       true
% 2.86/0.98  --brand_transform                       false
% 2.86/0.98  --non_eq_to_eq                          false
% 2.86/0.98  --prep_def_merge                        true
% 2.86/0.98  --prep_def_merge_prop_impl              false
% 2.86/0.98  --prep_def_merge_mbd                    true
% 2.86/0.98  --prep_def_merge_tr_red                 false
% 2.86/0.98  --prep_def_merge_tr_cl                  false
% 2.86/0.98  --smt_preprocessing                     true
% 2.86/0.98  --smt_ac_axioms                         fast
% 2.86/0.98  --preprocessed_out                      false
% 2.86/0.98  --preprocessed_stats                    false
% 2.86/0.98  
% 2.86/0.98  ------ Abstraction refinement Options
% 2.86/0.98  
% 2.86/0.98  --abstr_ref                             []
% 2.86/0.98  --abstr_ref_prep                        false
% 2.86/0.98  --abstr_ref_until_sat                   false
% 2.86/0.98  --abstr_ref_sig_restrict                funpre
% 2.86/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.86/0.98  --abstr_ref_under                       []
% 2.86/0.98  
% 2.86/0.98  ------ SAT Options
% 2.86/0.98  
% 2.86/0.98  --sat_mode                              false
% 2.86/0.98  --sat_fm_restart_options                ""
% 2.86/0.98  --sat_gr_def                            false
% 2.86/0.98  --sat_epr_types                         true
% 2.86/0.98  --sat_non_cyclic_types                  false
% 2.86/0.98  --sat_finite_models                     false
% 2.86/0.98  --sat_fm_lemmas                         false
% 2.86/0.98  --sat_fm_prep                           false
% 2.86/0.98  --sat_fm_uc_incr                        true
% 2.86/0.98  --sat_out_model                         small
% 2.86/0.98  --sat_out_clauses                       false
% 2.86/0.98  
% 2.86/0.98  ------ QBF Options
% 2.86/0.98  
% 2.86/0.98  --qbf_mode                              false
% 2.86/0.98  --qbf_elim_univ                         false
% 2.86/0.98  --qbf_dom_inst                          none
% 2.86/0.98  --qbf_dom_pre_inst                      false
% 2.86/0.98  --qbf_sk_in                             false
% 2.86/0.98  --qbf_pred_elim                         true
% 2.86/0.98  --qbf_split                             512
% 2.86/0.98  
% 2.86/0.98  ------ BMC1 Options
% 2.86/0.98  
% 2.86/0.98  --bmc1_incremental                      false
% 2.86/0.98  --bmc1_axioms                           reachable_all
% 2.86/0.98  --bmc1_min_bound                        0
% 2.86/0.98  --bmc1_max_bound                        -1
% 2.86/0.98  --bmc1_max_bound_default                -1
% 2.86/0.98  --bmc1_symbol_reachability              true
% 2.86/0.98  --bmc1_property_lemmas                  false
% 2.86/0.98  --bmc1_k_induction                      false
% 2.86/0.98  --bmc1_non_equiv_states                 false
% 2.86/0.98  --bmc1_deadlock                         false
% 2.86/0.98  --bmc1_ucm                              false
% 2.86/0.98  --bmc1_add_unsat_core                   none
% 2.86/0.98  --bmc1_unsat_core_children              false
% 2.86/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.86/0.98  --bmc1_out_stat                         full
% 2.86/0.98  --bmc1_ground_init                      false
% 2.86/0.98  --bmc1_pre_inst_next_state              false
% 2.86/0.98  --bmc1_pre_inst_state                   false
% 2.86/0.98  --bmc1_pre_inst_reach_state             false
% 2.86/0.98  --bmc1_out_unsat_core                   false
% 2.86/0.98  --bmc1_aig_witness_out                  false
% 2.86/0.98  --bmc1_verbose                          false
% 2.86/0.98  --bmc1_dump_clauses_tptp                false
% 2.86/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.86/0.98  --bmc1_dump_file                        -
% 2.86/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.86/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.86/0.98  --bmc1_ucm_extend_mode                  1
% 2.86/0.98  --bmc1_ucm_init_mode                    2
% 2.86/0.98  --bmc1_ucm_cone_mode                    none
% 2.86/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.86/0.98  --bmc1_ucm_relax_model                  4
% 2.86/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.86/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.86/0.98  --bmc1_ucm_layered_model                none
% 2.86/0.98  --bmc1_ucm_max_lemma_size               10
% 2.86/0.98  
% 2.86/0.98  ------ AIG Options
% 2.86/0.98  
% 2.86/0.98  --aig_mode                              false
% 2.86/0.98  
% 2.86/0.98  ------ Instantiation Options
% 2.86/0.98  
% 2.86/0.98  --instantiation_flag                    true
% 2.86/0.98  --inst_sos_flag                         false
% 2.86/0.98  --inst_sos_phase                        true
% 2.86/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.86/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.86/0.98  --inst_lit_sel_side                     none
% 2.86/0.98  --inst_solver_per_active                1400
% 2.86/0.98  --inst_solver_calls_frac                1.
% 2.86/0.98  --inst_passive_queue_type               priority_queues
% 2.86/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.86/0.98  --inst_passive_queues_freq              [25;2]
% 2.86/0.98  --inst_dismatching                      true
% 2.86/0.98  --inst_eager_unprocessed_to_passive     true
% 2.86/0.98  --inst_prop_sim_given                   true
% 2.86/0.98  --inst_prop_sim_new                     false
% 2.86/0.98  --inst_subs_new                         false
% 2.86/0.98  --inst_eq_res_simp                      false
% 2.86/0.98  --inst_subs_given                       false
% 2.86/0.98  --inst_orphan_elimination               true
% 2.86/0.98  --inst_learning_loop_flag               true
% 2.86/0.98  --inst_learning_start                   3000
% 2.86/0.98  --inst_learning_factor                  2
% 2.86/0.98  --inst_start_prop_sim_after_learn       3
% 2.86/0.98  --inst_sel_renew                        solver
% 2.86/0.98  --inst_lit_activity_flag                true
% 2.86/0.98  --inst_restr_to_given                   false
% 2.86/0.98  --inst_activity_threshold               500
% 2.86/0.98  --inst_out_proof                        true
% 2.86/0.98  
% 2.86/0.98  ------ Resolution Options
% 2.86/0.98  
% 2.86/0.98  --resolution_flag                       false
% 2.86/0.98  --res_lit_sel                           adaptive
% 2.86/0.98  --res_lit_sel_side                      none
% 2.86/0.98  --res_ordering                          kbo
% 2.86/0.98  --res_to_prop_solver                    active
% 2.86/0.98  --res_prop_simpl_new                    false
% 2.86/0.98  --res_prop_simpl_given                  true
% 2.86/0.98  --res_passive_queue_type                priority_queues
% 2.86/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.86/0.98  --res_passive_queues_freq               [15;5]
% 2.86/0.98  --res_forward_subs                      full
% 2.86/0.98  --res_backward_subs                     full
% 2.86/0.98  --res_forward_subs_resolution           true
% 2.86/0.98  --res_backward_subs_resolution          true
% 2.86/0.98  --res_orphan_elimination                true
% 2.86/0.98  --res_time_limit                        2.
% 2.86/0.98  --res_out_proof                         true
% 2.86/0.98  
% 2.86/0.98  ------ Superposition Options
% 2.86/0.98  
% 2.86/0.98  --superposition_flag                    true
% 2.86/0.98  --sup_passive_queue_type                priority_queues
% 2.86/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.86/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.86/0.98  --demod_completeness_check              fast
% 2.86/0.98  --demod_use_ground                      true
% 2.86/0.98  --sup_to_prop_solver                    passive
% 2.86/0.98  --sup_prop_simpl_new                    true
% 2.86/0.98  --sup_prop_simpl_given                  true
% 2.86/0.98  --sup_fun_splitting                     false
% 2.86/0.98  --sup_smt_interval                      50000
% 2.86/0.98  
% 2.86/0.98  ------ Superposition Simplification Setup
% 2.86/0.98  
% 2.86/0.98  --sup_indices_passive                   []
% 2.86/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.86/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/0.98  --sup_full_bw                           [BwDemod]
% 2.86/0.98  --sup_immed_triv                        [TrivRules]
% 2.86/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.86/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/0.98  --sup_immed_bw_main                     []
% 2.86/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.86/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.86/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.86/0.98  
% 2.86/0.98  ------ Combination Options
% 2.86/0.98  
% 2.86/0.98  --comb_res_mult                         3
% 2.86/0.98  --comb_sup_mult                         2
% 2.86/0.98  --comb_inst_mult                        10
% 2.86/0.98  
% 2.86/0.98  ------ Debug Options
% 2.86/0.98  
% 2.86/0.98  --dbg_backtrace                         false
% 2.86/0.98  --dbg_dump_prop_clauses                 false
% 2.86/0.98  --dbg_dump_prop_clauses_file            -
% 2.86/0.98  --dbg_out_stat                          false
% 2.86/0.98  
% 2.86/0.98  
% 2.86/0.98  
% 2.86/0.98  
% 2.86/0.98  ------ Proving...
% 2.86/0.98  
% 2.86/0.98  
% 2.86/0.98  % SZS status Theorem for theBenchmark.p
% 2.86/0.98  
% 2.86/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.86/0.98  
% 2.86/0.98  fof(f9,axiom,(
% 2.86/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 2.86/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.86/0.98  
% 2.86/0.98  fof(f20,plain,(
% 2.86/0.98    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.86/0.98    inference(ennf_transformation,[],[f9])).
% 2.86/0.98  
% 2.86/0.98  fof(f21,plain,(
% 2.86/0.98    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.86/0.98    inference(flattening,[],[f20])).
% 2.86/0.98  
% 2.86/0.98  fof(f31,plain,(
% 2.86/0.98    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.86/0.98    inference(nnf_transformation,[],[f21])).
% 2.86/0.98  
% 2.86/0.98  fof(f32,plain,(
% 2.86/0.98    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.86/0.98    inference(rectify,[],[f31])).
% 2.86/0.98  
% 2.86/0.98  fof(f33,plain,(
% 2.86/0.98    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0))))),
% 2.86/0.98    introduced(choice_axiom,[])).
% 2.86/0.98  
% 2.86/0.98  fof(f34,plain,(
% 2.86/0.98    ! [X0] : (((v2_funct_1(X0) | (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.86/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f33])).
% 2.86/0.98  
% 2.86/0.98  fof(f56,plain,(
% 2.86/0.98    ( ! [X0] : (v2_funct_1(X0) | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.86/0.98    inference(cnf_transformation,[],[f34])).
% 2.86/0.98  
% 2.86/0.98  fof(f12,conjecture,(
% 2.86/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 2.86/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.86/0.98  
% 2.86/0.98  fof(f13,negated_conjecture,(
% 2.86/0.98    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 2.86/0.98    inference(negated_conjecture,[],[f12])).
% 2.86/0.98  
% 2.86/0.98  fof(f25,plain,(
% 2.86/0.98    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.86/0.98    inference(ennf_transformation,[],[f13])).
% 2.86/0.98  
% 2.86/0.98  fof(f26,plain,(
% 2.86/0.98    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.86/0.98    inference(flattening,[],[f25])).
% 2.86/0.98  
% 2.86/0.98  fof(f35,plain,(
% 2.86/0.98    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.86/0.98    inference(nnf_transformation,[],[f26])).
% 2.86/0.98  
% 2.86/0.98  fof(f36,plain,(
% 2.86/0.98    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.86/0.98    inference(flattening,[],[f35])).
% 2.86/0.98  
% 2.86/0.98  fof(f37,plain,(
% 2.86/0.98    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.86/0.98    inference(rectify,[],[f36])).
% 2.86/0.98  
% 2.86/0.98  fof(f39,plain,(
% 2.86/0.98    ( ! [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (sK4 != sK5 & k1_funct_1(X1,sK4) = k1_funct_1(X1,sK5) & r2_hidden(sK5,X0) & r2_hidden(sK4,X0))) )),
% 2.86/0.98    introduced(choice_axiom,[])).
% 2.86/0.98  
% 2.86/0.98  fof(f38,plain,(
% 2.86/0.98    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3) & r2_hidden(X3,sK2) & r2_hidden(X2,sK2)) | ~v2_funct_1(sK3)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 2.86/0.98    introduced(choice_axiom,[])).
% 2.86/0.98  
% 2.86/0.98  fof(f40,plain,(
% 2.86/0.98    ((sK4 != sK5 & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) & r2_hidden(sK5,sK2) & r2_hidden(sK4,sK2)) | ~v2_funct_1(sK3)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 2.86/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f37,f39,f38])).
% 2.86/0.98  
% 2.86/0.98  fof(f60,plain,(
% 2.86/0.98    v1_funct_1(sK3)),
% 2.86/0.98    inference(cnf_transformation,[],[f40])).
% 2.86/0.98  
% 2.86/0.98  fof(f62,plain,(
% 2.86/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 2.86/0.98    inference(cnf_transformation,[],[f40])).
% 2.86/0.98  
% 2.86/0.98  fof(f4,axiom,(
% 2.86/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.86/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.86/0.98  
% 2.86/0.98  fof(f29,plain,(
% 2.86/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.86/0.98    inference(nnf_transformation,[],[f4])).
% 2.86/0.98  
% 2.86/0.98  fof(f46,plain,(
% 2.86/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.86/0.98    inference(cnf_transformation,[],[f29])).
% 2.86/0.98  
% 2.86/0.98  fof(f6,axiom,(
% 2.86/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.86/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.86/0.98  
% 2.86/0.98  fof(f18,plain,(
% 2.86/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.86/0.98    inference(ennf_transformation,[],[f6])).
% 2.86/0.98  
% 2.86/0.98  fof(f49,plain,(
% 2.86/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.86/0.98    inference(cnf_transformation,[],[f18])).
% 2.86/0.98  
% 2.86/0.98  fof(f47,plain,(
% 2.86/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.86/0.98    inference(cnf_transformation,[],[f29])).
% 2.86/0.98  
% 2.86/0.98  fof(f8,axiom,(
% 2.86/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.86/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.86/0.98  
% 2.86/0.98  fof(f52,plain,(
% 2.86/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.86/0.98    inference(cnf_transformation,[],[f8])).
% 2.86/0.98  
% 2.86/0.98  fof(f66,plain,(
% 2.86/0.98    k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) | ~v2_funct_1(sK3)),
% 2.86/0.98    inference(cnf_transformation,[],[f40])).
% 2.86/0.98  
% 2.86/0.98  fof(f53,plain,(
% 2.86/0.98    ( ! [X4,X0,X3] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.86/0.99    inference(cnf_transformation,[],[f34])).
% 2.86/0.99  
% 2.86/0.99  fof(f55,plain,(
% 2.86/0.99    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK1(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.86/0.99    inference(cnf_transformation,[],[f34])).
% 2.86/0.99  
% 2.86/0.99  fof(f57,plain,(
% 2.86/0.99    ( ! [X0] : (v2_funct_1(X0) | sK0(X0) != sK1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.86/0.99    inference(cnf_transformation,[],[f34])).
% 2.86/0.99  
% 2.86/0.99  fof(f54,plain,(
% 2.86/0.99    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK0(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.86/0.99    inference(cnf_transformation,[],[f34])).
% 2.86/0.99  
% 2.86/0.99  fof(f10,axiom,(
% 2.86/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.86/0.99  
% 2.86/0.99  fof(f14,plain,(
% 2.86/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.86/0.99    inference(pure_predicate_removal,[],[f10])).
% 2.86/0.99  
% 2.86/0.99  fof(f22,plain,(
% 2.86/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.86/0.99    inference(ennf_transformation,[],[f14])).
% 2.86/0.99  
% 2.86/0.99  fof(f58,plain,(
% 2.86/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.86/0.99    inference(cnf_transformation,[],[f22])).
% 2.86/0.99  
% 2.86/0.99  fof(f7,axiom,(
% 2.86/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.86/0.99  
% 2.86/0.99  fof(f19,plain,(
% 2.86/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.86/0.99    inference(ennf_transformation,[],[f7])).
% 2.86/0.99  
% 2.86/0.99  fof(f30,plain,(
% 2.86/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.86/0.99    inference(nnf_transformation,[],[f19])).
% 2.86/0.99  
% 2.86/0.99  fof(f50,plain,(
% 2.86/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.86/0.99    inference(cnf_transformation,[],[f30])).
% 2.86/0.99  
% 2.86/0.99  fof(f63,plain,(
% 2.86/0.99    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2) | v2_funct_1(sK3)) )),
% 2.86/0.99    inference(cnf_transformation,[],[f40])).
% 2.86/0.99  
% 2.86/0.99  fof(f3,axiom,(
% 2.86/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.86/0.99  
% 2.86/0.99  fof(f15,plain,(
% 2.86/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.86/0.99    inference(ennf_transformation,[],[f3])).
% 2.86/0.99  
% 2.86/0.99  fof(f45,plain,(
% 2.86/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.86/0.99    inference(cnf_transformation,[],[f15])).
% 2.86/0.99  
% 2.86/0.99  fof(f11,axiom,(
% 2.86/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 2.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.86/0.99  
% 2.86/0.99  fof(f23,plain,(
% 2.86/0.99    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.86/0.99    inference(ennf_transformation,[],[f11])).
% 2.86/0.99  
% 2.86/0.99  fof(f24,plain,(
% 2.86/0.99    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.86/0.99    inference(flattening,[],[f23])).
% 2.86/0.99  
% 2.86/0.99  fof(f59,plain,(
% 2.86/0.99    ( ! [X2,X0,X3,X1] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.86/0.99    inference(cnf_transformation,[],[f24])).
% 2.86/0.99  
% 2.86/0.99  fof(f61,plain,(
% 2.86/0.99    v1_funct_2(sK3,sK2,sK2)),
% 2.86/0.99    inference(cnf_transformation,[],[f40])).
% 2.86/0.99  
% 2.86/0.99  fof(f65,plain,(
% 2.86/0.99    r2_hidden(sK5,sK2) | ~v2_funct_1(sK3)),
% 2.86/0.99    inference(cnf_transformation,[],[f40])).
% 2.86/0.99  
% 2.86/0.99  fof(f1,axiom,(
% 2.86/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.86/0.99  
% 2.86/0.99  fof(f27,plain,(
% 2.86/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.86/0.99    inference(nnf_transformation,[],[f1])).
% 2.86/0.99  
% 2.86/0.99  fof(f28,plain,(
% 2.86/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.86/0.99    inference(flattening,[],[f27])).
% 2.86/0.99  
% 2.86/0.99  fof(f41,plain,(
% 2.86/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.86/0.99    inference(cnf_transformation,[],[f28])).
% 2.86/0.99  
% 2.86/0.99  fof(f69,plain,(
% 2.86/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.86/0.99    inference(equality_resolution,[],[f41])).
% 2.86/0.99  
% 2.86/0.99  fof(f43,plain,(
% 2.86/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.86/0.99    inference(cnf_transformation,[],[f28])).
% 2.86/0.99  
% 2.86/0.99  fof(f67,plain,(
% 2.86/0.99    sK4 != sK5 | ~v2_funct_1(sK3)),
% 2.86/0.99    inference(cnf_transformation,[],[f40])).
% 2.86/0.99  
% 2.86/0.99  fof(f64,plain,(
% 2.86/0.99    r2_hidden(sK4,sK2) | ~v2_funct_1(sK3)),
% 2.86/0.99    inference(cnf_transformation,[],[f40])).
% 2.86/0.99  
% 2.86/0.99  fof(f2,axiom,(
% 2.86/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.86/0.99  
% 2.86/0.99  fof(f44,plain,(
% 2.86/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.86/0.99    inference(cnf_transformation,[],[f2])).
% 2.86/0.99  
% 2.86/0.99  cnf(c_13,plain,
% 2.86/0.99      ( ~ v1_funct_1(X0)
% 2.86/0.99      | v2_funct_1(X0)
% 2.86/0.99      | ~ v1_relat_1(X0)
% 2.86/0.99      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
% 2.86/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_26,negated_conjecture,
% 2.86/0.99      ( v1_funct_1(sK3) ),
% 2.86/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_427,plain,
% 2.86/0.99      ( v2_funct_1(X0)
% 2.86/0.99      | ~ v1_relat_1(X0)
% 2.86/0.99      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
% 2.86/0.99      | sK3 != X0 ),
% 2.86/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_26]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_428,plain,
% 2.86/0.99      ( v2_funct_1(sK3)
% 2.86/0.99      | ~ v1_relat_1(sK3)
% 2.86/0.99      | k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
% 2.86/0.99      inference(unflattening,[status(thm)],[c_427]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2530,plain,
% 2.86/0.99      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
% 2.86/0.99      | v2_funct_1(sK3) = iProver_top
% 2.86/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_428]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_27,plain,
% 2.86/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_24,negated_conjecture,
% 2.86/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 2.86/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_29,plain,
% 2.86/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_52,plain,
% 2.86/0.99      ( k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
% 2.86/0.99      | v1_funct_1(X0) != iProver_top
% 2.86/0.99      | v2_funct_1(X0) = iProver_top
% 2.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_54,plain,
% 2.86/0.99      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
% 2.86/0.99      | v1_funct_1(sK3) != iProver_top
% 2.86/0.99      | v2_funct_1(sK3) = iProver_top
% 2.86/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_52]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_6,plain,
% 2.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.86/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2795,plain,
% 2.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/0.99      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2861,plain,
% 2.86/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 2.86/0.99      | r1_tarski(sK3,k2_zfmisc_1(sK2,sK2)) ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_2795]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2862,plain,
% 2.86/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 2.86/0.99      | r1_tarski(sK3,k2_zfmisc_1(sK2,sK2)) = iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_2861]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_8,plain,
% 2.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.86/0.99      | ~ v1_relat_1(X1)
% 2.86/0.99      | v1_relat_1(X0) ),
% 2.86/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_5,plain,
% 2.86/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.86/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_204,plain,
% 2.86/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.86/0.99      inference(prop_impl,[status(thm)],[c_5]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_205,plain,
% 2.86/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.86/0.99      inference(renaming,[status(thm)],[c_204]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_261,plain,
% 2.86/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.86/0.99      inference(bin_hyper_res,[status(thm)],[c_8,c_205]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2766,plain,
% 2.86/0.99      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 2.86/0.99      | v1_relat_1(X0)
% 2.86/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_261]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2965,plain,
% 2.86/0.99      ( ~ r1_tarski(sK3,k2_zfmisc_1(sK2,sK2))
% 2.86/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK2))
% 2.86/0.99      | v1_relat_1(sK3) ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_2766]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2966,plain,
% 2.86/0.99      ( r1_tarski(sK3,k2_zfmisc_1(sK2,sK2)) != iProver_top
% 2.86/0.99      | v1_relat_1(k2_zfmisc_1(sK2,sK2)) != iProver_top
% 2.86/0.99      | v1_relat_1(sK3) = iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_2965]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_11,plain,
% 2.86/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.86/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_3291,plain,
% 2.86/0.99      ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_3292,plain,
% 2.86/0.99      ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) = iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_3291]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_3595,plain,
% 2.86/0.99      ( v2_funct_1(sK3) = iProver_top
% 2.86/0.99      | k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
% 2.86/0.99      inference(global_propositional_subsumption,
% 2.86/0.99                [status(thm)],
% 2.86/0.99                [c_2530,c_27,c_29,c_54,c_2862,c_2966,c_3292]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_3596,plain,
% 2.86/0.99      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
% 2.86/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.86/0.99      inference(renaming,[status(thm)],[c_3595]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_20,negated_conjecture,
% 2.86/0.99      ( ~ v2_funct_1(sK3) | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
% 2.86/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2542,plain,
% 2.86/0.99      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
% 2.86/0.99      | v2_funct_1(sK3) != iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_3605,plain,
% 2.86/0.99      ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 2.86/0.99      | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_3596,c_2542]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_16,plain,
% 2.86/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.86/0.99      | ~ r2_hidden(X2,k1_relat_1(X1))
% 2.86/0.99      | ~ v1_funct_1(X1)
% 2.86/0.99      | ~ v2_funct_1(X1)
% 2.86/0.99      | ~ v1_relat_1(X1)
% 2.86/0.99      | X0 = X2
% 2.86/0.99      | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
% 2.86/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_453,plain,
% 2.86/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.86/0.99      | ~ r2_hidden(X2,k1_relat_1(X1))
% 2.86/0.99      | ~ v2_funct_1(X1)
% 2.86/0.99      | ~ v1_relat_1(X1)
% 2.86/0.99      | X2 = X0
% 2.86/0.99      | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
% 2.86/0.99      | sK3 != X1 ),
% 2.86/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_26]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_454,plain,
% 2.86/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.86/0.99      | ~ r2_hidden(X1,k1_relat_1(sK3))
% 2.86/0.99      | ~ v2_funct_1(sK3)
% 2.86/0.99      | ~ v1_relat_1(sK3)
% 2.86/0.99      | X0 = X1
% 2.86/0.99      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
% 2.86/0.99      inference(unflattening,[status(thm)],[c_453]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_1932,plain,
% 2.86/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.86/0.99      | ~ r2_hidden(X1,k1_relat_1(sK3))
% 2.86/0.99      | X0 = X1
% 2.86/0.99      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
% 2.86/0.99      | ~ sP0_iProver_split ),
% 2.86/0.99      inference(splitting,
% 2.86/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.86/0.99                [c_454]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2528,plain,
% 2.86/0.99      ( X0 = X1
% 2.86/0.99      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
% 2.86/0.99      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.86/0.99      | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top
% 2.86/0.99      | sP0_iProver_split != iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_1932]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_3853,plain,
% 2.86/0.99      ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
% 2.86/0.99      | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
% 2.86/0.99      | sK1(sK3) = X0
% 2.86/0.99      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.86/0.99      | r2_hidden(sK1(sK3),k1_relat_1(sK3)) != iProver_top
% 2.86/0.99      | sP0_iProver_split != iProver_top ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_3605,c_2528]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_14,plain,
% 2.86/0.99      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 2.86/0.99      | ~ v1_funct_1(X0)
% 2.86/0.99      | v2_funct_1(X0)
% 2.86/0.99      | ~ v1_relat_1(X0) ),
% 2.86/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_414,plain,
% 2.86/0.99      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 2.86/0.99      | v2_funct_1(X0)
% 2.86/0.99      | ~ v1_relat_1(X0)
% 2.86/0.99      | sK3 != X0 ),
% 2.86/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_415,plain,
% 2.86/0.99      ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 2.86/0.99      | v2_funct_1(sK3)
% 2.86/0.99      | ~ v1_relat_1(sK3) ),
% 2.86/0.99      inference(unflattening,[status(thm)],[c_414]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_749,plain,
% 2.86/0.99      ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 2.86/0.99      | ~ v1_relat_1(sK3)
% 2.86/0.99      | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
% 2.86/0.99      inference(resolution,[status(thm)],[c_415,c_20]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_750,plain,
% 2.86/0.99      ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
% 2.86/0.99      | r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
% 2.86/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_749]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_4371,plain,
% 2.86/0.99      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.86/0.99      | sK1(sK3) = X0
% 2.86/0.99      | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
% 2.86/0.99      | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
% 2.86/0.99      | sP0_iProver_split != iProver_top ),
% 2.86/0.99      inference(global_propositional_subsumption,
% 2.86/0.99                [status(thm)],
% 2.86/0.99                [c_3853,c_29,c_750,c_2862,c_2966,c_3292]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_4372,plain,
% 2.86/0.99      ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
% 2.86/0.99      | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
% 2.86/0.99      | sK1(sK3) = X0
% 2.86/0.99      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.86/0.99      | sP0_iProver_split != iProver_top ),
% 2.86/0.99      inference(renaming,[status(thm)],[c_4371]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_4383,plain,
% 2.86/0.99      ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
% 2.86/0.99      | sK1(sK3) = sK0(sK3)
% 2.86/0.99      | r2_hidden(sK0(sK3),k1_relat_1(sK3)) != iProver_top
% 2.86/0.99      | sP0_iProver_split != iProver_top ),
% 2.86/0.99      inference(equality_resolution,[status(thm)],[c_4372]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_12,plain,
% 2.86/0.99      ( ~ v1_funct_1(X0)
% 2.86/0.99      | v2_funct_1(X0)
% 2.86/0.99      | ~ v1_relat_1(X0)
% 2.86/0.99      | sK1(X0) != sK0(X0) ),
% 2.86/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_440,plain,
% 2.86/0.99      ( v2_funct_1(X0)
% 2.86/0.99      | ~ v1_relat_1(X0)
% 2.86/0.99      | sK1(X0) != sK0(X0)
% 2.86/0.99      | sK3 != X0 ),
% 2.86/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_26]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_441,plain,
% 2.86/0.99      ( v2_funct_1(sK3) | ~ v1_relat_1(sK3) | sK1(sK3) != sK0(sK3) ),
% 2.86/0.99      inference(unflattening,[status(thm)],[c_440]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_567,plain,
% 2.86/0.99      ( ~ v1_relat_1(sK3)
% 2.86/0.99      | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
% 2.86/0.99      | sK1(sK3) != sK0(sK3) ),
% 2.86/0.99      inference(resolution,[status(thm)],[c_441,c_20]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_15,plain,
% 2.86/0.99      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 2.86/0.99      | ~ v1_funct_1(X0)
% 2.86/0.99      | v2_funct_1(X0)
% 2.86/0.99      | ~ v1_relat_1(X0) ),
% 2.86/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_401,plain,
% 2.86/0.99      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 2.86/0.99      | v2_funct_1(X0)
% 2.86/0.99      | ~ v1_relat_1(X0)
% 2.86/0.99      | sK3 != X0 ),
% 2.86/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_26]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_402,plain,
% 2.86/0.99      ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 2.86/0.99      | v2_funct_1(sK3)
% 2.86/0.99      | ~ v1_relat_1(sK3) ),
% 2.86/0.99      inference(unflattening,[status(thm)],[c_401]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_840,plain,
% 2.86/0.99      ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 2.86/0.99      | ~ v1_relat_1(sK3)
% 2.86/0.99      | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
% 2.86/0.99      inference(resolution,[status(thm)],[c_402,c_20]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_1933,plain,
% 2.86/0.99      ( ~ v2_funct_1(sK3) | ~ v1_relat_1(sK3) | sP0_iProver_split ),
% 2.86/0.99      inference(splitting,
% 2.86/0.99                [splitting(split),new_symbols(definition,[])],
% 2.86/0.99                [c_454]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_17,plain,
% 2.86/0.99      ( v4_relat_1(X0,X1)
% 2.86/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.86/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_10,plain,
% 2.86/0.99      ( ~ v4_relat_1(X0,X1)
% 2.86/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 2.86/0.99      | ~ v1_relat_1(X0) ),
% 2.86/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_382,plain,
% 2.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 2.86/0.99      | ~ v1_relat_1(X0) ),
% 2.86/0.99      inference(resolution,[status(thm)],[c_17,c_10]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_3816,plain,
% 2.86/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 2.86/0.99      | r1_tarski(k1_relat_1(sK3),sK2)
% 2.86/0.99      | ~ v1_relat_1(sK3) ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_382]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_23,negated_conjecture,
% 2.86/0.99      ( ~ r2_hidden(X0,sK2)
% 2.86/0.99      | ~ r2_hidden(X1,sK2)
% 2.86/0.99      | v2_funct_1(sK3)
% 2.86/0.99      | X1 = X0
% 2.86/0.99      | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
% 2.86/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2539,plain,
% 2.86/0.99      ( X0 = X1
% 2.86/0.99      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
% 2.86/0.99      | r2_hidden(X1,sK2) != iProver_top
% 2.86/0.99      | r2_hidden(X0,sK2) != iProver_top
% 2.86/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_3854,plain,
% 2.86/0.99      ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
% 2.86/0.99      | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
% 2.86/0.99      | sK1(sK3) = X0
% 2.86/0.99      | r2_hidden(X0,sK2) != iProver_top
% 2.86/0.99      | r2_hidden(sK1(sK3),sK2) != iProver_top
% 2.86/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_3605,c_2539]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_3893,plain,
% 2.86/0.99      ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
% 2.86/0.99      | sK1(sK3) = sK0(sK3)
% 2.86/0.99      | r2_hidden(sK1(sK3),sK2) != iProver_top
% 2.86/0.99      | r2_hidden(sK0(sK3),sK2) != iProver_top
% 2.86/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.86/0.99      inference(equality_resolution,[status(thm)],[c_3854]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_55,plain,
% 2.86/0.99      ( sK1(X0) != sK0(X0)
% 2.86/0.99      | v1_funct_1(X0) != iProver_top
% 2.86/0.99      | v2_funct_1(X0) = iProver_top
% 2.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_57,plain,
% 2.86/0.99      ( sK1(sK3) != sK0(sK3)
% 2.86/0.99      | v1_funct_1(sK3) != iProver_top
% 2.86/0.99      | v2_funct_1(sK3) = iProver_top
% 2.86/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_55]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_3589,plain,
% 2.86/0.99      ( ~ r2_hidden(sK1(sK3),sK2)
% 2.86/0.99      | ~ r2_hidden(sK0(sK3),sK2)
% 2.86/0.99      | v2_funct_1(sK3)
% 2.86/0.99      | k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
% 2.86/0.99      | sK1(sK3) = sK0(sK3) ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_23]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_3590,plain,
% 2.86/0.99      ( k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
% 2.86/0.99      | sK1(sK3) = sK0(sK3)
% 2.86/0.99      | r2_hidden(sK1(sK3),sK2) != iProver_top
% 2.86/0.99      | r2_hidden(sK0(sK3),sK2) != iProver_top
% 2.86/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_3589]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_4363,plain,
% 2.86/0.99      ( r2_hidden(sK1(sK3),sK2) != iProver_top
% 2.86/0.99      | r2_hidden(sK0(sK3),sK2) != iProver_top
% 2.86/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.86/0.99      inference(global_propositional_subsumption,
% 2.86/0.99                [status(thm)],
% 2.86/0.99                [c_3893,c_27,c_29,c_54,c_57,c_2862,c_2966,c_3292,c_3590]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_4365,plain,
% 2.86/0.99      ( ~ r2_hidden(sK1(sK3),sK2)
% 2.86/0.99      | ~ r2_hidden(sK0(sK3),sK2)
% 2.86/0.99      | v2_funct_1(sK3) ),
% 2.86/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4363]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_4392,plain,
% 2.86/0.99      ( ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 2.86/0.99      | ~ sP0_iProver_split
% 2.86/0.99      | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
% 2.86/0.99      | sK1(sK3) = sK0(sK3) ),
% 2.86/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4383]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_4,plain,
% 2.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.86/0.99      | ~ r2_hidden(X2,X0)
% 2.86/0.99      | r2_hidden(X2,X1) ),
% 2.86/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_258,plain,
% 2.86/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.86/0.99      inference(bin_hyper_res,[status(thm)],[c_4,c_205]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_3557,plain,
% 2.86/0.99      ( r2_hidden(sK0(sK3),X0)
% 2.86/0.99      | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 2.86/0.99      | ~ r1_tarski(k1_relat_1(sK3),X0) ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_258]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_4422,plain,
% 2.86/0.99      ( ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 2.86/0.99      | r2_hidden(sK0(sK3),sK2)
% 2.86/0.99      | ~ r1_tarski(k1_relat_1(sK3),sK2) ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_3557]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_3572,plain,
% 2.86/0.99      ( r2_hidden(sK1(sK3),X0)
% 2.86/0.99      | ~ r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 2.86/0.99      | ~ r1_tarski(k1_relat_1(sK3),X0) ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_258]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_4437,plain,
% 2.86/0.99      ( ~ r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 2.86/0.99      | r2_hidden(sK1(sK3),sK2)
% 2.86/0.99      | ~ r1_tarski(k1_relat_1(sK3),sK2) ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_3572]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_4628,plain,
% 2.86/0.99      ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
% 2.86/0.99      inference(global_propositional_subsumption,
% 2.86/0.99                [status(thm)],
% 2.86/0.99                [c_4383,c_24,c_567,c_749,c_840,c_1933,c_2861,c_2965,
% 2.86/0.99                 c_3291,c_3816,c_4365,c_4392,c_4422,c_4437]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_18,plain,
% 2.86/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.86/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/0.99      | ~ r2_hidden(X3,X1)
% 2.86/0.99      | ~ v1_funct_1(X0)
% 2.86/0.99      | ~ v2_funct_1(X0)
% 2.86/0.99      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
% 2.86/0.99      | k1_xboole_0 = X2 ),
% 2.86/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_25,negated_conjecture,
% 2.86/0.99      ( v1_funct_2(sK3,sK2,sK2) ),
% 2.86/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_353,plain,
% 2.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/0.99      | ~ r2_hidden(X3,X1)
% 2.86/0.99      | ~ v1_funct_1(X0)
% 2.86/0.99      | ~ v2_funct_1(X0)
% 2.86/0.99      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
% 2.86/0.99      | sK2 != X2
% 2.86/0.99      | sK2 != X1
% 2.86/0.99      | sK3 != X0
% 2.86/0.99      | k1_xboole_0 = X2 ),
% 2.86/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_354,plain,
% 2.86/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 2.86/0.99      | ~ r2_hidden(X0,sK2)
% 2.86/0.99      | ~ v1_funct_1(sK3)
% 2.86/0.99      | ~ v2_funct_1(sK3)
% 2.86/0.99      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 2.86/0.99      | k1_xboole_0 = sK2 ),
% 2.86/0.99      inference(unflattening,[status(thm)],[c_353]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_358,plain,
% 2.86/0.99      ( ~ r2_hidden(X0,sK2)
% 2.86/0.99      | ~ v2_funct_1(sK3)
% 2.86/0.99      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 2.86/0.99      | k1_xboole_0 = sK2 ),
% 2.86/0.99      inference(global_propositional_subsumption,
% 2.86/0.99                [status(thm)],
% 2.86/0.99                [c_354,c_26,c_24]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_1935,plain,
% 2.86/0.99      ( ~ v2_funct_1(sK3) | sP1_iProver_split | k1_xboole_0 = sK2 ),
% 2.86/0.99      inference(splitting,
% 2.86/0.99                [splitting(split),new_symbols(definition,[])],
% 2.86/0.99                [c_358]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2534,plain,
% 2.86/0.99      ( k1_xboole_0 = sK2
% 2.86/0.99      | v2_funct_1(sK3) != iProver_top
% 2.86/0.99      | sP1_iProver_split = iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_1935]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_3601,plain,
% 2.86/0.99      ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 2.86/0.99      | sK2 = k1_xboole_0
% 2.86/0.99      | sP1_iProver_split = iProver_top ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_3596,c_2534]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_21,negated_conjecture,
% 2.86/0.99      ( r2_hidden(sK5,sK2) | ~ v2_funct_1(sK3) ),
% 2.86/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2541,plain,
% 2.86/0.99      ( r2_hidden(sK5,sK2) = iProver_top
% 2.86/0.99      | v2_funct_1(sK3) != iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_1934,plain,
% 2.86/0.99      ( ~ r2_hidden(X0,sK2)
% 2.86/0.99      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 2.86/0.99      | ~ sP1_iProver_split ),
% 2.86/0.99      inference(splitting,
% 2.86/0.99                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.86/0.99                [c_358]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2535,plain,
% 2.86/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 2.86/0.99      | r2_hidden(X0,sK2) != iProver_top
% 2.86/0.99      | sP1_iProver_split != iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_1934]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_3215,plain,
% 2.86/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
% 2.86/0.99      | v2_funct_1(sK3) != iProver_top
% 2.86/0.99      | sP1_iProver_split != iProver_top ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_2541,c_2535]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_3603,plain,
% 2.86/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
% 2.86/0.99      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 2.86/0.99      | sP1_iProver_split != iProver_top ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_3596,c_3215]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_4311,plain,
% 2.86/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
% 2.86/0.99      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 2.86/0.99      | sK2 = k1_xboole_0 ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_3601,c_3603]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_4631,plain,
% 2.86/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
% 2.86/0.99      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 2.86/0.99      | sK2 = k1_xboole_0 ),
% 2.86/0.99      inference(demodulation,[status(thm)],[c_4628,c_4311]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2,plain,
% 2.86/0.99      ( r1_tarski(X0,X0) ),
% 2.86/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_82,plain,
% 2.86/0.99      ( r1_tarski(sK3,sK3) ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_0,plain,
% 2.86/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.86/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_86,plain,
% 2.86/0.99      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_19,negated_conjecture,
% 2.86/0.99      ( ~ v2_funct_1(sK3) | sK4 != sK5 ),
% 2.86/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_579,plain,
% 2.86/0.99      ( ~ v1_relat_1(sK3) | sK1(sK3) != sK0(sK3) | sK5 != sK4 ),
% 2.86/0.99      inference(resolution,[status(thm)],[c_441,c_19]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_670,plain,
% 2.86/0.99      ( ~ v1_relat_1(sK3)
% 2.86/0.99      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 2.86/0.99      | sK5 != sK4 ),
% 2.86/0.99      inference(resolution,[status(thm)],[c_428,c_19]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_761,plain,
% 2.86/0.99      ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 2.86/0.99      | ~ v1_relat_1(sK3)
% 2.86/0.99      | sK5 != sK4 ),
% 2.86/0.99      inference(resolution,[status(thm)],[c_415,c_19]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_852,plain,
% 2.86/0.99      ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 2.86/0.99      | ~ v1_relat_1(sK3)
% 2.86/0.99      | sK5 != sK4 ),
% 2.86/0.99      inference(resolution,[status(thm)],[c_402,c_19]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_1948,plain,( X0 != X1 | sK1(X0) = sK1(X1) ),theory(equality) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_1960,plain,
% 2.86/0.99      ( sK1(sK3) = sK1(sK3) | sK3 != sK3 ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_1948]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_1938,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_3592,plain,
% 2.86/0.99      ( sK1(sK3) != X0 | sK1(sK3) = sK0(sK3) | sK0(sK3) != X0 ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_1938]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_4485,plain,
% 2.86/0.99      ( sK1(sK3) != sK1(sK3)
% 2.86/0.99      | sK1(sK3) = sK0(sK3)
% 2.86/0.99      | sK0(sK3) != sK1(sK3) ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_3592]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_4660,plain,
% 2.86/0.99      ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4)
% 2.86/0.99      | sK5 = X0
% 2.86/0.99      | r2_hidden(X0,sK2) != iProver_top
% 2.86/0.99      | r2_hidden(sK5,sK2) != iProver_top
% 2.86/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_4628,c_2539]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_46,plain,
% 2.86/0.99      ( r2_hidden(sK0(X0),k1_relat_1(X0)) = iProver_top
% 2.86/0.99      | v1_funct_1(X0) != iProver_top
% 2.86/0.99      | v2_funct_1(X0) = iProver_top
% 2.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_48,plain,
% 2.86/0.99      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 2.86/0.99      | v1_funct_1(sK3) != iProver_top
% 2.86/0.99      | v2_funct_1(sK3) = iProver_top
% 2.86/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_46]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_49,plain,
% 2.86/0.99      ( r2_hidden(sK1(X0),k1_relat_1(X0)) = iProver_top
% 2.86/0.99      | v1_funct_1(X0) != iProver_top
% 2.86/0.99      | v2_funct_1(X0) = iProver_top
% 2.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_51,plain,
% 2.86/0.99      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
% 2.86/0.99      | v1_funct_1(sK3) != iProver_top
% 2.86/0.99      | v2_funct_1(sK3) = iProver_top
% 2.86/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_49]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_3817,plain,
% 2.86/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 2.86/0.99      | r1_tarski(k1_relat_1(sK3),sK2) = iProver_top
% 2.86/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_3816]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_4423,plain,
% 2.86/0.99      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) != iProver_top
% 2.86/0.99      | r2_hidden(sK0(sK3),sK2) = iProver_top
% 2.86/0.99      | r1_tarski(k1_relat_1(sK3),sK2) != iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_4422]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_4438,plain,
% 2.86/0.99      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) != iProver_top
% 2.86/0.99      | r2_hidden(sK1(sK3),sK2) = iProver_top
% 2.86/0.99      | r1_tarski(k1_relat_1(sK3),sK2) != iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_4437]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_4688,plain,
% 2.86/0.99      ( v2_funct_1(sK3) = iProver_top ),
% 2.86/0.99      inference(global_propositional_subsumption,
% 2.86/0.99                [status(thm)],
% 2.86/0.99                [c_4660,c_27,c_29,c_48,c_51,c_54,c_57,c_2862,c_2966,
% 2.86/0.99                 c_3292,c_3590,c_3817,c_4423,c_4438]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_4690,plain,
% 2.86/0.99      ( v2_funct_1(sK3) ),
% 2.86/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4688]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_5457,plain,
% 2.86/0.99      ( ~ r2_hidden(sK1(X0),k1_relat_1(sK3))
% 2.86/0.99      | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 2.86/0.99      | ~ sP0_iProver_split
% 2.86/0.99      | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(X0))
% 2.86/0.99      | sK0(sK3) = sK1(X0) ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_1932]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_5464,plain,
% 2.86/0.99      ( ~ r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 2.86/0.99      | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 2.86/0.99      | ~ sP0_iProver_split
% 2.86/0.99      | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(sK3))
% 2.86/0.99      | sK0(sK3) = sK1(sK3) ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_5457]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_4693,plain,
% 2.86/0.99      ( sK2 = k1_xboole_0 | sP1_iProver_split = iProver_top ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_4688,c_2534]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2549,plain,
% 2.86/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2537,plain,
% 2.86/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.86/0.99      | r2_hidden(X0,X2) = iProver_top
% 2.86/0.99      | r1_tarski(X1,X2) != iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_258]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_4840,plain,
% 2.86/0.99      ( r2_hidden(sK5,X0) = iProver_top
% 2.86/0.99      | r1_tarski(sK2,X0) != iProver_top
% 2.86/0.99      | v2_funct_1(sK3) != iProver_top ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_2541,c_2537]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_5153,plain,
% 2.86/0.99      ( r1_tarski(sK2,X0) != iProver_top
% 2.86/0.99      | r2_hidden(sK5,X0) = iProver_top ),
% 2.86/0.99      inference(global_propositional_subsumption,
% 2.86/0.99                [status(thm)],
% 2.86/0.99                [c_4840,c_27,c_29,c_48,c_51,c_54,c_57,c_2862,c_2966,
% 2.86/0.99                 c_3292,c_3590,c_3817,c_4423,c_4438]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_5154,plain,
% 2.86/0.99      ( r2_hidden(sK5,X0) = iProver_top
% 2.86/0.99      | r1_tarski(sK2,X0) != iProver_top ),
% 2.86/0.99      inference(renaming,[status(thm)],[c_5153]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_5161,plain,
% 2.86/0.99      ( r2_hidden(sK5,sK2) = iProver_top ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_2549,c_5154]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_5166,plain,
% 2.86/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
% 2.86/0.99      | sP1_iProver_split != iProver_top ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_5161,c_2535]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_5169,plain,
% 2.86/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
% 2.86/0.99      | sP1_iProver_split != iProver_top ),
% 2.86/0.99      inference(light_normalisation,[status(thm)],[c_5166,c_4628]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_6060,plain,
% 2.86/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
% 2.86/0.99      | sK2 = k1_xboole_0 ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_4693,c_5169]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_22,negated_conjecture,
% 2.86/0.99      ( r2_hidden(sK4,sK2) | ~ v2_funct_1(sK3) ),
% 2.86/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2540,plain,
% 2.86/0.99      ( r2_hidden(sK4,sK2) = iProver_top
% 2.86/0.99      | v2_funct_1(sK3) != iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_3216,plain,
% 2.86/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 2.86/0.99      | v2_funct_1(sK3) != iProver_top
% 2.86/0.99      | sP1_iProver_split != iProver_top ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_2540,c_2535]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_4694,plain,
% 2.86/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 2.86/0.99      | sP1_iProver_split != iProver_top ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_4688,c_3216]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_5485,plain,
% 2.86/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 2.86/0.99      | sK2 = k1_xboole_0 ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_4693,c_4694]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_6172,plain,
% 2.86/0.99      ( sK2 = k1_xboole_0 | sK5 = sK4 ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_6060,c_5485]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_6297,plain,
% 2.86/0.99      ( sK2 = k1_xboole_0 ),
% 2.86/0.99      inference(global_propositional_subsumption,
% 2.86/0.99                [status(thm)],
% 2.86/0.99                [c_4631,c_24,c_82,c_86,c_579,c_670,c_761,c_852,c_1960,
% 2.86/0.99                 c_1933,c_2861,c_2965,c_3291,c_4485,c_4690,c_5464,c_6172]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2538,plain,
% 2.86/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2533,plain,
% 2.86/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.86/0.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 2.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_382]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_4189,plain,
% 2.86/0.99      ( r1_tarski(k1_relat_1(sK3),sK2) = iProver_top
% 2.86/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_2538,c_2533]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_4205,plain,
% 2.86/0.99      ( r1_tarski(k1_relat_1(sK3),sK2) = iProver_top ),
% 2.86/0.99      inference(global_propositional_subsumption,
% 2.86/0.99                [status(thm)],
% 2.86/0.99                [c_4189,c_29,c_2862,c_2966,c_3292,c_3817]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_6310,plain,
% 2.86/0.99      ( r1_tarski(k1_relat_1(sK3),k1_xboole_0) = iProver_top ),
% 2.86/0.99      inference(demodulation,[status(thm)],[c_6297,c_4205]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_3,plain,
% 2.86/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.86/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2548,plain,
% 2.86/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2550,plain,
% 2.86/0.99      ( X0 = X1
% 2.86/0.99      | r1_tarski(X0,X1) != iProver_top
% 2.86/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_3698,plain,
% 2.86/0.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_2548,c_2550]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_6691,plain,
% 2.86/0.99      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_6310,c_3698]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_4659,plain,
% 2.86/0.99      ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4)
% 2.86/0.99      | sK5 = X0
% 2.86/0.99      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.86/0.99      | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
% 2.86/0.99      | sP0_iProver_split != iProver_top ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_4628,c_2528]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_1965,plain,
% 2.86/0.99      ( v2_funct_1(sK3) != iProver_top
% 2.86/0.99      | v1_relat_1(sK3) != iProver_top
% 2.86/0.99      | sP0_iProver_split = iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_1933]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_5394,plain,
% 2.86/0.99      ( r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
% 2.86/0.99      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.86/0.99      | sK5 = X0
% 2.86/0.99      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4) ),
% 2.86/0.99      inference(global_propositional_subsumption,
% 2.86/0.99                [status(thm)],
% 2.86/0.99                [c_4659,c_27,c_29,c_48,c_51,c_54,c_57,c_1965,c_2862,
% 2.86/0.99                 c_2966,c_3292,c_3590,c_3817,c_4423,c_4438]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_5395,plain,
% 2.86/0.99      ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4)
% 2.86/0.99      | sK5 = X0
% 2.86/0.99      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.86/0.99      | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top ),
% 2.86/0.99      inference(renaming,[status(thm)],[c_5394]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_5406,plain,
% 2.86/0.99      ( sK5 = sK4
% 2.86/0.99      | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
% 2.86/0.99      | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
% 2.86/0.99      inference(equality_resolution,[status(thm)],[c_5395]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_6067,plain,
% 2.86/0.99      ( r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
% 2.86/0.99      | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
% 2.86/0.99      inference(global_propositional_subsumption,
% 2.86/0.99                [status(thm)],
% 2.86/0.99                [c_5406,c_27,c_29,c_35,c_36,c_48,c_51,c_54,c_57,c_1965,
% 2.86/0.99                 c_2862,c_2966,c_3292,c_3590,c_3817,c_4423,c_4438,c_5179]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_7154,plain,
% 2.86/0.99      ( r2_hidden(sK5,k1_xboole_0) != iProver_top
% 2.86/0.99      | r2_hidden(sK4,k1_xboole_0) != iProver_top ),
% 2.86/0.99      inference(demodulation,[status(thm)],[c_6691,c_6067]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_6306,plain,
% 2.86/0.99      ( r2_hidden(sK5,k1_xboole_0) = iProver_top ),
% 2.86/0.99      inference(demodulation,[status(thm)],[c_6297,c_5161]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_4841,plain,
% 2.86/0.99      ( r2_hidden(sK4,X0) = iProver_top
% 2.86/0.99      | r1_tarski(sK2,X0) != iProver_top
% 2.86/0.99      | v2_funct_1(sK3) != iProver_top ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_2540,c_2537]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_5266,plain,
% 2.86/0.99      ( r1_tarski(sK2,X0) != iProver_top
% 2.86/0.99      | r2_hidden(sK4,X0) = iProver_top ),
% 2.86/0.99      inference(global_propositional_subsumption,
% 2.86/0.99                [status(thm)],
% 2.86/0.99                [c_4841,c_27,c_29,c_48,c_51,c_54,c_57,c_2862,c_2966,
% 2.86/0.99                 c_3292,c_3590,c_3817,c_4423,c_4438]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_5267,plain,
% 2.86/0.99      ( r2_hidden(sK4,X0) = iProver_top
% 2.86/0.99      | r1_tarski(sK2,X0) != iProver_top ),
% 2.86/0.99      inference(renaming,[status(thm)],[c_5266]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_5274,plain,
% 2.86/0.99      ( r2_hidden(sK4,sK2) = iProver_top ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_2549,c_5267]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_6304,plain,
% 2.86/0.99      ( r2_hidden(sK4,k1_xboole_0) = iProver_top ),
% 2.86/0.99      inference(demodulation,[status(thm)],[c_6297,c_5274]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(contradiction,plain,
% 2.86/0.99      ( $false ),
% 2.86/0.99      inference(minisat,[status(thm)],[c_7154,c_6306,c_6304]) ).
% 2.86/0.99  
% 2.86/0.99  
% 2.86/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.86/0.99  
% 2.86/0.99  ------                               Statistics
% 2.86/0.99  
% 2.86/0.99  ------ General
% 2.86/0.99  
% 2.86/0.99  abstr_ref_over_cycles:                  0
% 2.86/0.99  abstr_ref_under_cycles:                 0
% 2.86/0.99  gc_basic_clause_elim:                   0
% 2.86/0.99  forced_gc_time:                         0
% 2.86/0.99  parsing_time:                           0.008
% 2.86/0.99  unif_index_cands_time:                  0.
% 2.86/0.99  unif_index_add_time:                    0.
% 2.86/0.99  orderings_time:                         0.
% 2.86/0.99  out_proof_time:                         0.012
% 2.86/0.99  total_time:                             0.188
% 2.86/0.99  num_of_symbols:                         53
% 2.86/0.99  num_of_terms:                           4182
% 2.86/0.99  
% 2.86/0.99  ------ Preprocessing
% 2.86/0.99  
% 2.86/0.99  num_of_splits:                          2
% 2.86/0.99  num_of_split_atoms:                     2
% 2.86/0.99  num_of_reused_defs:                     0
% 2.86/0.99  num_eq_ax_congr_red:                    9
% 2.86/0.99  num_of_sem_filtered_clauses:            1
% 2.86/0.99  num_of_subtypes:                        0
% 2.86/0.99  monotx_restored_types:                  0
% 2.86/0.99  sat_num_of_epr_types:                   0
% 2.86/0.99  sat_num_of_non_cyclic_types:            0
% 2.86/0.99  sat_guarded_non_collapsed_types:        0
% 2.86/0.99  num_pure_diseq_elim:                    0
% 2.86/0.99  simp_replaced_by:                       0
% 2.86/0.99  res_preprocessed:                       125
% 2.86/0.99  prep_upred:                             0
% 2.86/0.99  prep_unflattend:                        8
% 2.86/0.99  smt_new_axioms:                         0
% 2.86/0.99  pred_elim_cands:                        5
% 2.86/0.99  pred_elim:                              3
% 2.86/0.99  pred_elim_cl:                           4
% 2.86/0.99  pred_elim_cycles:                       5
% 2.86/0.99  merged_defs:                            8
% 2.86/0.99  merged_defs_ncl:                        0
% 2.86/0.99  bin_hyper_res:                          10
% 2.86/0.99  prep_cycles:                            4
% 2.86/0.99  pred_elim_time:                         0.024
% 2.86/0.99  splitting_time:                         0.
% 2.86/0.99  sem_filter_time:                        0.
% 2.86/0.99  monotx_time:                            0.001
% 2.86/0.99  subtype_inf_time:                       0.
% 2.86/0.99  
% 2.86/0.99  ------ Problem properties
% 2.86/0.99  
% 2.86/0.99  clauses:                                24
% 2.86/0.99  conjectures:                            6
% 2.86/0.99  epr:                                    10
% 2.86/0.99  horn:                                   19
% 2.86/0.99  ground:                                 11
% 2.86/0.99  unary:                                  4
% 2.86/0.99  binary:                                 6
% 2.86/0.99  lits:                                   62
% 2.86/0.99  lits_eq:                                11
% 2.86/0.99  fd_pure:                                0
% 2.86/0.99  fd_pseudo:                              0
% 2.86/0.99  fd_cond:                                0
% 2.86/0.99  fd_pseudo_cond:                         3
% 2.86/0.99  ac_symbols:                             0
% 2.86/0.99  
% 2.86/0.99  ------ Propositional Solver
% 2.86/0.99  
% 2.86/0.99  prop_solver_calls:                      30
% 2.86/0.99  prop_fast_solver_calls:                 1192
% 2.86/0.99  smt_solver_calls:                       0
% 2.86/0.99  smt_fast_solver_calls:                  0
% 2.86/0.99  prop_num_of_clauses:                    2117
% 2.86/0.99  prop_preprocess_simplified:             6186
% 2.86/0.99  prop_fo_subsumed:                       32
% 2.86/0.99  prop_solver_time:                       0.
% 2.86/0.99  smt_solver_time:                        0.
% 2.86/0.99  smt_fast_solver_time:                   0.
% 2.86/0.99  prop_fast_solver_time:                  0.
% 2.86/0.99  prop_unsat_core_time:                   0.
% 2.86/0.99  
% 2.86/0.99  ------ QBF
% 2.86/0.99  
% 2.86/0.99  qbf_q_res:                              0
% 2.86/0.99  qbf_num_tautologies:                    0
% 2.86/0.99  qbf_prep_cycles:                        0
% 2.86/0.99  
% 2.86/0.99  ------ BMC1
% 2.86/0.99  
% 2.86/0.99  bmc1_current_bound:                     -1
% 2.86/0.99  bmc1_last_solved_bound:                 -1
% 2.86/0.99  bmc1_unsat_core_size:                   -1
% 2.86/0.99  bmc1_unsat_core_parents_size:           -1
% 2.86/0.99  bmc1_merge_next_fun:                    0
% 2.86/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.86/0.99  
% 2.86/0.99  ------ Instantiation
% 2.86/0.99  
% 2.86/0.99  inst_num_of_clauses:                    609
% 2.86/0.99  inst_num_in_passive:                    210
% 2.86/0.99  inst_num_in_active:                     361
% 2.86/0.99  inst_num_in_unprocessed:                41
% 2.86/0.99  inst_num_of_loops:                      400
% 2.86/0.99  inst_num_of_learning_restarts:          0
% 2.86/0.99  inst_num_moves_active_passive:          34
% 2.86/0.99  inst_lit_activity:                      0
% 2.86/0.99  inst_lit_activity_moves:                0
% 2.86/0.99  inst_num_tautologies:                   0
% 2.86/0.99  inst_num_prop_implied:                  0
% 2.86/0.99  inst_num_existing_simplified:           0
% 2.86/0.99  inst_num_eq_res_simplified:             0
% 2.86/0.99  inst_num_child_elim:                    0
% 2.86/0.99  inst_num_of_dismatching_blockings:      266
% 2.86/0.99  inst_num_of_non_proper_insts:           923
% 2.86/0.99  inst_num_of_duplicates:                 0
% 2.86/0.99  inst_inst_num_from_inst_to_res:         0
% 2.86/0.99  inst_dismatching_checking_time:         0.
% 2.86/0.99  
% 2.86/0.99  ------ Resolution
% 2.86/0.99  
% 2.86/0.99  res_num_of_clauses:                     0
% 2.86/0.99  res_num_in_passive:                     0
% 2.86/0.99  res_num_in_active:                      0
% 2.86/0.99  res_num_of_loops:                       129
% 2.86/0.99  res_forward_subset_subsumed:            83
% 2.86/0.99  res_backward_subset_subsumed:           10
% 2.86/0.99  res_forward_subsumed:                   0
% 2.86/0.99  res_backward_subsumed:                  0
% 2.86/0.99  res_forward_subsumption_resolution:     0
% 2.86/0.99  res_backward_subsumption_resolution:    0
% 2.86/0.99  res_clause_to_clause_subsumption:       191
% 2.86/0.99  res_orphan_elimination:                 0
% 2.86/0.99  res_tautology_del:                      113
% 2.86/0.99  res_num_eq_res_simplified:              0
% 2.86/0.99  res_num_sel_changes:                    0
% 2.86/0.99  res_moves_from_active_to_pass:          0
% 2.86/0.99  
% 2.86/0.99  ------ Superposition
% 2.86/0.99  
% 2.86/0.99  sup_time_total:                         0.
% 2.86/0.99  sup_time_generating:                    0.
% 2.86/0.99  sup_time_sim_full:                      0.
% 2.86/0.99  sup_time_sim_immed:                     0.
% 2.86/0.99  
% 2.86/0.99  sup_num_of_clauses:                     64
% 2.86/0.99  sup_num_in_active:                      42
% 2.86/0.99  sup_num_in_passive:                     22
% 2.86/0.99  sup_num_of_loops:                       78
% 2.86/0.99  sup_fw_superposition:                   48
% 2.86/0.99  sup_bw_superposition:                   48
% 2.86/0.99  sup_immediate_simplified:               14
% 2.86/0.99  sup_given_eliminated:                   2
% 2.86/0.99  comparisons_done:                       0
% 2.86/0.99  comparisons_avoided:                    24
% 2.86/0.99  
% 2.86/0.99  ------ Simplifications
% 2.86/0.99  
% 2.86/0.99  
% 2.86/0.99  sim_fw_subset_subsumed:                 13
% 2.86/0.99  sim_bw_subset_subsumed:                 5
% 2.86/0.99  sim_fw_subsumed:                        1
% 2.86/0.99  sim_bw_subsumed:                        1
% 2.86/0.99  sim_fw_subsumption_res:                 0
% 2.86/0.99  sim_bw_subsumption_res:                 0
% 2.86/0.99  sim_tautology_del:                      2
% 2.86/0.99  sim_eq_tautology_del:                   13
% 2.86/0.99  sim_eq_res_simp:                        0
% 2.86/0.99  sim_fw_demodulated:                     0
% 2.86/0.99  sim_bw_demodulated:                     33
% 2.86/0.99  sim_light_normalised:                   2
% 2.86/0.99  sim_joinable_taut:                      0
% 2.86/0.99  sim_joinable_simp:                      0
% 2.86/0.99  sim_ac_normalised:                      0
% 2.86/0.99  sim_smt_subsumption:                    0
% 2.86/0.99  
%------------------------------------------------------------------------------
