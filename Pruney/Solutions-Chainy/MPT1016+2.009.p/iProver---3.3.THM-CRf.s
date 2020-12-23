%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:52 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_3185)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

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
    inference(nnf_transformation,[],[f14])).

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

fof(f49,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK1(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

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
    inference(ennf_transformation,[],[f11])).

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
    inference(nnf_transformation,[],[f21])).

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

fof(f57,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f50,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK2(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | sK1(X0) != sK2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK4,X4) != k1_funct_1(sK4,X5)
      | ~ r2_hidden(X5,sK3)
      | ~ r2_hidden(X4,sK3)
      | v2_funct_1(sK4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

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

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

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

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    v1_funct_2(sK4,sK3,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f62,plain,
    ( r2_hidden(sK6,sK3)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f48,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,
    ( sK5 != sK6
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,
    ( r2_hidden(sK5,sK3)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_12,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_366,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_25])).

cnf(c_367,plain,
    ( r2_hidden(sK1(sK4),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | v2_funct_1(sK4) ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_2719,plain,
    ( r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_367])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_28,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_368,plain,
    ( r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_367])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2928,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2929,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2928])).

cnf(c_3406,plain,
    ( r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2719,c_28,c_368,c_2929])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2736,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4078,plain,
    ( r2_hidden(sK1(sK4),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3406,c_2736])).

cnf(c_26,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_51,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_53,plain,
    ( r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_51])).

cnf(c_11,plain,
    ( r2_hidden(sK2(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_54,plain,
    ( r2_hidden(sK2(X0),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_56,plain,
    ( r2_hidden(sK2(sK4),k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_57,plain,
    ( k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK1(X0))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_59,plain,
    ( k1_funct_1(sK4,sK2(sK4)) = k1_funct_1(sK4,sK1(sK4))
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | sK2(X0) != sK1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_60,plain,
    ( sK2(X0) != sK1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_62,plain,
    ( sK2(sK4) != sK1(sK4)
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_60])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X1,sK3)
    | v2_funct_1(sK4)
    | X1 = X0
    | k1_funct_1(sK4,X1) != k1_funct_1(sK4,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2997,plain,
    ( ~ r2_hidden(sK2(sK4),sK3)
    | ~ r2_hidden(sK1(sK4),sK3)
    | v2_funct_1(sK4)
    | k1_funct_1(sK4,sK2(sK4)) != k1_funct_1(sK4,sK1(sK4))
    | sK2(sK4) = sK1(sK4) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2998,plain,
    ( k1_funct_1(sK4,sK2(sK4)) != k1_funct_1(sK4,sK1(sK4))
    | sK2(sK4) = sK1(sK4)
    | r2_hidden(sK2(sK4),sK3) != iProver_top
    | r2_hidden(sK1(sK4),sK3) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2997])).

cnf(c_2977,plain,
    ( r2_hidden(sK1(sK4),X0)
    | ~ r2_hidden(sK1(sK4),k1_relat_1(sK4))
    | ~ r1_tarski(k1_relat_1(sK4),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3800,plain,
    ( ~ r2_hidden(sK1(sK4),k1_relat_1(sK4))
    | r2_hidden(sK1(sK4),sK3)
    | ~ r1_tarski(k1_relat_1(sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_2977])).

cnf(c_3803,plain,
    ( r2_hidden(sK1(sK4),k1_relat_1(sK4)) != iProver_top
    | r2_hidden(sK1(sK4),sK3) = iProver_top
    | r1_tarski(k1_relat_1(sK4),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3800])).

cnf(c_2987,plain,
    ( r2_hidden(sK2(sK4),X0)
    | ~ r2_hidden(sK2(sK4),k1_relat_1(sK4))
    | ~ r1_tarski(k1_relat_1(sK4),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3823,plain,
    ( ~ r2_hidden(sK2(sK4),k1_relat_1(sK4))
    | r2_hidden(sK2(sK4),sK3)
    | ~ r1_tarski(k1_relat_1(sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_2987])).

cnf(c_3826,plain,
    ( r2_hidden(sK2(sK4),k1_relat_1(sK4)) != iProver_top
    | r2_hidden(sK2(sK4),sK3) = iProver_top
    | r1_tarski(k1_relat_1(sK4),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3823])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3090,plain,
    ( ~ m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(X0))
    | r1_tarski(k1_relat_1(sK4),X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3930,plain,
    ( ~ m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK3))
    | r1_tarski(k1_relat_1(sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_3090])).

cnf(c_3936,plain,
    ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(k1_relat_1(sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3930])).

cnf(c_2722,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2728,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3645,plain,
    ( k1_relset_1(sK3,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2722,c_2728])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2729,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3946,plain,
    ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3645,c_2729])).

cnf(c_4738,plain,
    ( v2_funct_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4078,c_26,c_28,c_53,c_56,c_59,c_62,c_2929,c_2998,c_3803,c_3826,c_3936,c_3946])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK4,sK3,sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_337,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
    | sK3 != X2
    | sK3 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_338,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    | ~ r2_hidden(X0,sK3)
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_337])).

cnf(c_342,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ v2_funct_1(sK4)
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_338,c_25,c_23])).

cnf(c_2102,plain,
    ( ~ v2_funct_1(sK4)
    | sP1_iProver_split
    | k1_xboole_0 = sK3 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_342])).

cnf(c_2720,plain,
    ( k1_xboole_0 = sK3
    | v2_funct_1(sK4) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2102])).

cnf(c_4743,plain,
    ( sK3 = k1_xboole_0
    | sP1_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_4738,c_2720])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2737,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2101,plain,
    ( ~ r2_hidden(X0,sK3)
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_342])).

cnf(c_2721,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0
    | r2_hidden(X0,sK3) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2101])).

cnf(c_3516,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK0(sK3,X0))) = sK0(sK3,X0)
    | r1_tarski(sK3,X0) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2737,c_2721])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK6,sK3)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2725,plain,
    ( r2_hidden(sK6,sK3) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4076,plain,
    ( r2_hidden(sK6,X0) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2725,c_2736])).

cnf(c_33,plain,
    ( r2_hidden(sK6,sK3) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3155,plain,
    ( r2_hidden(sK6,X0)
    | ~ r2_hidden(sK6,sK3)
    | ~ r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3156,plain,
    ( r2_hidden(sK6,X0) = iProver_top
    | r2_hidden(sK6,sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3155])).

cnf(c_4239,plain,
    ( r1_tarski(sK3,X0) != iProver_top
    | r2_hidden(sK6,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4076,c_26,c_28,c_33,c_53,c_56,c_59,c_62,c_2929,c_2998,c_3156,c_3803,c_3826,c_3936,c_3946])).

cnf(c_4240,plain,
    ( r2_hidden(sK6,X0) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4239])).

cnf(c_5064,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK0(sK3,X0))) = sK0(sK3,X0)
    | r2_hidden(sK6,X0) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3516,c_4240])).

cnf(c_19,negated_conjecture,
    ( ~ v2_funct_1(sK4)
    | k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2726,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4747,plain,
    ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_4738,c_2726])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_418,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | X2 = X0
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_419,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ r2_hidden(X1,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v2_funct_1(sK4)
    | X0 = X1
    | k1_funct_1(sK4,X0) != k1_funct_1(sK4,X1) ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_2099,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ r2_hidden(X1,k1_relat_1(sK4))
    | X0 = X1
    | k1_funct_1(sK4,X0) != k1_funct_1(sK4,X1)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_419])).

cnf(c_2715,plain,
    ( X0 = X1
    | k1_funct_1(sK4,X0) != k1_funct_1(sK4,X1)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2099])).

cnf(c_4829,plain,
    ( k1_funct_1(sK4,X0) != k1_funct_1(sK4,sK5)
    | sK6 = X0
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(sK6,k1_relat_1(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_4747,c_2715])).

cnf(c_2100,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v2_funct_1(sK4)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_419])).

cnf(c_2132,plain,
    ( v1_relat_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2100])).

cnf(c_4933,plain,
    ( r2_hidden(sK6,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | sK6 = X0
    | k1_funct_1(sK4,X0) != k1_funct_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4829,c_26,c_28,c_53,c_56,c_59,c_62,c_2132,c_2929,c_2998,c_3803,c_3826,c_3936,c_3946])).

cnf(c_4934,plain,
    ( k1_funct_1(sK4,X0) != k1_funct_1(sK4,sK5)
    | sK6 = X0
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(sK6,k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4933])).

cnf(c_4945,plain,
    ( sK6 = sK5
    | r2_hidden(sK6,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(sK5,k1_relat_1(sK4)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4934])).

cnf(c_34,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( ~ v2_funct_1(sK4)
    | sK5 != sK6 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_35,plain,
    ( sK5 != sK6
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_73,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_77,plain,
    ( ~ r1_tarski(sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_405,plain,
    ( ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | sK2(X0) != sK1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_25])).

cnf(c_406,plain,
    ( ~ v1_relat_1(sK4)
    | v2_funct_1(sK4)
    | sK2(sK4) != sK1(sK4) ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_646,plain,
    ( ~ v1_relat_1(sK4)
    | sK2(sK4) != sK1(sK4)
    | sK6 != sK5 ),
    inference(resolution,[status(thm)],[c_406,c_18])).

cnf(c_392,plain,
    ( ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK1(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_25])).

cnf(c_393,plain,
    ( ~ v1_relat_1(sK4)
    | v2_funct_1(sK4)
    | k1_funct_1(sK4,sK2(sK4)) = k1_funct_1(sK4,sK1(sK4)) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_737,plain,
    ( ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK2(sK4))
    | sK6 != sK5 ),
    inference(resolution,[status(thm)],[c_393,c_18])).

cnf(c_379,plain,
    ( r2_hidden(sK2(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_25])).

cnf(c_380,plain,
    ( r2_hidden(sK2(sK4),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | v2_funct_1(sK4) ),
    inference(unflattening,[status(thm)],[c_379])).

cnf(c_828,plain,
    ( r2_hidden(sK2(sK4),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | sK6 != sK5 ),
    inference(resolution,[status(thm)],[c_380,c_18])).

cnf(c_919,plain,
    ( r2_hidden(sK1(sK4),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | sK6 != sK5 ),
    inference(resolution,[status(thm)],[c_367,c_18])).

cnf(c_2112,plain,
    ( X0 != X1
    | sK2(X0) = sK2(X1) ),
    theory(equality)).

cnf(c_2124,plain,
    ( sK2(sK4) = sK2(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2112])).

cnf(c_2105,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3002,plain,
    ( sK2(sK4) != X0
    | sK2(sK4) = sK1(sK4)
    | sK1(sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_2105])).

cnf(c_3124,plain,
    ( sK2(sK4) != sK2(sK4)
    | sK2(sK4) = sK1(sK4)
    | sK1(sK4) != sK2(sK4) ),
    inference(instantiation,[status(thm)],[c_3002])).

cnf(c_3147,plain,
    ( ~ r2_hidden(sK6,sK3)
    | ~ r2_hidden(sK5,sK3)
    | v2_funct_1(sK4)
    | k1_funct_1(sK4,sK5) != k1_funct_1(sK4,sK6)
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_3221,plain,
    ( ~ r2_hidden(sK2(sK4),k1_relat_1(sK4))
    | ~ r2_hidden(sK1(sK4),k1_relat_1(sK4))
    | ~ sP0_iProver_split
    | k1_funct_1(sK4,sK1(sK4)) != k1_funct_1(sK4,sK2(sK4))
    | sK1(sK4) = sK2(sK4) ),
    inference(instantiation,[status(thm)],[c_2099])).

cnf(c_2734,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4247,plain,
    ( r2_hidden(sK6,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2734,c_4240])).

cnf(c_4248,plain,
    ( r2_hidden(sK6,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4247])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(sK5,sK3)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2724,plain,
    ( r2_hidden(sK5,sK3) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4077,plain,
    ( r2_hidden(sK5,X0) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2724,c_2736])).

cnf(c_32,plain,
    ( r2_hidden(sK5,sK3) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3170,plain,
    ( r2_hidden(sK5,X0)
    | ~ r2_hidden(sK5,sK3)
    | ~ r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3171,plain,
    ( r2_hidden(sK5,X0) = iProver_top
    | r2_hidden(sK5,sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3170])).

cnf(c_4250,plain,
    ( r1_tarski(sK3,X0) != iProver_top
    | r2_hidden(sK5,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4077,c_26,c_28,c_32,c_53,c_56,c_59,c_62,c_2929,c_2998,c_3171,c_3803,c_3826,c_3936,c_3946])).

cnf(c_4251,plain,
    ( r2_hidden(sK5,X0) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4250])).

cnf(c_4258,plain,
    ( r2_hidden(sK5,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2734,c_4251])).

cnf(c_4259,plain,
    ( r2_hidden(sK5,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4258])).

cnf(c_5369,plain,
    ( r2_hidden(sK6,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(sK5,k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4945,c_26,c_28,c_34,c_35,c_53,c_56,c_59,c_62,c_2132,c_2929,c_2998,c_3185,c_3803,c_3826,c_3936,c_3946])).

cnf(c_5375,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK0(sK3,k1_relat_1(sK4)))) = sK0(sK3,k1_relat_1(sK4))
    | r2_hidden(sK5,k1_relat_1(sK4)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_5064,c_5369])).

cnf(c_5063,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK0(sK3,X0))) = sK0(sK3,X0)
    | r2_hidden(sK5,X0) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3516,c_4251])).

cnf(c_5381,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK0(sK3,k1_relat_1(sK4)))) = sK0(sK3,k1_relat_1(sK4))
    | sP1_iProver_split != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5375,c_5063])).

cnf(c_5383,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK0(sK3,k1_relat_1(sK4)))) = sK0(sK3,k1_relat_1(sK4))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4743,c_5381])).

cnf(c_4356,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK6)) = sK6
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_4247,c_2721])).

cnf(c_4812,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK6
    | sP1_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_4747,c_4356])).

cnf(c_5041,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK6
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4743,c_4812])).

cnf(c_4365,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK5
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_4258,c_2721])).

cnf(c_5042,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK5
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4743,c_4365])).

cnf(c_5421,plain,
    ( sK3 = k1_xboole_0
    | sK6 = sK5 ),
    inference(superposition,[status(thm)],[c_5041,c_5042])).

cnf(c_5480,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5383,c_26,c_23,c_28,c_34,c_35,c_53,c_56,c_59,c_62,c_73,c_77,c_646,c_737,c_828,c_919,c_2124,c_2100,c_2928,c_2929,c_2998,c_3124,c_3147,c_3221,c_3803,c_3826,c_3936,c_3946,c_4248,c_4259,c_5421])).

cnf(c_5494,plain,
    ( r2_hidden(sK6,X0) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5480,c_4240])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_69,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5908,plain,
    ( r2_hidden(sK6,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5494,c_69])).

cnf(c_5916,plain,
    ( r2_hidden(sK5,k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5908,c_5369])).

cnf(c_5493,plain,
    ( r2_hidden(sK5,X0) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5480,c_4251])).

cnf(c_5818,plain,
    ( r2_hidden(sK5,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5493,c_69])).

cnf(c_6489,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5916,c_5818])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:06:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.91/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.01  
% 2.91/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.91/1.01  
% 2.91/1.01  ------  iProver source info
% 2.91/1.01  
% 2.91/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.91/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.91/1.01  git: non_committed_changes: false
% 2.91/1.01  git: last_make_outside_of_git: false
% 2.91/1.01  
% 2.91/1.01  ------ 
% 2.91/1.01  
% 2.91/1.01  ------ Input Options
% 2.91/1.01  
% 2.91/1.01  --out_options                           all
% 2.91/1.01  --tptp_safe_out                         true
% 2.91/1.01  --problem_path                          ""
% 2.91/1.01  --include_path                          ""
% 2.91/1.01  --clausifier                            res/vclausify_rel
% 2.91/1.01  --clausifier_options                    --mode clausify
% 2.91/1.01  --stdin                                 false
% 2.91/1.01  --stats_out                             all
% 2.91/1.01  
% 2.91/1.01  ------ General Options
% 2.91/1.01  
% 2.91/1.01  --fof                                   false
% 2.91/1.01  --time_out_real                         305.
% 2.91/1.01  --time_out_virtual                      -1.
% 2.91/1.01  --symbol_type_check                     false
% 2.91/1.01  --clausify_out                          false
% 2.91/1.01  --sig_cnt_out                           false
% 2.91/1.01  --trig_cnt_out                          false
% 2.91/1.01  --trig_cnt_out_tolerance                1.
% 2.91/1.01  --trig_cnt_out_sk_spl                   false
% 2.91/1.01  --abstr_cl_out                          false
% 2.91/1.01  
% 2.91/1.01  ------ Global Options
% 2.91/1.01  
% 2.91/1.01  --schedule                              default
% 2.91/1.01  --add_important_lit                     false
% 2.91/1.01  --prop_solver_per_cl                    1000
% 2.91/1.01  --min_unsat_core                        false
% 2.91/1.01  --soft_assumptions                      false
% 2.91/1.01  --soft_lemma_size                       3
% 2.91/1.01  --prop_impl_unit_size                   0
% 2.91/1.01  --prop_impl_unit                        []
% 2.91/1.01  --share_sel_clauses                     true
% 2.91/1.01  --reset_solvers                         false
% 2.91/1.01  --bc_imp_inh                            [conj_cone]
% 2.91/1.01  --conj_cone_tolerance                   3.
% 2.91/1.01  --extra_neg_conj                        none
% 2.91/1.01  --large_theory_mode                     true
% 2.91/1.01  --prolific_symb_bound                   200
% 2.91/1.01  --lt_threshold                          2000
% 2.91/1.01  --clause_weak_htbl                      true
% 2.91/1.01  --gc_record_bc_elim                     false
% 2.91/1.01  
% 2.91/1.01  ------ Preprocessing Options
% 2.91/1.01  
% 2.91/1.01  --preprocessing_flag                    true
% 2.91/1.01  --time_out_prep_mult                    0.1
% 2.91/1.01  --splitting_mode                        input
% 2.91/1.01  --splitting_grd                         true
% 2.91/1.01  --splitting_cvd                         false
% 2.91/1.01  --splitting_cvd_svl                     false
% 2.91/1.01  --splitting_nvd                         32
% 2.91/1.01  --sub_typing                            true
% 2.91/1.01  --prep_gs_sim                           true
% 2.91/1.01  --prep_unflatten                        true
% 2.91/1.01  --prep_res_sim                          true
% 2.91/1.01  --prep_upred                            true
% 2.91/1.01  --prep_sem_filter                       exhaustive
% 2.91/1.01  --prep_sem_filter_out                   false
% 2.91/1.01  --pred_elim                             true
% 2.91/1.01  --res_sim_input                         true
% 2.91/1.01  --eq_ax_congr_red                       true
% 2.91/1.01  --pure_diseq_elim                       true
% 2.91/1.01  --brand_transform                       false
% 2.91/1.01  --non_eq_to_eq                          false
% 2.91/1.01  --prep_def_merge                        true
% 2.91/1.01  --prep_def_merge_prop_impl              false
% 2.91/1.01  --prep_def_merge_mbd                    true
% 2.91/1.01  --prep_def_merge_tr_red                 false
% 2.91/1.01  --prep_def_merge_tr_cl                  false
% 2.91/1.01  --smt_preprocessing                     true
% 2.91/1.01  --smt_ac_axioms                         fast
% 2.91/1.01  --preprocessed_out                      false
% 2.91/1.01  --preprocessed_stats                    false
% 2.91/1.01  
% 2.91/1.01  ------ Abstraction refinement Options
% 2.91/1.01  
% 2.91/1.01  --abstr_ref                             []
% 2.91/1.01  --abstr_ref_prep                        false
% 2.91/1.01  --abstr_ref_until_sat                   false
% 2.91/1.01  --abstr_ref_sig_restrict                funpre
% 2.91/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.91/1.01  --abstr_ref_under                       []
% 2.91/1.01  
% 2.91/1.01  ------ SAT Options
% 2.91/1.01  
% 2.91/1.01  --sat_mode                              false
% 2.91/1.01  --sat_fm_restart_options                ""
% 2.91/1.01  --sat_gr_def                            false
% 2.91/1.01  --sat_epr_types                         true
% 2.91/1.01  --sat_non_cyclic_types                  false
% 2.91/1.01  --sat_finite_models                     false
% 2.91/1.01  --sat_fm_lemmas                         false
% 2.91/1.01  --sat_fm_prep                           false
% 2.91/1.01  --sat_fm_uc_incr                        true
% 2.91/1.01  --sat_out_model                         small
% 2.91/1.01  --sat_out_clauses                       false
% 2.91/1.01  
% 2.91/1.01  ------ QBF Options
% 2.91/1.01  
% 2.91/1.01  --qbf_mode                              false
% 2.91/1.01  --qbf_elim_univ                         false
% 2.91/1.01  --qbf_dom_inst                          none
% 2.91/1.01  --qbf_dom_pre_inst                      false
% 2.91/1.01  --qbf_sk_in                             false
% 2.91/1.01  --qbf_pred_elim                         true
% 2.91/1.01  --qbf_split                             512
% 2.91/1.01  
% 2.91/1.01  ------ BMC1 Options
% 2.91/1.01  
% 2.91/1.01  --bmc1_incremental                      false
% 2.91/1.01  --bmc1_axioms                           reachable_all
% 2.91/1.01  --bmc1_min_bound                        0
% 2.91/1.01  --bmc1_max_bound                        -1
% 2.91/1.01  --bmc1_max_bound_default                -1
% 2.91/1.01  --bmc1_symbol_reachability              true
% 2.91/1.01  --bmc1_property_lemmas                  false
% 2.91/1.01  --bmc1_k_induction                      false
% 2.91/1.01  --bmc1_non_equiv_states                 false
% 2.91/1.01  --bmc1_deadlock                         false
% 2.91/1.01  --bmc1_ucm                              false
% 2.91/1.01  --bmc1_add_unsat_core                   none
% 2.91/1.01  --bmc1_unsat_core_children              false
% 2.91/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.91/1.01  --bmc1_out_stat                         full
% 2.91/1.01  --bmc1_ground_init                      false
% 2.91/1.01  --bmc1_pre_inst_next_state              false
% 2.91/1.01  --bmc1_pre_inst_state                   false
% 2.91/1.01  --bmc1_pre_inst_reach_state             false
% 2.91/1.01  --bmc1_out_unsat_core                   false
% 2.91/1.01  --bmc1_aig_witness_out                  false
% 2.91/1.01  --bmc1_verbose                          false
% 2.91/1.01  --bmc1_dump_clauses_tptp                false
% 2.91/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.91/1.01  --bmc1_dump_file                        -
% 2.91/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.91/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.91/1.01  --bmc1_ucm_extend_mode                  1
% 2.91/1.01  --bmc1_ucm_init_mode                    2
% 2.91/1.01  --bmc1_ucm_cone_mode                    none
% 2.91/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.91/1.01  --bmc1_ucm_relax_model                  4
% 2.91/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.91/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.91/1.01  --bmc1_ucm_layered_model                none
% 2.91/1.01  --bmc1_ucm_max_lemma_size               10
% 2.91/1.01  
% 2.91/1.01  ------ AIG Options
% 2.91/1.01  
% 2.91/1.01  --aig_mode                              false
% 2.91/1.01  
% 2.91/1.01  ------ Instantiation Options
% 2.91/1.01  
% 2.91/1.01  --instantiation_flag                    true
% 2.91/1.01  --inst_sos_flag                         false
% 2.91/1.01  --inst_sos_phase                        true
% 2.91/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.91/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.91/1.01  --inst_lit_sel_side                     num_symb
% 2.91/1.01  --inst_solver_per_active                1400
% 2.91/1.01  --inst_solver_calls_frac                1.
% 2.91/1.01  --inst_passive_queue_type               priority_queues
% 2.91/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.91/1.01  --inst_passive_queues_freq              [25;2]
% 2.91/1.01  --inst_dismatching                      true
% 2.91/1.01  --inst_eager_unprocessed_to_passive     true
% 2.91/1.01  --inst_prop_sim_given                   true
% 2.91/1.01  --inst_prop_sim_new                     false
% 2.91/1.01  --inst_subs_new                         false
% 2.91/1.01  --inst_eq_res_simp                      false
% 2.91/1.01  --inst_subs_given                       false
% 2.91/1.01  --inst_orphan_elimination               true
% 2.91/1.01  --inst_learning_loop_flag               true
% 2.91/1.01  --inst_learning_start                   3000
% 2.91/1.01  --inst_learning_factor                  2
% 2.91/1.01  --inst_start_prop_sim_after_learn       3
% 2.91/1.01  --inst_sel_renew                        solver
% 2.91/1.01  --inst_lit_activity_flag                true
% 2.91/1.01  --inst_restr_to_given                   false
% 2.91/1.01  --inst_activity_threshold               500
% 2.91/1.01  --inst_out_proof                        true
% 2.91/1.01  
% 2.91/1.01  ------ Resolution Options
% 2.91/1.01  
% 2.91/1.01  --resolution_flag                       true
% 2.91/1.01  --res_lit_sel                           adaptive
% 2.91/1.01  --res_lit_sel_side                      none
% 2.91/1.01  --res_ordering                          kbo
% 2.91/1.01  --res_to_prop_solver                    active
% 2.91/1.01  --res_prop_simpl_new                    false
% 2.91/1.01  --res_prop_simpl_given                  true
% 2.91/1.01  --res_passive_queue_type                priority_queues
% 2.91/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.91/1.01  --res_passive_queues_freq               [15;5]
% 2.91/1.01  --res_forward_subs                      full
% 2.91/1.01  --res_backward_subs                     full
% 2.91/1.01  --res_forward_subs_resolution           true
% 2.91/1.01  --res_backward_subs_resolution          true
% 2.91/1.01  --res_orphan_elimination                true
% 2.91/1.01  --res_time_limit                        2.
% 2.91/1.01  --res_out_proof                         true
% 2.91/1.01  
% 2.91/1.01  ------ Superposition Options
% 2.91/1.01  
% 2.91/1.01  --superposition_flag                    true
% 2.91/1.01  --sup_passive_queue_type                priority_queues
% 2.91/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.91/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.91/1.01  --demod_completeness_check              fast
% 2.91/1.01  --demod_use_ground                      true
% 2.91/1.01  --sup_to_prop_solver                    passive
% 2.91/1.01  --sup_prop_simpl_new                    true
% 2.91/1.01  --sup_prop_simpl_given                  true
% 2.91/1.01  --sup_fun_splitting                     false
% 2.91/1.01  --sup_smt_interval                      50000
% 2.91/1.01  
% 2.91/1.01  ------ Superposition Simplification Setup
% 2.91/1.01  
% 2.91/1.01  --sup_indices_passive                   []
% 2.91/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.91/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/1.01  --sup_full_bw                           [BwDemod]
% 2.91/1.01  --sup_immed_triv                        [TrivRules]
% 2.91/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.91/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/1.01  --sup_immed_bw_main                     []
% 2.91/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.91/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.91/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.91/1.01  
% 2.91/1.01  ------ Combination Options
% 2.91/1.01  
% 2.91/1.01  --comb_res_mult                         3
% 2.91/1.01  --comb_sup_mult                         2
% 2.91/1.01  --comb_inst_mult                        10
% 2.91/1.01  
% 2.91/1.01  ------ Debug Options
% 2.91/1.01  
% 2.91/1.01  --dbg_backtrace                         false
% 2.91/1.01  --dbg_dump_prop_clauses                 false
% 2.91/1.01  --dbg_dump_prop_clauses_file            -
% 2.91/1.01  --dbg_out_stat                          false
% 2.91/1.01  ------ Parsing...
% 2.91/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.91/1.01  
% 2.91/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.91/1.01  
% 2.91/1.01  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.91/1.01  
% 2.91/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.91/1.01  ------ Proving...
% 2.91/1.01  ------ Problem Properties 
% 2.91/1.01  
% 2.91/1.01  
% 2.91/1.01  clauses                                 25
% 2.91/1.01  conjectures                             6
% 2.91/1.01  EPR                                     9
% 2.91/1.01  Horn                                    19
% 2.91/1.01  unary                                   3
% 2.91/1.01  binary                                  11
% 2.91/1.01  lits                                    62
% 2.91/1.01  lits eq                                 12
% 2.91/1.01  fd_pure                                 0
% 2.91/1.01  fd_pseudo                               0
% 2.91/1.01  fd_cond                                 0
% 2.91/1.01  fd_pseudo_cond                          3
% 2.91/1.01  AC symbols                              0
% 2.91/1.01  
% 2.91/1.01  ------ Schedule dynamic 5 is on 
% 2.91/1.01  
% 2.91/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.91/1.01  
% 2.91/1.01  
% 2.91/1.01  ------ 
% 2.91/1.01  Current options:
% 2.91/1.01  ------ 
% 2.91/1.01  
% 2.91/1.01  ------ Input Options
% 2.91/1.01  
% 2.91/1.01  --out_options                           all
% 2.91/1.01  --tptp_safe_out                         true
% 2.91/1.01  --problem_path                          ""
% 2.91/1.01  --include_path                          ""
% 2.91/1.01  --clausifier                            res/vclausify_rel
% 2.91/1.01  --clausifier_options                    --mode clausify
% 2.91/1.01  --stdin                                 false
% 2.91/1.01  --stats_out                             all
% 2.91/1.01  
% 2.91/1.01  ------ General Options
% 2.91/1.01  
% 2.91/1.01  --fof                                   false
% 2.91/1.01  --time_out_real                         305.
% 2.91/1.01  --time_out_virtual                      -1.
% 2.91/1.01  --symbol_type_check                     false
% 2.91/1.01  --clausify_out                          false
% 2.91/1.01  --sig_cnt_out                           false
% 2.91/1.01  --trig_cnt_out                          false
% 2.91/1.01  --trig_cnt_out_tolerance                1.
% 2.91/1.01  --trig_cnt_out_sk_spl                   false
% 2.91/1.01  --abstr_cl_out                          false
% 2.91/1.01  
% 2.91/1.01  ------ Global Options
% 2.91/1.01  
% 2.91/1.01  --schedule                              default
% 2.91/1.01  --add_important_lit                     false
% 2.91/1.01  --prop_solver_per_cl                    1000
% 2.91/1.01  --min_unsat_core                        false
% 2.91/1.01  --soft_assumptions                      false
% 2.91/1.01  --soft_lemma_size                       3
% 2.91/1.01  --prop_impl_unit_size                   0
% 2.91/1.01  --prop_impl_unit                        []
% 2.91/1.01  --share_sel_clauses                     true
% 2.91/1.01  --reset_solvers                         false
% 2.91/1.01  --bc_imp_inh                            [conj_cone]
% 2.91/1.01  --conj_cone_tolerance                   3.
% 2.91/1.01  --extra_neg_conj                        none
% 2.91/1.01  --large_theory_mode                     true
% 2.91/1.01  --prolific_symb_bound                   200
% 2.91/1.01  --lt_threshold                          2000
% 2.91/1.01  --clause_weak_htbl                      true
% 2.91/1.01  --gc_record_bc_elim                     false
% 2.91/1.01  
% 2.91/1.01  ------ Preprocessing Options
% 2.91/1.01  
% 2.91/1.01  --preprocessing_flag                    true
% 2.91/1.01  --time_out_prep_mult                    0.1
% 2.91/1.01  --splitting_mode                        input
% 2.91/1.01  --splitting_grd                         true
% 2.91/1.01  --splitting_cvd                         false
% 2.91/1.01  --splitting_cvd_svl                     false
% 2.91/1.01  --splitting_nvd                         32
% 2.91/1.01  --sub_typing                            true
% 2.91/1.01  --prep_gs_sim                           true
% 2.91/1.01  --prep_unflatten                        true
% 2.91/1.01  --prep_res_sim                          true
% 2.91/1.01  --prep_upred                            true
% 2.91/1.01  --prep_sem_filter                       exhaustive
% 2.91/1.01  --prep_sem_filter_out                   false
% 2.91/1.01  --pred_elim                             true
% 2.91/1.01  --res_sim_input                         true
% 2.91/1.01  --eq_ax_congr_red                       true
% 2.91/1.01  --pure_diseq_elim                       true
% 2.91/1.01  --brand_transform                       false
% 2.91/1.01  --non_eq_to_eq                          false
% 2.91/1.01  --prep_def_merge                        true
% 2.91/1.01  --prep_def_merge_prop_impl              false
% 2.91/1.01  --prep_def_merge_mbd                    true
% 2.91/1.01  --prep_def_merge_tr_red                 false
% 2.91/1.01  --prep_def_merge_tr_cl                  false
% 2.91/1.01  --smt_preprocessing                     true
% 2.91/1.01  --smt_ac_axioms                         fast
% 2.91/1.01  --preprocessed_out                      false
% 2.91/1.01  --preprocessed_stats                    false
% 2.91/1.01  
% 2.91/1.01  ------ Abstraction refinement Options
% 2.91/1.01  
% 2.91/1.01  --abstr_ref                             []
% 2.91/1.01  --abstr_ref_prep                        false
% 2.91/1.01  --abstr_ref_until_sat                   false
% 2.91/1.01  --abstr_ref_sig_restrict                funpre
% 2.91/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.91/1.01  --abstr_ref_under                       []
% 2.91/1.01  
% 2.91/1.01  ------ SAT Options
% 2.91/1.01  
% 2.91/1.01  --sat_mode                              false
% 2.91/1.01  --sat_fm_restart_options                ""
% 2.91/1.01  --sat_gr_def                            false
% 2.91/1.01  --sat_epr_types                         true
% 2.91/1.01  --sat_non_cyclic_types                  false
% 2.91/1.01  --sat_finite_models                     false
% 2.91/1.01  --sat_fm_lemmas                         false
% 2.91/1.01  --sat_fm_prep                           false
% 2.91/1.01  --sat_fm_uc_incr                        true
% 2.91/1.01  --sat_out_model                         small
% 2.91/1.01  --sat_out_clauses                       false
% 2.91/1.01  
% 2.91/1.01  ------ QBF Options
% 2.91/1.01  
% 2.91/1.01  --qbf_mode                              false
% 2.91/1.01  --qbf_elim_univ                         false
% 2.91/1.01  --qbf_dom_inst                          none
% 2.91/1.01  --qbf_dom_pre_inst                      false
% 2.91/1.01  --qbf_sk_in                             false
% 2.91/1.01  --qbf_pred_elim                         true
% 2.91/1.01  --qbf_split                             512
% 2.91/1.01  
% 2.91/1.01  ------ BMC1 Options
% 2.91/1.01  
% 2.91/1.01  --bmc1_incremental                      false
% 2.91/1.01  --bmc1_axioms                           reachable_all
% 2.91/1.01  --bmc1_min_bound                        0
% 2.91/1.01  --bmc1_max_bound                        -1
% 2.91/1.01  --bmc1_max_bound_default                -1
% 2.91/1.01  --bmc1_symbol_reachability              true
% 2.91/1.01  --bmc1_property_lemmas                  false
% 2.91/1.01  --bmc1_k_induction                      false
% 2.91/1.01  --bmc1_non_equiv_states                 false
% 2.91/1.01  --bmc1_deadlock                         false
% 2.91/1.01  --bmc1_ucm                              false
% 2.91/1.01  --bmc1_add_unsat_core                   none
% 2.91/1.01  --bmc1_unsat_core_children              false
% 2.91/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.91/1.01  --bmc1_out_stat                         full
% 2.91/1.01  --bmc1_ground_init                      false
% 2.91/1.01  --bmc1_pre_inst_next_state              false
% 2.91/1.01  --bmc1_pre_inst_state                   false
% 2.91/1.01  --bmc1_pre_inst_reach_state             false
% 2.91/1.01  --bmc1_out_unsat_core                   false
% 2.91/1.01  --bmc1_aig_witness_out                  false
% 2.91/1.01  --bmc1_verbose                          false
% 2.91/1.01  --bmc1_dump_clauses_tptp                false
% 2.91/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.91/1.01  --bmc1_dump_file                        -
% 2.91/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.91/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.91/1.01  --bmc1_ucm_extend_mode                  1
% 2.91/1.01  --bmc1_ucm_init_mode                    2
% 2.91/1.01  --bmc1_ucm_cone_mode                    none
% 2.91/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.91/1.01  --bmc1_ucm_relax_model                  4
% 2.91/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.91/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.91/1.01  --bmc1_ucm_layered_model                none
% 2.91/1.01  --bmc1_ucm_max_lemma_size               10
% 2.91/1.01  
% 2.91/1.01  ------ AIG Options
% 2.91/1.01  
% 2.91/1.01  --aig_mode                              false
% 2.91/1.01  
% 2.91/1.01  ------ Instantiation Options
% 2.91/1.01  
% 2.91/1.01  --instantiation_flag                    true
% 2.91/1.01  --inst_sos_flag                         false
% 2.91/1.01  --inst_sos_phase                        true
% 2.91/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.91/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.91/1.01  --inst_lit_sel_side                     none
% 2.91/1.01  --inst_solver_per_active                1400
% 2.91/1.01  --inst_solver_calls_frac                1.
% 2.91/1.01  --inst_passive_queue_type               priority_queues
% 2.91/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.91/1.01  --inst_passive_queues_freq              [25;2]
% 2.91/1.01  --inst_dismatching                      true
% 2.91/1.01  --inst_eager_unprocessed_to_passive     true
% 2.91/1.01  --inst_prop_sim_given                   true
% 2.91/1.01  --inst_prop_sim_new                     false
% 2.91/1.01  --inst_subs_new                         false
% 2.91/1.01  --inst_eq_res_simp                      false
% 2.91/1.01  --inst_subs_given                       false
% 2.91/1.01  --inst_orphan_elimination               true
% 2.91/1.01  --inst_learning_loop_flag               true
% 2.91/1.01  --inst_learning_start                   3000
% 2.91/1.01  --inst_learning_factor                  2
% 2.91/1.01  --inst_start_prop_sim_after_learn       3
% 2.91/1.01  --inst_sel_renew                        solver
% 2.91/1.01  --inst_lit_activity_flag                true
% 2.91/1.01  --inst_restr_to_given                   false
% 2.91/1.01  --inst_activity_threshold               500
% 2.91/1.01  --inst_out_proof                        true
% 2.91/1.01  
% 2.91/1.01  ------ Resolution Options
% 2.91/1.01  
% 2.91/1.01  --resolution_flag                       false
% 2.91/1.01  --res_lit_sel                           adaptive
% 2.91/1.01  --res_lit_sel_side                      none
% 2.91/1.01  --res_ordering                          kbo
% 2.91/1.01  --res_to_prop_solver                    active
% 2.91/1.01  --res_prop_simpl_new                    false
% 2.91/1.01  --res_prop_simpl_given                  true
% 2.91/1.01  --res_passive_queue_type                priority_queues
% 2.91/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.91/1.01  --res_passive_queues_freq               [15;5]
% 2.91/1.01  --res_forward_subs                      full
% 2.91/1.01  --res_backward_subs                     full
% 2.91/1.01  --res_forward_subs_resolution           true
% 2.91/1.01  --res_backward_subs_resolution          true
% 2.91/1.01  --res_orphan_elimination                true
% 2.91/1.01  --res_time_limit                        2.
% 2.91/1.01  --res_out_proof                         true
% 2.91/1.01  
% 2.91/1.01  ------ Superposition Options
% 2.91/1.01  
% 2.91/1.01  --superposition_flag                    true
% 2.91/1.01  --sup_passive_queue_type                priority_queues
% 2.91/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.91/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.91/1.01  --demod_completeness_check              fast
% 2.91/1.01  --demod_use_ground                      true
% 2.91/1.01  --sup_to_prop_solver                    passive
% 2.91/1.01  --sup_prop_simpl_new                    true
% 2.91/1.01  --sup_prop_simpl_given                  true
% 2.91/1.01  --sup_fun_splitting                     false
% 2.91/1.01  --sup_smt_interval                      50000
% 2.91/1.01  
% 2.91/1.01  ------ Superposition Simplification Setup
% 2.91/1.01  
% 2.91/1.01  --sup_indices_passive                   []
% 2.91/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.91/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/1.01  --sup_full_bw                           [BwDemod]
% 2.91/1.01  --sup_immed_triv                        [TrivRules]
% 2.91/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.91/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/1.01  --sup_immed_bw_main                     []
% 2.91/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.91/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.91/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.91/1.01  
% 2.91/1.01  ------ Combination Options
% 2.91/1.01  
% 2.91/1.01  --comb_res_mult                         3
% 2.91/1.01  --comb_sup_mult                         2
% 2.91/1.01  --comb_inst_mult                        10
% 2.91/1.01  
% 2.91/1.01  ------ Debug Options
% 2.91/1.01  
% 2.91/1.01  --dbg_backtrace                         false
% 2.91/1.01  --dbg_dump_prop_clauses                 false
% 2.91/1.01  --dbg_dump_prop_clauses_file            -
% 2.91/1.01  --dbg_out_stat                          false
% 2.91/1.01  
% 2.91/1.01  
% 2.91/1.01  
% 2.91/1.01  
% 2.91/1.01  ------ Proving...
% 2.91/1.01  
% 2.91/1.01  
% 2.91/1.01  % SZS status Theorem for theBenchmark.p
% 2.91/1.01  
% 2.91/1.01   Resolution empty clause
% 2.91/1.01  
% 2.91/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.91/1.01  
% 2.91/1.01  fof(f5,axiom,(
% 2.91/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 2.91/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.91/1.01  
% 2.91/1.01  fof(f13,plain,(
% 2.91/1.01    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.91/1.01    inference(ennf_transformation,[],[f5])).
% 2.91/1.01  
% 2.91/1.01  fof(f14,plain,(
% 2.91/1.01    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.91/1.01    inference(flattening,[],[f13])).
% 2.91/1.01  
% 2.91/1.01  fof(f29,plain,(
% 2.91/1.01    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.91/1.01    inference(nnf_transformation,[],[f14])).
% 2.91/1.01  
% 2.91/1.01  fof(f30,plain,(
% 2.91/1.01    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.91/1.01    inference(rectify,[],[f29])).
% 2.91/1.01  
% 2.91/1.01  fof(f31,plain,(
% 2.91/1.01    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK1(X0) != sK2(X0) & k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0)) & r2_hidden(sK2(X0),k1_relat_1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0))))),
% 2.91/1.01    introduced(choice_axiom,[])).
% 2.91/1.01  
% 2.91/1.01  fof(f32,plain,(
% 2.91/1.01    ! [X0] : (((v2_funct_1(X0) | (sK1(X0) != sK2(X0) & k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0)) & r2_hidden(sK2(X0),k1_relat_1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.91/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f31])).
% 2.91/1.01  
% 2.91/1.01  fof(f49,plain,(
% 2.91/1.01    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK1(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.91/1.01    inference(cnf_transformation,[],[f32])).
% 2.91/1.01  
% 2.91/1.01  fof(f10,conjecture,(
% 2.91/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 2.91/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.91/1.01  
% 2.91/1.01  fof(f11,negated_conjecture,(
% 2.91/1.01    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 2.91/1.01    inference(negated_conjecture,[],[f10])).
% 2.91/1.01  
% 2.91/1.01  fof(f20,plain,(
% 2.91/1.01    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.91/1.01    inference(ennf_transformation,[],[f11])).
% 2.91/1.01  
% 2.91/1.01  fof(f21,plain,(
% 2.91/1.01    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.91/1.01    inference(flattening,[],[f20])).
% 2.91/1.01  
% 2.91/1.01  fof(f33,plain,(
% 2.91/1.01    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.91/1.01    inference(nnf_transformation,[],[f21])).
% 2.91/1.01  
% 2.91/1.01  fof(f34,plain,(
% 2.91/1.01    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.91/1.01    inference(flattening,[],[f33])).
% 2.91/1.01  
% 2.91/1.01  fof(f35,plain,(
% 2.91/1.01    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.91/1.01    inference(rectify,[],[f34])).
% 2.91/1.01  
% 2.91/1.01  fof(f37,plain,(
% 2.91/1.01    ( ! [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (sK5 != sK6 & k1_funct_1(X1,sK5) = k1_funct_1(X1,sK6) & r2_hidden(sK6,X0) & r2_hidden(sK5,X0))) )),
% 2.91/1.01    introduced(choice_axiom,[])).
% 2.91/1.01  
% 2.91/1.01  fof(f36,plain,(
% 2.91/1.01    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK4,X2) = k1_funct_1(sK4,X3) & r2_hidden(X3,sK3) & r2_hidden(X2,sK3)) | ~v2_funct_1(sK4)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK4,X4) != k1_funct_1(sK4,X5) | ~r2_hidden(X5,sK3) | ~r2_hidden(X4,sK3)) | v2_funct_1(sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) & v1_funct_2(sK4,sK3,sK3) & v1_funct_1(sK4))),
% 2.91/1.01    introduced(choice_axiom,[])).
% 2.91/1.01  
% 2.91/1.01  fof(f38,plain,(
% 2.91/1.01    ((sK5 != sK6 & k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) & r2_hidden(sK6,sK3) & r2_hidden(sK5,sK3)) | ~v2_funct_1(sK4)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK4,X4) != k1_funct_1(sK4,X5) | ~r2_hidden(X5,sK3) | ~r2_hidden(X4,sK3)) | v2_funct_1(sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) & v1_funct_2(sK4,sK3,sK3) & v1_funct_1(sK4)),
% 2.91/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f35,f37,f36])).
% 2.91/1.01  
% 2.91/1.01  fof(f57,plain,(
% 2.91/1.01    v1_funct_1(sK4)),
% 2.91/1.01    inference(cnf_transformation,[],[f38])).
% 2.91/1.01  
% 2.91/1.01  fof(f59,plain,(
% 2.91/1.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))),
% 2.91/1.01    inference(cnf_transformation,[],[f38])).
% 2.91/1.01  
% 2.91/1.01  fof(f6,axiom,(
% 2.91/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.91/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.91/1.01  
% 2.91/1.01  fof(f15,plain,(
% 2.91/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.91/1.01    inference(ennf_transformation,[],[f6])).
% 2.91/1.01  
% 2.91/1.01  fof(f53,plain,(
% 2.91/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.91/1.01    inference(cnf_transformation,[],[f15])).
% 2.91/1.01  
% 2.91/1.01  fof(f1,axiom,(
% 2.91/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.91/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.91/1.01  
% 2.91/1.01  fof(f12,plain,(
% 2.91/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.91/1.01    inference(ennf_transformation,[],[f1])).
% 2.91/1.01  
% 2.91/1.01  fof(f22,plain,(
% 2.91/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.91/1.01    inference(nnf_transformation,[],[f12])).
% 2.91/1.01  
% 2.91/1.01  fof(f23,plain,(
% 2.91/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.91/1.01    inference(rectify,[],[f22])).
% 2.91/1.01  
% 2.91/1.01  fof(f24,plain,(
% 2.91/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.91/1.01    introduced(choice_axiom,[])).
% 2.91/1.01  
% 2.91/1.01  fof(f25,plain,(
% 2.91/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.91/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 2.91/1.01  
% 2.91/1.01  fof(f39,plain,(
% 2.91/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.91/1.01    inference(cnf_transformation,[],[f25])).
% 2.91/1.01  
% 2.91/1.01  fof(f50,plain,(
% 2.91/1.01    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK2(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.91/1.01    inference(cnf_transformation,[],[f32])).
% 2.91/1.01  
% 2.91/1.01  fof(f51,plain,(
% 2.91/1.01    ( ! [X0] : (v2_funct_1(X0) | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.91/1.01    inference(cnf_transformation,[],[f32])).
% 2.91/1.01  
% 2.91/1.01  fof(f52,plain,(
% 2.91/1.01    ( ! [X0] : (v2_funct_1(X0) | sK1(X0) != sK2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.91/1.01    inference(cnf_transformation,[],[f32])).
% 2.91/1.01  
% 2.91/1.01  fof(f60,plain,(
% 2.91/1.01    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK4,X4) != k1_funct_1(sK4,X5) | ~r2_hidden(X5,sK3) | ~r2_hidden(X4,sK3) | v2_funct_1(sK4)) )),
% 2.91/1.01    inference(cnf_transformation,[],[f38])).
% 2.91/1.01  
% 2.91/1.01  fof(f4,axiom,(
% 2.91/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.91/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.91/1.01  
% 2.91/1.01  fof(f28,plain,(
% 2.91/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.91/1.01    inference(nnf_transformation,[],[f4])).
% 2.91/1.01  
% 2.91/1.01  fof(f46,plain,(
% 2.91/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.91/1.01    inference(cnf_transformation,[],[f28])).
% 2.91/1.01  
% 2.91/1.01  fof(f8,axiom,(
% 2.91/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.91/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.91/1.01  
% 2.91/1.01  fof(f17,plain,(
% 2.91/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.91/1.01    inference(ennf_transformation,[],[f8])).
% 2.91/1.01  
% 2.91/1.01  fof(f55,plain,(
% 2.91/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.91/1.01    inference(cnf_transformation,[],[f17])).
% 2.91/1.01  
% 2.91/1.01  fof(f7,axiom,(
% 2.91/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.91/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.91/1.01  
% 2.91/1.01  fof(f16,plain,(
% 2.91/1.01    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.91/1.01    inference(ennf_transformation,[],[f7])).
% 2.91/1.01  
% 2.91/1.01  fof(f54,plain,(
% 2.91/1.01    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.91/1.01    inference(cnf_transformation,[],[f16])).
% 2.91/1.01  
% 2.91/1.01  fof(f9,axiom,(
% 2.91/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 2.91/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.91/1.01  
% 2.91/1.01  fof(f18,plain,(
% 2.91/1.01    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.91/1.01    inference(ennf_transformation,[],[f9])).
% 2.91/1.01  
% 2.91/1.01  fof(f19,plain,(
% 2.91/1.01    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.91/1.01    inference(flattening,[],[f18])).
% 2.91/1.01  
% 2.91/1.01  fof(f56,plain,(
% 2.91/1.01    ( ! [X2,X0,X3,X1] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.91/1.01    inference(cnf_transformation,[],[f19])).
% 2.91/1.01  
% 2.91/1.01  fof(f58,plain,(
% 2.91/1.01    v1_funct_2(sK4,sK3,sK3)),
% 2.91/1.01    inference(cnf_transformation,[],[f38])).
% 2.91/1.01  
% 2.91/1.01  fof(f40,plain,(
% 2.91/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.91/1.01    inference(cnf_transformation,[],[f25])).
% 2.91/1.01  
% 2.91/1.01  fof(f62,plain,(
% 2.91/1.01    r2_hidden(sK6,sK3) | ~v2_funct_1(sK4)),
% 2.91/1.01    inference(cnf_transformation,[],[f38])).
% 2.91/1.01  
% 2.91/1.01  fof(f63,plain,(
% 2.91/1.01    k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) | ~v2_funct_1(sK4)),
% 2.91/1.01    inference(cnf_transformation,[],[f38])).
% 2.91/1.01  
% 2.91/1.01  fof(f48,plain,(
% 2.91/1.01    ( ! [X4,X0,X3] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.91/1.01    inference(cnf_transformation,[],[f32])).
% 2.91/1.01  
% 2.91/1.01  fof(f64,plain,(
% 2.91/1.01    sK5 != sK6 | ~v2_funct_1(sK4)),
% 2.91/1.01    inference(cnf_transformation,[],[f38])).
% 2.91/1.01  
% 2.91/1.01  fof(f2,axiom,(
% 2.91/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.91/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.91/1.01  
% 2.91/1.01  fof(f26,plain,(
% 2.91/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.91/1.01    inference(nnf_transformation,[],[f2])).
% 2.91/1.01  
% 2.91/1.01  fof(f27,plain,(
% 2.91/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.91/1.01    inference(flattening,[],[f26])).
% 2.91/1.01  
% 2.91/1.01  fof(f42,plain,(
% 2.91/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.91/1.01    inference(cnf_transformation,[],[f27])).
% 2.91/1.01  
% 2.91/1.01  fof(f66,plain,(
% 2.91/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.91/1.01    inference(equality_resolution,[],[f42])).
% 2.91/1.01  
% 2.91/1.01  fof(f44,plain,(
% 2.91/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.91/1.01    inference(cnf_transformation,[],[f27])).
% 2.91/1.01  
% 2.91/1.01  fof(f61,plain,(
% 2.91/1.01    r2_hidden(sK5,sK3) | ~v2_funct_1(sK4)),
% 2.91/1.01    inference(cnf_transformation,[],[f38])).
% 2.91/1.01  
% 2.91/1.01  fof(f3,axiom,(
% 2.91/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.91/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.91/1.01  
% 2.91/1.01  fof(f45,plain,(
% 2.91/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.91/1.01    inference(cnf_transformation,[],[f3])).
% 2.91/1.01  
% 2.91/1.01  cnf(c_12,plain,
% 2.91/1.01      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 2.91/1.01      | ~ v1_relat_1(X0)
% 2.91/1.01      | ~ v1_funct_1(X0)
% 2.91/1.01      | v2_funct_1(X0) ),
% 2.91/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_25,negated_conjecture,
% 2.91/1.01      ( v1_funct_1(sK4) ),
% 2.91/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_366,plain,
% 2.91/1.01      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 2.91/1.01      | ~ v1_relat_1(X0)
% 2.91/1.01      | v2_funct_1(X0)
% 2.91/1.01      | sK4 != X0 ),
% 2.91/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_25]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_367,plain,
% 2.91/1.01      ( r2_hidden(sK1(sK4),k1_relat_1(sK4))
% 2.91/1.01      | ~ v1_relat_1(sK4)
% 2.91/1.01      | v2_funct_1(sK4) ),
% 2.91/1.01      inference(unflattening,[status(thm)],[c_366]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_2719,plain,
% 2.91/1.01      ( r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top
% 2.91/1.01      | v1_relat_1(sK4) != iProver_top
% 2.91/1.01      | v2_funct_1(sK4) = iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_367]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_23,negated_conjecture,
% 2.91/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) ),
% 2.91/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_28,plain,
% 2.91/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) = iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_368,plain,
% 2.91/1.01      ( r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top
% 2.91/1.01      | v1_relat_1(sK4) != iProver_top
% 2.91/1.01      | v2_funct_1(sK4) = iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_367]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_14,plain,
% 2.91/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.91/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_2928,plain,
% 2.91/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
% 2.91/1.01      | v1_relat_1(sK4) ),
% 2.91/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_2929,plain,
% 2.91/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) != iProver_top
% 2.91/1.01      | v1_relat_1(sK4) = iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_2928]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_3406,plain,
% 2.91/1.01      ( r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top
% 2.91/1.01      | v2_funct_1(sK4) = iProver_top ),
% 2.91/1.01      inference(global_propositional_subsumption,
% 2.91/1.01                [status(thm)],
% 2.91/1.01                [c_2719,c_28,c_368,c_2929]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_2,plain,
% 2.91/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.91/1.01      inference(cnf_transformation,[],[f39]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_2736,plain,
% 2.91/1.01      ( r2_hidden(X0,X1) != iProver_top
% 2.91/1.01      | r2_hidden(X0,X2) = iProver_top
% 2.91/1.01      | r1_tarski(X1,X2) != iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_4078,plain,
% 2.91/1.01      ( r2_hidden(sK1(sK4),X0) = iProver_top
% 2.91/1.01      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 2.91/1.01      | v2_funct_1(sK4) = iProver_top ),
% 2.91/1.01      inference(superposition,[status(thm)],[c_3406,c_2736]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_26,plain,
% 2.91/1.01      ( v1_funct_1(sK4) = iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_51,plain,
% 2.91/1.01      ( r2_hidden(sK1(X0),k1_relat_1(X0)) = iProver_top
% 2.91/1.01      | v1_relat_1(X0) != iProver_top
% 2.91/1.01      | v1_funct_1(X0) != iProver_top
% 2.91/1.01      | v2_funct_1(X0) = iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_53,plain,
% 2.91/1.01      ( r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top
% 2.91/1.01      | v1_relat_1(sK4) != iProver_top
% 2.91/1.01      | v1_funct_1(sK4) != iProver_top
% 2.91/1.01      | v2_funct_1(sK4) = iProver_top ),
% 2.91/1.01      inference(instantiation,[status(thm)],[c_51]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_11,plain,
% 2.91/1.01      ( r2_hidden(sK2(X0),k1_relat_1(X0))
% 2.91/1.01      | ~ v1_relat_1(X0)
% 2.91/1.01      | ~ v1_funct_1(X0)
% 2.91/1.01      | v2_funct_1(X0) ),
% 2.91/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_54,plain,
% 2.91/1.01      ( r2_hidden(sK2(X0),k1_relat_1(X0)) = iProver_top
% 2.91/1.01      | v1_relat_1(X0) != iProver_top
% 2.91/1.01      | v1_funct_1(X0) != iProver_top
% 2.91/1.01      | v2_funct_1(X0) = iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_56,plain,
% 2.91/1.01      ( r2_hidden(sK2(sK4),k1_relat_1(sK4)) = iProver_top
% 2.91/1.01      | v1_relat_1(sK4) != iProver_top
% 2.91/1.01      | v1_funct_1(sK4) != iProver_top
% 2.91/1.01      | v2_funct_1(sK4) = iProver_top ),
% 2.91/1.01      inference(instantiation,[status(thm)],[c_54]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_10,plain,
% 2.91/1.01      ( ~ v1_relat_1(X0)
% 2.91/1.01      | ~ v1_funct_1(X0)
% 2.91/1.01      | v2_funct_1(X0)
% 2.91/1.01      | k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK1(X0)) ),
% 2.91/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_57,plain,
% 2.91/1.01      ( k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK1(X0))
% 2.91/1.01      | v1_relat_1(X0) != iProver_top
% 2.91/1.01      | v1_funct_1(X0) != iProver_top
% 2.91/1.01      | v2_funct_1(X0) = iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_59,plain,
% 2.91/1.01      ( k1_funct_1(sK4,sK2(sK4)) = k1_funct_1(sK4,sK1(sK4))
% 2.91/1.01      | v1_relat_1(sK4) != iProver_top
% 2.91/1.01      | v1_funct_1(sK4) != iProver_top
% 2.91/1.01      | v2_funct_1(sK4) = iProver_top ),
% 2.91/1.01      inference(instantiation,[status(thm)],[c_57]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_9,plain,
% 2.91/1.01      ( ~ v1_relat_1(X0)
% 2.91/1.01      | ~ v1_funct_1(X0)
% 2.91/1.01      | v2_funct_1(X0)
% 2.91/1.01      | sK2(X0) != sK1(X0) ),
% 2.91/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_60,plain,
% 2.91/1.01      ( sK2(X0) != sK1(X0)
% 2.91/1.01      | v1_relat_1(X0) != iProver_top
% 2.91/1.01      | v1_funct_1(X0) != iProver_top
% 2.91/1.01      | v2_funct_1(X0) = iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_62,plain,
% 2.91/1.01      ( sK2(sK4) != sK1(sK4)
% 2.91/1.01      | v1_relat_1(sK4) != iProver_top
% 2.91/1.01      | v1_funct_1(sK4) != iProver_top
% 2.91/1.01      | v2_funct_1(sK4) = iProver_top ),
% 2.91/1.01      inference(instantiation,[status(thm)],[c_60]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_22,negated_conjecture,
% 2.91/1.01      ( ~ r2_hidden(X0,sK3)
% 2.91/1.01      | ~ r2_hidden(X1,sK3)
% 2.91/1.01      | v2_funct_1(sK4)
% 2.91/1.01      | X1 = X0
% 2.91/1.01      | k1_funct_1(sK4,X1) != k1_funct_1(sK4,X0) ),
% 2.91/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_2997,plain,
% 2.91/1.01      ( ~ r2_hidden(sK2(sK4),sK3)
% 2.91/1.01      | ~ r2_hidden(sK1(sK4),sK3)
% 2.91/1.01      | v2_funct_1(sK4)
% 2.91/1.01      | k1_funct_1(sK4,sK2(sK4)) != k1_funct_1(sK4,sK1(sK4))
% 2.91/1.01      | sK2(sK4) = sK1(sK4) ),
% 2.91/1.01      inference(instantiation,[status(thm)],[c_22]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_2998,plain,
% 2.91/1.01      ( k1_funct_1(sK4,sK2(sK4)) != k1_funct_1(sK4,sK1(sK4))
% 2.91/1.01      | sK2(sK4) = sK1(sK4)
% 2.91/1.01      | r2_hidden(sK2(sK4),sK3) != iProver_top
% 2.91/1.01      | r2_hidden(sK1(sK4),sK3) != iProver_top
% 2.91/1.01      | v2_funct_1(sK4) = iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_2997]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_2977,plain,
% 2.91/1.01      ( r2_hidden(sK1(sK4),X0)
% 2.91/1.01      | ~ r2_hidden(sK1(sK4),k1_relat_1(sK4))
% 2.91/1.01      | ~ r1_tarski(k1_relat_1(sK4),X0) ),
% 2.91/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_3800,plain,
% 2.91/1.01      ( ~ r2_hidden(sK1(sK4),k1_relat_1(sK4))
% 2.91/1.01      | r2_hidden(sK1(sK4),sK3)
% 2.91/1.01      | ~ r1_tarski(k1_relat_1(sK4),sK3) ),
% 2.91/1.01      inference(instantiation,[status(thm)],[c_2977]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_3803,plain,
% 2.91/1.01      ( r2_hidden(sK1(sK4),k1_relat_1(sK4)) != iProver_top
% 2.91/1.01      | r2_hidden(sK1(sK4),sK3) = iProver_top
% 2.91/1.01      | r1_tarski(k1_relat_1(sK4),sK3) != iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_3800]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_2987,plain,
% 2.91/1.01      ( r2_hidden(sK2(sK4),X0)
% 2.91/1.01      | ~ r2_hidden(sK2(sK4),k1_relat_1(sK4))
% 2.91/1.01      | ~ r1_tarski(k1_relat_1(sK4),X0) ),
% 2.91/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_3823,plain,
% 2.91/1.01      ( ~ r2_hidden(sK2(sK4),k1_relat_1(sK4))
% 2.91/1.01      | r2_hidden(sK2(sK4),sK3)
% 2.91/1.01      | ~ r1_tarski(k1_relat_1(sK4),sK3) ),
% 2.91/1.01      inference(instantiation,[status(thm)],[c_2987]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_3826,plain,
% 2.91/1.01      ( r2_hidden(sK2(sK4),k1_relat_1(sK4)) != iProver_top
% 2.91/1.01      | r2_hidden(sK2(sK4),sK3) = iProver_top
% 2.91/1.01      | r1_tarski(k1_relat_1(sK4),sK3) != iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_3823]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_8,plain,
% 2.91/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.91/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_3090,plain,
% 2.91/1.01      ( ~ m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(X0))
% 2.91/1.01      | r1_tarski(k1_relat_1(sK4),X0) ),
% 2.91/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_3930,plain,
% 2.91/1.01      ( ~ m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK3))
% 2.91/1.01      | r1_tarski(k1_relat_1(sK4),sK3) ),
% 2.91/1.01      inference(instantiation,[status(thm)],[c_3090]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_3936,plain,
% 2.91/1.01      ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK3)) != iProver_top
% 2.91/1.01      | r1_tarski(k1_relat_1(sK4),sK3) = iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_3930]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_2722,plain,
% 2.91/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) = iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_16,plain,
% 2.91/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.91/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.91/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_2728,plain,
% 2.91/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.91/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_3645,plain,
% 2.91/1.01      ( k1_relset_1(sK3,sK3,sK4) = k1_relat_1(sK4) ),
% 2.91/1.01      inference(superposition,[status(thm)],[c_2722,c_2728]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_15,plain,
% 2.91/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.91/1.01      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 2.91/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_2729,plain,
% 2.91/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.91/1.01      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_3946,plain,
% 2.91/1.01      ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top
% 2.91/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) != iProver_top ),
% 2.91/1.01      inference(superposition,[status(thm)],[c_3645,c_2729]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_4738,plain,
% 2.91/1.01      ( v2_funct_1(sK4) = iProver_top ),
% 2.91/1.01      inference(global_propositional_subsumption,
% 2.91/1.01                [status(thm)],
% 2.91/1.01                [c_4078,c_26,c_28,c_53,c_56,c_59,c_62,c_2929,c_2998,c_3803,
% 2.91/1.01                 c_3826,c_3936,c_3946]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_17,plain,
% 2.91/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.91/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.91/1.01      | ~ r2_hidden(X3,X1)
% 2.91/1.01      | ~ v1_funct_1(X0)
% 2.91/1.01      | ~ v2_funct_1(X0)
% 2.91/1.01      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
% 2.91/1.01      | k1_xboole_0 = X2 ),
% 2.91/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_24,negated_conjecture,
% 2.91/1.01      ( v1_funct_2(sK4,sK3,sK3) ),
% 2.91/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_337,plain,
% 2.91/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.91/1.01      | ~ r2_hidden(X3,X1)
% 2.91/1.01      | ~ v1_funct_1(X0)
% 2.91/1.01      | ~ v2_funct_1(X0)
% 2.91/1.01      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
% 2.91/1.01      | sK3 != X2
% 2.91/1.01      | sK3 != X1
% 2.91/1.01      | sK4 != X0
% 2.91/1.01      | k1_xboole_0 = X2 ),
% 2.91/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_24]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_338,plain,
% 2.91/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
% 2.91/1.01      | ~ r2_hidden(X0,sK3)
% 2.91/1.01      | ~ v1_funct_1(sK4)
% 2.91/1.01      | ~ v2_funct_1(sK4)
% 2.91/1.01      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0
% 2.91/1.01      | k1_xboole_0 = sK3 ),
% 2.91/1.01      inference(unflattening,[status(thm)],[c_337]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_342,plain,
% 2.91/1.01      ( ~ r2_hidden(X0,sK3)
% 2.91/1.01      | ~ v2_funct_1(sK4)
% 2.91/1.01      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0
% 2.91/1.01      | k1_xboole_0 = sK3 ),
% 2.91/1.01      inference(global_propositional_subsumption,
% 2.91/1.01                [status(thm)],
% 2.91/1.01                [c_338,c_25,c_23]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_2102,plain,
% 2.91/1.01      ( ~ v2_funct_1(sK4) | sP1_iProver_split | k1_xboole_0 = sK3 ),
% 2.91/1.01      inference(splitting,
% 2.91/1.01                [splitting(split),new_symbols(definition,[])],
% 2.91/1.01                [c_342]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_2720,plain,
% 2.91/1.01      ( k1_xboole_0 = sK3
% 2.91/1.01      | v2_funct_1(sK4) != iProver_top
% 2.91/1.01      | sP1_iProver_split = iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_2102]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_4743,plain,
% 2.91/1.01      ( sK3 = k1_xboole_0 | sP1_iProver_split = iProver_top ),
% 2.91/1.01      inference(superposition,[status(thm)],[c_4738,c_2720]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_1,plain,
% 2.91/1.01      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.91/1.01      inference(cnf_transformation,[],[f40]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_2737,plain,
% 2.91/1.01      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.91/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_2101,plain,
% 2.91/1.01      ( ~ r2_hidden(X0,sK3)
% 2.91/1.01      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0
% 2.91/1.01      | ~ sP1_iProver_split ),
% 2.91/1.01      inference(splitting,
% 2.91/1.01                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.91/1.01                [c_342]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_2721,plain,
% 2.91/1.01      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0
% 2.91/1.01      | r2_hidden(X0,sK3) != iProver_top
% 2.91/1.01      | sP1_iProver_split != iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_2101]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_3516,plain,
% 2.91/1.01      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK0(sK3,X0))) = sK0(sK3,X0)
% 2.91/1.01      | r1_tarski(sK3,X0) = iProver_top
% 2.91/1.01      | sP1_iProver_split != iProver_top ),
% 2.91/1.01      inference(superposition,[status(thm)],[c_2737,c_2721]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_20,negated_conjecture,
% 2.91/1.01      ( r2_hidden(sK6,sK3) | ~ v2_funct_1(sK4) ),
% 2.91/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_2725,plain,
% 2.91/1.01      ( r2_hidden(sK6,sK3) = iProver_top | v2_funct_1(sK4) != iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_4076,plain,
% 2.91/1.01      ( r2_hidden(sK6,X0) = iProver_top
% 2.91/1.01      | r1_tarski(sK3,X0) != iProver_top
% 2.91/1.01      | v2_funct_1(sK4) != iProver_top ),
% 2.91/1.01      inference(superposition,[status(thm)],[c_2725,c_2736]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_33,plain,
% 2.91/1.01      ( r2_hidden(sK6,sK3) = iProver_top | v2_funct_1(sK4) != iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_3155,plain,
% 2.91/1.01      ( r2_hidden(sK6,X0) | ~ r2_hidden(sK6,sK3) | ~ r1_tarski(sK3,X0) ),
% 2.91/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_3156,plain,
% 2.91/1.01      ( r2_hidden(sK6,X0) = iProver_top
% 2.91/1.01      | r2_hidden(sK6,sK3) != iProver_top
% 2.91/1.01      | r1_tarski(sK3,X0) != iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_3155]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_4239,plain,
% 2.91/1.01      ( r1_tarski(sK3,X0) != iProver_top | r2_hidden(sK6,X0) = iProver_top ),
% 2.91/1.01      inference(global_propositional_subsumption,
% 2.91/1.01                [status(thm)],
% 2.91/1.01                [c_4076,c_26,c_28,c_33,c_53,c_56,c_59,c_62,c_2929,c_2998,
% 2.91/1.01                 c_3156,c_3803,c_3826,c_3936,c_3946]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_4240,plain,
% 2.91/1.01      ( r2_hidden(sK6,X0) = iProver_top | r1_tarski(sK3,X0) != iProver_top ),
% 2.91/1.01      inference(renaming,[status(thm)],[c_4239]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_5064,plain,
% 2.91/1.01      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK0(sK3,X0))) = sK0(sK3,X0)
% 2.91/1.01      | r2_hidden(sK6,X0) = iProver_top
% 2.91/1.01      | sP1_iProver_split != iProver_top ),
% 2.91/1.01      inference(superposition,[status(thm)],[c_3516,c_4240]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_19,negated_conjecture,
% 2.91/1.01      ( ~ v2_funct_1(sK4) | k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
% 2.91/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_2726,plain,
% 2.91/1.01      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
% 2.91/1.01      | v2_funct_1(sK4) != iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_4747,plain,
% 2.91/1.01      ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5) ),
% 2.91/1.01      inference(superposition,[status(thm)],[c_4738,c_2726]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_13,plain,
% 2.91/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.91/1.01      | ~ r2_hidden(X2,k1_relat_1(X1))
% 2.91/1.01      | ~ v1_relat_1(X1)
% 2.91/1.01      | ~ v1_funct_1(X1)
% 2.91/1.01      | ~ v2_funct_1(X1)
% 2.91/1.01      | X0 = X2
% 2.91/1.01      | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
% 2.91/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_418,plain,
% 2.91/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.91/1.01      | ~ r2_hidden(X2,k1_relat_1(X1))
% 2.91/1.01      | ~ v1_relat_1(X1)
% 2.91/1.01      | ~ v2_funct_1(X1)
% 2.91/1.01      | X2 = X0
% 2.91/1.01      | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
% 2.91/1.01      | sK4 != X1 ),
% 2.91/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_419,plain,
% 2.91/1.01      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.91/1.01      | ~ r2_hidden(X1,k1_relat_1(sK4))
% 2.91/1.01      | ~ v1_relat_1(sK4)
% 2.91/1.01      | ~ v2_funct_1(sK4)
% 2.91/1.01      | X0 = X1
% 2.91/1.01      | k1_funct_1(sK4,X0) != k1_funct_1(sK4,X1) ),
% 2.91/1.01      inference(unflattening,[status(thm)],[c_418]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_2099,plain,
% 2.91/1.01      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.91/1.01      | ~ r2_hidden(X1,k1_relat_1(sK4))
% 2.91/1.01      | X0 = X1
% 2.91/1.01      | k1_funct_1(sK4,X0) != k1_funct_1(sK4,X1)
% 2.91/1.01      | ~ sP0_iProver_split ),
% 2.91/1.01      inference(splitting,
% 2.91/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.91/1.01                [c_419]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_2715,plain,
% 2.91/1.01      ( X0 = X1
% 2.91/1.01      | k1_funct_1(sK4,X0) != k1_funct_1(sK4,X1)
% 2.91/1.01      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.91/1.01      | r2_hidden(X1,k1_relat_1(sK4)) != iProver_top
% 2.91/1.01      | sP0_iProver_split != iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_2099]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_4829,plain,
% 2.91/1.01      ( k1_funct_1(sK4,X0) != k1_funct_1(sK4,sK5)
% 2.91/1.01      | sK6 = X0
% 2.91/1.01      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.91/1.01      | r2_hidden(sK6,k1_relat_1(sK4)) != iProver_top
% 2.91/1.01      | sP0_iProver_split != iProver_top ),
% 2.91/1.01      inference(superposition,[status(thm)],[c_4747,c_2715]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_2100,plain,
% 2.91/1.01      ( ~ v1_relat_1(sK4) | ~ v2_funct_1(sK4) | sP0_iProver_split ),
% 2.91/1.01      inference(splitting,
% 2.91/1.01                [splitting(split),new_symbols(definition,[])],
% 2.91/1.01                [c_419]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_2132,plain,
% 2.91/1.01      ( v1_relat_1(sK4) != iProver_top
% 2.91/1.01      | v2_funct_1(sK4) != iProver_top
% 2.91/1.01      | sP0_iProver_split = iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_2100]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_4933,plain,
% 2.91/1.01      ( r2_hidden(sK6,k1_relat_1(sK4)) != iProver_top
% 2.91/1.01      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.91/1.01      | sK6 = X0
% 2.91/1.01      | k1_funct_1(sK4,X0) != k1_funct_1(sK4,sK5) ),
% 2.91/1.01      inference(global_propositional_subsumption,
% 2.91/1.01                [status(thm)],
% 2.91/1.01                [c_4829,c_26,c_28,c_53,c_56,c_59,c_62,c_2132,c_2929,c_2998,
% 2.91/1.01                 c_3803,c_3826,c_3936,c_3946]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_4934,plain,
% 2.91/1.01      ( k1_funct_1(sK4,X0) != k1_funct_1(sK4,sK5)
% 2.91/1.01      | sK6 = X0
% 2.91/1.01      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.91/1.01      | r2_hidden(sK6,k1_relat_1(sK4)) != iProver_top ),
% 2.91/1.01      inference(renaming,[status(thm)],[c_4933]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_4945,plain,
% 2.91/1.01      ( sK6 = sK5
% 2.91/1.01      | r2_hidden(sK6,k1_relat_1(sK4)) != iProver_top
% 2.91/1.01      | r2_hidden(sK5,k1_relat_1(sK4)) != iProver_top ),
% 2.91/1.01      inference(equality_resolution,[status(thm)],[c_4934]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_34,plain,
% 2.91/1.01      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
% 2.91/1.01      | v2_funct_1(sK4) != iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_18,negated_conjecture,
% 2.91/1.01      ( ~ v2_funct_1(sK4) | sK5 != sK6 ),
% 2.91/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_35,plain,
% 2.91/1.01      ( sK5 != sK6 | v2_funct_1(sK4) != iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_5,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f66]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_73,plain,
% 2.91/1.01      ( r1_tarski(sK4,sK4) ),
% 2.91/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_3,plain,
% 2.91/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.91/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_77,plain,
% 2.91/1.01      ( ~ r1_tarski(sK4,sK4) | sK4 = sK4 ),
% 2.91/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_405,plain,
% 2.91/1.01      ( ~ v1_relat_1(X0) | v2_funct_1(X0) | sK2(X0) != sK1(X0) | sK4 != X0 ),
% 2.91/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_25]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_406,plain,
% 2.91/1.01      ( ~ v1_relat_1(sK4) | v2_funct_1(sK4) | sK2(sK4) != sK1(sK4) ),
% 2.91/1.01      inference(unflattening,[status(thm)],[c_405]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_646,plain,
% 2.91/1.01      ( ~ v1_relat_1(sK4) | sK2(sK4) != sK1(sK4) | sK6 != sK5 ),
% 2.91/1.01      inference(resolution,[status(thm)],[c_406,c_18]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_392,plain,
% 2.91/1.01      ( ~ v1_relat_1(X0)
% 2.91/1.01      | v2_funct_1(X0)
% 2.91/1.01      | k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK1(X0))
% 2.91/1.01      | sK4 != X0 ),
% 2.91/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_25]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_393,plain,
% 2.91/1.01      ( ~ v1_relat_1(sK4)
% 2.91/1.01      | v2_funct_1(sK4)
% 2.91/1.01      | k1_funct_1(sK4,sK2(sK4)) = k1_funct_1(sK4,sK1(sK4)) ),
% 2.91/1.01      inference(unflattening,[status(thm)],[c_392]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_737,plain,
% 2.91/1.01      ( ~ v1_relat_1(sK4)
% 2.91/1.01      | k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK2(sK4))
% 2.91/1.01      | sK6 != sK5 ),
% 2.91/1.01      inference(resolution,[status(thm)],[c_393,c_18]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_379,plain,
% 2.91/1.01      ( r2_hidden(sK2(X0),k1_relat_1(X0))
% 2.91/1.01      | ~ v1_relat_1(X0)
% 2.91/1.01      | v2_funct_1(X0)
% 2.91/1.01      | sK4 != X0 ),
% 2.91/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_25]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_380,plain,
% 2.91/1.01      ( r2_hidden(sK2(sK4),k1_relat_1(sK4))
% 2.91/1.01      | ~ v1_relat_1(sK4)
% 2.91/1.01      | v2_funct_1(sK4) ),
% 2.91/1.01      inference(unflattening,[status(thm)],[c_379]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_828,plain,
% 2.91/1.01      ( r2_hidden(sK2(sK4),k1_relat_1(sK4)) | ~ v1_relat_1(sK4) | sK6 != sK5 ),
% 2.91/1.01      inference(resolution,[status(thm)],[c_380,c_18]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_919,plain,
% 2.91/1.01      ( r2_hidden(sK1(sK4),k1_relat_1(sK4)) | ~ v1_relat_1(sK4) | sK6 != sK5 ),
% 2.91/1.01      inference(resolution,[status(thm)],[c_367,c_18]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_2112,plain,( X0 != X1 | sK2(X0) = sK2(X1) ),theory(equality) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_2124,plain,
% 2.91/1.01      ( sK2(sK4) = sK2(sK4) | sK4 != sK4 ),
% 2.91/1.01      inference(instantiation,[status(thm)],[c_2112]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_2105,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_3002,plain,
% 2.91/1.01      ( sK2(sK4) != X0 | sK2(sK4) = sK1(sK4) | sK1(sK4) != X0 ),
% 2.91/1.01      inference(instantiation,[status(thm)],[c_2105]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_3124,plain,
% 2.91/1.01      ( sK2(sK4) != sK2(sK4) | sK2(sK4) = sK1(sK4) | sK1(sK4) != sK2(sK4) ),
% 2.91/1.01      inference(instantiation,[status(thm)],[c_3002]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_3147,plain,
% 2.91/1.01      ( ~ r2_hidden(sK6,sK3)
% 2.91/1.01      | ~ r2_hidden(sK5,sK3)
% 2.91/1.01      | v2_funct_1(sK4)
% 2.91/1.01      | k1_funct_1(sK4,sK5) != k1_funct_1(sK4,sK6)
% 2.91/1.01      | sK5 = sK6 ),
% 2.91/1.01      inference(instantiation,[status(thm)],[c_22]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_3221,plain,
% 2.91/1.01      ( ~ r2_hidden(sK2(sK4),k1_relat_1(sK4))
% 2.91/1.01      | ~ r2_hidden(sK1(sK4),k1_relat_1(sK4))
% 2.91/1.01      | ~ sP0_iProver_split
% 2.91/1.01      | k1_funct_1(sK4,sK1(sK4)) != k1_funct_1(sK4,sK2(sK4))
% 2.91/1.01      | sK1(sK4) = sK2(sK4) ),
% 2.91/1.01      inference(instantiation,[status(thm)],[c_2099]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_2734,plain,
% 2.91/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_4247,plain,
% 2.91/1.01      ( r2_hidden(sK6,sK3) = iProver_top ),
% 2.91/1.01      inference(superposition,[status(thm)],[c_2734,c_4240]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_4248,plain,
% 2.91/1.01      ( r2_hidden(sK6,sK3) ),
% 2.91/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_4247]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_21,negated_conjecture,
% 2.91/1.01      ( r2_hidden(sK5,sK3) | ~ v2_funct_1(sK4) ),
% 2.91/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_2724,plain,
% 2.91/1.01      ( r2_hidden(sK5,sK3) = iProver_top | v2_funct_1(sK4) != iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_4077,plain,
% 2.91/1.01      ( r2_hidden(sK5,X0) = iProver_top
% 2.91/1.01      | r1_tarski(sK3,X0) != iProver_top
% 2.91/1.01      | v2_funct_1(sK4) != iProver_top ),
% 2.91/1.01      inference(superposition,[status(thm)],[c_2724,c_2736]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_32,plain,
% 2.91/1.01      ( r2_hidden(sK5,sK3) = iProver_top | v2_funct_1(sK4) != iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_3170,plain,
% 2.91/1.01      ( r2_hidden(sK5,X0) | ~ r2_hidden(sK5,sK3) | ~ r1_tarski(sK3,X0) ),
% 2.91/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_3171,plain,
% 2.91/1.01      ( r2_hidden(sK5,X0) = iProver_top
% 2.91/1.01      | r2_hidden(sK5,sK3) != iProver_top
% 2.91/1.01      | r1_tarski(sK3,X0) != iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_3170]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_4250,plain,
% 2.91/1.01      ( r1_tarski(sK3,X0) != iProver_top | r2_hidden(sK5,X0) = iProver_top ),
% 2.91/1.01      inference(global_propositional_subsumption,
% 2.91/1.01                [status(thm)],
% 2.91/1.01                [c_4077,c_26,c_28,c_32,c_53,c_56,c_59,c_62,c_2929,c_2998,
% 2.91/1.01                 c_3171,c_3803,c_3826,c_3936,c_3946]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_4251,plain,
% 2.91/1.01      ( r2_hidden(sK5,X0) = iProver_top | r1_tarski(sK3,X0) != iProver_top ),
% 2.91/1.01      inference(renaming,[status(thm)],[c_4250]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_4258,plain,
% 2.91/1.01      ( r2_hidden(sK5,sK3) = iProver_top ),
% 2.91/1.01      inference(superposition,[status(thm)],[c_2734,c_4251]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_4259,plain,
% 2.91/1.01      ( r2_hidden(sK5,sK3) ),
% 2.91/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_4258]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_5369,plain,
% 2.91/1.01      ( r2_hidden(sK6,k1_relat_1(sK4)) != iProver_top
% 2.91/1.01      | r2_hidden(sK5,k1_relat_1(sK4)) != iProver_top ),
% 2.91/1.01      inference(global_propositional_subsumption,
% 2.91/1.01                [status(thm)],
% 2.91/1.01                [c_4945,c_26,c_28,c_34,c_35,c_53,c_56,c_59,c_62,c_2132,
% 2.91/1.01                 c_2929,c_2998,c_3185,c_3803,c_3826,c_3936,c_3946]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_5375,plain,
% 2.91/1.01      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK0(sK3,k1_relat_1(sK4)))) = sK0(sK3,k1_relat_1(sK4))
% 2.91/1.01      | r2_hidden(sK5,k1_relat_1(sK4)) != iProver_top
% 2.91/1.01      | sP1_iProver_split != iProver_top ),
% 2.91/1.01      inference(superposition,[status(thm)],[c_5064,c_5369]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_5063,plain,
% 2.91/1.01      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK0(sK3,X0))) = sK0(sK3,X0)
% 2.91/1.01      | r2_hidden(sK5,X0) = iProver_top
% 2.91/1.01      | sP1_iProver_split != iProver_top ),
% 2.91/1.01      inference(superposition,[status(thm)],[c_3516,c_4251]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_5381,plain,
% 2.91/1.01      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK0(sK3,k1_relat_1(sK4)))) = sK0(sK3,k1_relat_1(sK4))
% 2.91/1.01      | sP1_iProver_split != iProver_top ),
% 2.91/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_5375,c_5063]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_5383,plain,
% 2.91/1.01      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK0(sK3,k1_relat_1(sK4)))) = sK0(sK3,k1_relat_1(sK4))
% 2.91/1.01      | sK3 = k1_xboole_0 ),
% 2.91/1.01      inference(superposition,[status(thm)],[c_4743,c_5381]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_4356,plain,
% 2.91/1.01      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK6)) = sK6
% 2.91/1.01      | sP1_iProver_split != iProver_top ),
% 2.91/1.01      inference(superposition,[status(thm)],[c_4247,c_2721]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_4812,plain,
% 2.91/1.01      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK6
% 2.91/1.01      | sP1_iProver_split != iProver_top ),
% 2.91/1.01      inference(demodulation,[status(thm)],[c_4747,c_4356]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_5041,plain,
% 2.91/1.01      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK6
% 2.91/1.01      | sK3 = k1_xboole_0 ),
% 2.91/1.01      inference(superposition,[status(thm)],[c_4743,c_4812]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_4365,plain,
% 2.91/1.01      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK5
% 2.91/1.01      | sP1_iProver_split != iProver_top ),
% 2.91/1.01      inference(superposition,[status(thm)],[c_4258,c_2721]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_5042,plain,
% 2.91/1.01      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK5
% 2.91/1.01      | sK3 = k1_xboole_0 ),
% 2.91/1.01      inference(superposition,[status(thm)],[c_4743,c_4365]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_5421,plain,
% 2.91/1.01      ( sK3 = k1_xboole_0 | sK6 = sK5 ),
% 2.91/1.01      inference(superposition,[status(thm)],[c_5041,c_5042]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_5480,plain,
% 2.91/1.01      ( sK3 = k1_xboole_0 ),
% 2.91/1.01      inference(global_propositional_subsumption,
% 2.91/1.01                [status(thm)],
% 2.91/1.01                [c_5383,c_26,c_23,c_28,c_34,c_35,c_53,c_56,c_59,c_62,c_73,
% 2.91/1.01                 c_77,c_646,c_737,c_828,c_919,c_2124,c_2100,c_2928,c_2929,
% 2.91/1.01                 c_2998,c_3124,c_3147,c_3221,c_3803,c_3826,c_3936,c_3946,
% 2.91/1.01                 c_4248,c_4259,c_5421]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_5494,plain,
% 2.91/1.01      ( r2_hidden(sK6,X0) = iProver_top
% 2.91/1.01      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 2.91/1.01      inference(demodulation,[status(thm)],[c_5480,c_4240]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_6,plain,
% 2.91/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 2.91/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_69,plain,
% 2.91/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.91/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_5908,plain,
% 2.91/1.01      ( r2_hidden(sK6,X0) = iProver_top ),
% 2.91/1.01      inference(global_propositional_subsumption,[status(thm)],[c_5494,c_69]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_5916,plain,
% 2.91/1.01      ( r2_hidden(sK5,k1_relat_1(sK4)) != iProver_top ),
% 2.91/1.01      inference(superposition,[status(thm)],[c_5908,c_5369]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_5493,plain,
% 2.91/1.01      ( r2_hidden(sK5,X0) = iProver_top
% 2.91/1.01      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 2.91/1.01      inference(demodulation,[status(thm)],[c_5480,c_4251]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_5818,plain,
% 2.91/1.01      ( r2_hidden(sK5,X0) = iProver_top ),
% 2.91/1.01      inference(global_propositional_subsumption,[status(thm)],[c_5493,c_69]) ).
% 2.91/1.01  
% 2.91/1.01  cnf(c_6489,plain,
% 2.91/1.01      ( $false ),
% 2.91/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_5916,c_5818]) ).
% 2.91/1.01  
% 2.91/1.01  
% 2.91/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.91/1.01  
% 2.91/1.01  ------                               Statistics
% 2.91/1.01  
% 2.91/1.01  ------ General
% 2.91/1.01  
% 2.91/1.01  abstr_ref_over_cycles:                  0
% 2.91/1.01  abstr_ref_under_cycles:                 0
% 2.91/1.01  gc_basic_clause_elim:                   0
% 2.91/1.01  forced_gc_time:                         0
% 2.91/1.01  parsing_time:                           0.007
% 2.91/1.01  unif_index_cands_time:                  0.
% 2.91/1.01  unif_index_add_time:                    0.
% 2.91/1.01  orderings_time:                         0.
% 2.91/1.01  out_proof_time:                         0.013
% 2.91/1.01  total_time:                             0.156
% 2.91/1.01  num_of_symbols:                         54
% 2.91/1.01  num_of_terms:                           3674
% 2.91/1.01  
% 2.91/1.01  ------ Preprocessing
% 2.91/1.01  
% 2.91/1.01  num_of_splits:                          2
% 2.91/1.01  num_of_split_atoms:                     2
% 2.91/1.01  num_of_reused_defs:                     0
% 2.91/1.01  num_eq_ax_congr_red:                    23
% 2.91/1.01  num_of_sem_filtered_clauses:            1
% 2.91/1.01  num_of_subtypes:                        0
% 2.91/1.01  monotx_restored_types:                  0
% 2.91/1.01  sat_num_of_epr_types:                   0
% 2.91/1.01  sat_num_of_non_cyclic_types:            0
% 2.91/1.01  sat_guarded_non_collapsed_types:        0
% 2.91/1.01  num_pure_diseq_elim:                    0
% 2.91/1.01  simp_replaced_by:                       0
% 2.91/1.01  res_preprocessed:                       127
% 2.91/1.01  prep_upred:                             0
% 2.91/1.01  prep_unflattend:                        18
% 2.91/1.01  smt_new_axioms:                         0
% 2.91/1.01  pred_elim_cands:                        5
% 2.91/1.01  pred_elim:                              2
% 2.91/1.01  pred_elim_cl:                           2
% 2.91/1.01  pred_elim_cycles:                       6
% 2.91/1.01  merged_defs:                            8
% 2.91/1.01  merged_defs_ncl:                        0
% 2.91/1.01  bin_hyper_res:                          8
% 2.91/1.01  prep_cycles:                            4
% 2.91/1.01  pred_elim_time:                         0.015
% 2.91/1.01  splitting_time:                         0.
% 2.91/1.01  sem_filter_time:                        0.
% 2.91/1.01  monotx_time:                            0.
% 2.91/1.01  subtype_inf_time:                       0.
% 2.91/1.01  
% 2.91/1.01  ------ Problem properties
% 2.91/1.01  
% 2.91/1.01  clauses:                                25
% 2.91/1.01  conjectures:                            6
% 2.91/1.01  epr:                                    9
% 2.91/1.01  horn:                                   19
% 2.91/1.01  ground:                                 11
% 2.91/1.01  unary:                                  3
% 2.91/1.01  binary:                                 11
% 2.91/1.01  lits:                                   62
% 2.91/1.01  lits_eq:                                12
% 2.91/1.01  fd_pure:                                0
% 2.91/1.01  fd_pseudo:                              0
% 2.91/1.01  fd_cond:                                0
% 2.91/1.01  fd_pseudo_cond:                         3
% 2.91/1.01  ac_symbols:                             0
% 2.91/1.01  
% 2.91/1.01  ------ Propositional Solver
% 2.91/1.01  
% 2.91/1.01  prop_solver_calls:                      29
% 2.91/1.01  prop_fast_solver_calls:                 1200
% 2.91/1.01  smt_solver_calls:                       0
% 2.91/1.01  smt_fast_solver_calls:                  0
% 2.91/1.01  prop_num_of_clauses:                    1881
% 2.91/1.01  prop_preprocess_simplified:             5571
% 2.91/1.01  prop_fo_subsumed:                       29
% 2.91/1.01  prop_solver_time:                       0.
% 2.91/1.01  smt_solver_time:                        0.
% 2.91/1.01  smt_fast_solver_time:                   0.
% 2.91/1.01  prop_fast_solver_time:                  0.
% 2.91/1.01  prop_unsat_core_time:                   0.
% 2.91/1.01  
% 2.91/1.01  ------ QBF
% 2.91/1.01  
% 2.91/1.01  qbf_q_res:                              0
% 2.91/1.01  qbf_num_tautologies:                    0
% 2.91/1.01  qbf_prep_cycles:                        0
% 2.91/1.01  
% 2.91/1.01  ------ BMC1
% 2.91/1.01  
% 2.91/1.01  bmc1_current_bound:                     -1
% 2.91/1.01  bmc1_last_solved_bound:                 -1
% 2.91/1.01  bmc1_unsat_core_size:                   -1
% 2.91/1.01  bmc1_unsat_core_parents_size:           -1
% 2.91/1.01  bmc1_merge_next_fun:                    0
% 2.91/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.91/1.01  
% 2.91/1.01  ------ Instantiation
% 2.91/1.01  
% 2.91/1.01  inst_num_of_clauses:                    492
% 2.91/1.01  inst_num_in_passive:                    60
% 2.91/1.01  inst_num_in_active:                     279
% 2.91/1.01  inst_num_in_unprocessed:                154
% 2.91/1.01  inst_num_of_loops:                      410
% 2.91/1.01  inst_num_of_learning_restarts:          0
% 2.91/1.01  inst_num_moves_active_passive:          127
% 2.91/1.01  inst_lit_activity:                      0
% 2.91/1.01  inst_lit_activity_moves:                0
% 2.91/1.01  inst_num_tautologies:                   0
% 2.91/1.01  inst_num_prop_implied:                  0
% 2.91/1.01  inst_num_existing_simplified:           0
% 2.91/1.01  inst_num_eq_res_simplified:             0
% 2.91/1.01  inst_num_child_elim:                    0
% 2.91/1.01  inst_num_of_dismatching_blockings:      89
% 2.91/1.01  inst_num_of_non_proper_insts:           402
% 2.91/1.01  inst_num_of_duplicates:                 0
% 2.91/1.01  inst_inst_num_from_inst_to_res:         0
% 2.91/1.01  inst_dismatching_checking_time:         0.
% 2.91/1.01  
% 2.91/1.01  ------ Resolution
% 2.91/1.01  
% 2.91/1.01  res_num_of_clauses:                     0
% 2.91/1.01  res_num_in_passive:                     0
% 2.91/1.01  res_num_in_active:                      0
% 2.91/1.01  res_num_of_loops:                       131
% 2.91/1.01  res_forward_subset_subsumed:            43
% 2.91/1.01  res_backward_subset_subsumed:           2
% 2.91/1.01  res_forward_subsumed:                   0
% 2.91/1.01  res_backward_subsumed:                  0
% 2.91/1.01  res_forward_subsumption_resolution:     0
% 2.91/1.01  res_backward_subsumption_resolution:    0
% 2.91/1.01  res_clause_to_clause_subsumption:       234
% 2.91/1.01  res_orphan_elimination:                 0
% 2.91/1.01  res_tautology_del:                      73
% 2.91/1.01  res_num_eq_res_simplified:              0
% 2.91/1.01  res_num_sel_changes:                    0
% 2.91/1.01  res_moves_from_active_to_pass:          0
% 2.91/1.01  
% 2.91/1.01  ------ Superposition
% 2.91/1.01  
% 2.91/1.01  sup_time_total:                         0.
% 2.91/1.01  sup_time_generating:                    0.
% 2.91/1.01  sup_time_sim_full:                      0.
% 2.91/1.01  sup_time_sim_immed:                     0.
% 2.91/1.01  
% 2.91/1.01  sup_num_of_clauses:                     91
% 2.91/1.01  sup_num_in_active:                      53
% 2.91/1.01  sup_num_in_passive:                     38
% 2.91/1.01  sup_num_of_loops:                       80
% 2.91/1.01  sup_fw_superposition:                   52
% 2.91/1.01  sup_bw_superposition:                   69
% 2.91/1.01  sup_immediate_simplified:               13
% 2.91/1.01  sup_given_eliminated:                   1
% 2.91/1.01  comparisons_done:                       0
% 2.91/1.01  comparisons_avoided:                    12
% 2.91/1.01  
% 2.91/1.01  ------ Simplifications
% 2.91/1.01  
% 2.91/1.01  
% 2.91/1.01  sim_fw_subset_subsumed:                 9
% 2.91/1.01  sim_bw_subset_subsumed:                 5
% 2.91/1.01  sim_fw_subsumed:                        3
% 2.91/1.01  sim_bw_subsumed:                        2
% 2.91/1.01  sim_fw_subsumption_res:                 2
% 2.91/1.01  sim_bw_subsumption_res:                 0
% 2.91/1.01  sim_tautology_del:                      1
% 2.91/1.01  sim_eq_tautology_del:                   11
% 2.91/1.01  sim_eq_res_simp:                        0
% 2.91/1.01  sim_fw_demodulated:                     0
% 2.91/1.01  sim_bw_demodulated:                     24
% 2.91/1.01  sim_light_normalised:                   2
% 2.91/1.01  sim_joinable_taut:                      0
% 2.91/1.01  sim_joinable_simp:                      0
% 2.91/1.01  sim_ac_normalised:                      0
% 2.91/1.01  sim_smt_subsumption:                    0
% 2.91/1.01  
%------------------------------------------------------------------------------
