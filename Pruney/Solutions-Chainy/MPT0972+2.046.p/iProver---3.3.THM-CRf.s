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
% DateTime   : Thu Dec  3 12:01:17 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_2770)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( r2_hidden(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK4)
        & ! [X4] :
            ( k1_funct_1(sK4,X4) = k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK4,X0,X1)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK1,sK2,sK3,X3)
          & ! [X4] :
              ( k1_funct_1(sK3,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,sK1) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ~ r2_relset_1(sK1,sK2,sK3,sK4)
    & ! [X4] :
        ( k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4)
        | ~ r2_hidden(X4,sK1) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f36,f35])).

fof(f65,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f66,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f62,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f63,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
        & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
            & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f31])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f61,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f67,plain,(
    ! [X4] :
      ( k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f20])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f54])).

fof(f68,plain,(
    ~ r2_relset_1(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f28])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f71,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f43])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
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
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_534,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_535,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_537,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_535,c_25])).

cnf(c_1359,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1361,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1704,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1359,c_1361])).

cnf(c_1843,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_537,c_1704])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1366,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2955,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1359,c_1366])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_217,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_218,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_217])).

cnf(c_278,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_218])).

cnf(c_1355,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_278])).

cnf(c_4025,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2955,c_1355])).

cnf(c_11,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1364,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4179,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4025,c_1364])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_545,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_29])).

cnf(c_546,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_545])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_548,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_546,c_28])).

cnf(c_1357,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1705,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1357,c_1361])).

cnf(c_1935,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_548,c_1705])).

cnf(c_13,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X1 = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1362,plain,
    ( X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1)
    | r2_hidden(sK0(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2195,plain,
    ( k1_relat_1(X0) != sK1
    | sK3 = X0
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(X0,sK3),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1935,c_1362])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_31,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2543,plain,
    ( v1_funct_1(X0) != iProver_top
    | r2_hidden(sK0(X0,sK3),k1_relat_1(X0)) = iProver_top
    | sK2 = k1_xboole_0
    | sK3 = X0
    | k1_relat_1(X0) != sK1
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2195,c_31])).

cnf(c_2544,plain,
    ( k1_relat_1(X0) != sK1
    | sK3 = X0
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(X0,sK3),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2543])).

cnf(c_2556,plain,
    ( sK4 = sK3
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(sK4,sK3),k1_relat_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1843,c_2544])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_34,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2752,plain,
    ( r2_hidden(sK0(sK4,sK3),k1_relat_1(sK4)) = iProver_top
    | sK2 = k1_xboole_0
    | sK4 = sK3
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2556,c_34])).

cnf(c_2753,plain,
    ( sK4 = sK3
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(sK4,sK3),k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2752])).

cnf(c_2761,plain,
    ( sK4 = sK3
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(sK4,sK3),sK1) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1843,c_2753])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(X0,sK1)
    | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1360,plain,
    ( k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2769,plain,
    ( k1_funct_1(sK4,sK0(sK4,sK3)) = k1_funct_1(sK3,sK0(sK4,sK3))
    | sK4 = sK3
    | sK2 = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2761,c_1360])).

cnf(c_4181,plain,
    ( k1_funct_1(sK4,sK0(sK4,sK3)) = k1_funct_1(sK3,sK0(sK4,sK3))
    | sK4 = sK3
    | sK2 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4179,c_2769])).

cnf(c_2956,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1357,c_1366])).

cnf(c_4026,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2956,c_1355])).

cnf(c_4204,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4026,c_1364])).

cnf(c_4342,plain,
    ( sK2 = k1_xboole_0
    | sK4 = sK3
    | k1_funct_1(sK4,sK0(sK4,sK3)) = k1_funct_1(sK3,sK0(sK4,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4181,c_2770,c_4180,c_4205])).

cnf(c_4343,plain,
    ( k1_funct_1(sK4,sK0(sK4,sK3)) = k1_funct_1(sK3,sK0(sK4,sK3))
    | sK4 = sK3
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4342])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | X0 = X1
    | k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1363,plain,
    ( X0 = X1
    | k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4347,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK4)
    | sK4 = sK3
    | sK2 = k1_xboole_0
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4343,c_1363])).

cnf(c_4930,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK4)
    | sK4 = sK3
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4347,c_30,c_27,c_4180,c_4205,c_4348])).

cnf(c_4935,plain,
    ( k1_relat_1(sK3) != sK1
    | sK4 = sK3
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1843,c_4930])).

cnf(c_4936,plain,
    ( sK4 = sK3
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4935,c_1935])).

cnf(c_15,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_23,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_375,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK4 != X0
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_23])).

cnf(c_376,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | sK3 != sK4 ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_378,plain,
    ( sK3 != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_376,c_25])).

cnf(c_4953,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4936,c_378])).

cnf(c_5154,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4953,c_1359])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_5160,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5154,c_3])).

cnf(c_5155,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4953,c_1357])).

cnf(c_5157,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5155,c_3])).

cnf(c_3078,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3079,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3078])).

cnf(c_3081,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3079])).

cnf(c_2827,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2828,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2827])).

cnf(c_2830,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2828])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2058,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2061,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2058])).

cnf(c_2049,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2052,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2049])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1815,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1816,plain,
    ( sK3 = X0
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1815])).

cnf(c_1818,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1816])).

cnf(c_1798,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1799,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(X0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1798])).

cnf(c_1801,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1799])).

cnf(c_1779,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4))
    | r1_tarski(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1780,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
    | r1_tarski(X0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1779])).

cnf(c_1782,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) != iProver_top
    | r1_tarski(k1_xboole_0,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1780])).

cnf(c_1726,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1727,plain,
    ( sK4 = X0
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1726])).

cnf(c_1729,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1727])).

cnf(c_843,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1574,plain,
    ( sK4 != X0
    | sK3 != X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_843])).

cnf(c_1575,plain,
    ( sK4 != k1_xboole_0
    | sK3 = sK4
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1574])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5160,c_5157,c_3081,c_2830,c_2061,c_2052,c_1818,c_1801,c_1782,c_1729,c_1575,c_376,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:51:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.68/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.02  
% 2.68/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.68/1.02  
% 2.68/1.02  ------  iProver source info
% 2.68/1.02  
% 2.68/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.68/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.68/1.02  git: non_committed_changes: false
% 2.68/1.02  git: last_make_outside_of_git: false
% 2.68/1.02  
% 2.68/1.02  ------ 
% 2.68/1.02  
% 2.68/1.02  ------ Input Options
% 2.68/1.02  
% 2.68/1.02  --out_options                           all
% 2.68/1.02  --tptp_safe_out                         true
% 2.68/1.02  --problem_path                          ""
% 2.68/1.02  --include_path                          ""
% 2.68/1.02  --clausifier                            res/vclausify_rel
% 2.68/1.02  --clausifier_options                    --mode clausify
% 2.68/1.02  --stdin                                 false
% 2.68/1.02  --stats_out                             all
% 2.68/1.02  
% 2.68/1.02  ------ General Options
% 2.68/1.02  
% 2.68/1.02  --fof                                   false
% 2.68/1.02  --time_out_real                         305.
% 2.68/1.02  --time_out_virtual                      -1.
% 2.68/1.02  --symbol_type_check                     false
% 2.68/1.02  --clausify_out                          false
% 2.68/1.02  --sig_cnt_out                           false
% 2.68/1.02  --trig_cnt_out                          false
% 2.68/1.02  --trig_cnt_out_tolerance                1.
% 2.68/1.02  --trig_cnt_out_sk_spl                   false
% 2.68/1.02  --abstr_cl_out                          false
% 2.68/1.02  
% 2.68/1.02  ------ Global Options
% 2.68/1.02  
% 2.68/1.02  --schedule                              default
% 2.68/1.02  --add_important_lit                     false
% 2.68/1.02  --prop_solver_per_cl                    1000
% 2.68/1.02  --min_unsat_core                        false
% 2.68/1.02  --soft_assumptions                      false
% 2.68/1.02  --soft_lemma_size                       3
% 2.68/1.02  --prop_impl_unit_size                   0
% 2.68/1.02  --prop_impl_unit                        []
% 2.68/1.02  --share_sel_clauses                     true
% 2.68/1.02  --reset_solvers                         false
% 2.68/1.02  --bc_imp_inh                            [conj_cone]
% 2.68/1.02  --conj_cone_tolerance                   3.
% 2.68/1.02  --extra_neg_conj                        none
% 2.68/1.02  --large_theory_mode                     true
% 2.68/1.02  --prolific_symb_bound                   200
% 2.68/1.02  --lt_threshold                          2000
% 2.68/1.02  --clause_weak_htbl                      true
% 2.68/1.02  --gc_record_bc_elim                     false
% 2.68/1.02  
% 2.68/1.02  ------ Preprocessing Options
% 2.68/1.02  
% 2.68/1.02  --preprocessing_flag                    true
% 2.68/1.02  --time_out_prep_mult                    0.1
% 2.68/1.02  --splitting_mode                        input
% 2.68/1.02  --splitting_grd                         true
% 2.68/1.02  --splitting_cvd                         false
% 2.68/1.02  --splitting_cvd_svl                     false
% 2.68/1.02  --splitting_nvd                         32
% 2.68/1.02  --sub_typing                            true
% 2.68/1.02  --prep_gs_sim                           true
% 2.68/1.02  --prep_unflatten                        true
% 2.68/1.02  --prep_res_sim                          true
% 2.68/1.02  --prep_upred                            true
% 2.68/1.02  --prep_sem_filter                       exhaustive
% 2.68/1.02  --prep_sem_filter_out                   false
% 2.68/1.02  --pred_elim                             true
% 2.68/1.02  --res_sim_input                         true
% 2.68/1.02  --eq_ax_congr_red                       true
% 2.68/1.02  --pure_diseq_elim                       true
% 2.68/1.02  --brand_transform                       false
% 2.68/1.02  --non_eq_to_eq                          false
% 2.68/1.02  --prep_def_merge                        true
% 2.68/1.02  --prep_def_merge_prop_impl              false
% 2.68/1.02  --prep_def_merge_mbd                    true
% 2.68/1.02  --prep_def_merge_tr_red                 false
% 2.68/1.02  --prep_def_merge_tr_cl                  false
% 2.68/1.02  --smt_preprocessing                     true
% 2.68/1.02  --smt_ac_axioms                         fast
% 2.68/1.02  --preprocessed_out                      false
% 2.68/1.02  --preprocessed_stats                    false
% 2.68/1.02  
% 2.68/1.02  ------ Abstraction refinement Options
% 2.68/1.02  
% 2.68/1.02  --abstr_ref                             []
% 2.68/1.02  --abstr_ref_prep                        false
% 2.68/1.02  --abstr_ref_until_sat                   false
% 2.68/1.02  --abstr_ref_sig_restrict                funpre
% 2.68/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.68/1.02  --abstr_ref_under                       []
% 2.68/1.02  
% 2.68/1.02  ------ SAT Options
% 2.68/1.02  
% 2.68/1.02  --sat_mode                              false
% 2.68/1.02  --sat_fm_restart_options                ""
% 2.68/1.02  --sat_gr_def                            false
% 2.68/1.02  --sat_epr_types                         true
% 2.68/1.02  --sat_non_cyclic_types                  false
% 2.68/1.02  --sat_finite_models                     false
% 2.68/1.02  --sat_fm_lemmas                         false
% 2.68/1.02  --sat_fm_prep                           false
% 2.68/1.02  --sat_fm_uc_incr                        true
% 2.68/1.02  --sat_out_model                         small
% 2.68/1.02  --sat_out_clauses                       false
% 2.68/1.02  
% 2.68/1.02  ------ QBF Options
% 2.68/1.02  
% 2.68/1.02  --qbf_mode                              false
% 2.68/1.02  --qbf_elim_univ                         false
% 2.68/1.02  --qbf_dom_inst                          none
% 2.68/1.02  --qbf_dom_pre_inst                      false
% 2.68/1.02  --qbf_sk_in                             false
% 2.68/1.02  --qbf_pred_elim                         true
% 2.68/1.02  --qbf_split                             512
% 2.68/1.02  
% 2.68/1.02  ------ BMC1 Options
% 2.68/1.02  
% 2.68/1.02  --bmc1_incremental                      false
% 2.68/1.02  --bmc1_axioms                           reachable_all
% 2.68/1.02  --bmc1_min_bound                        0
% 2.68/1.02  --bmc1_max_bound                        -1
% 2.68/1.02  --bmc1_max_bound_default                -1
% 2.68/1.02  --bmc1_symbol_reachability              true
% 2.68/1.02  --bmc1_property_lemmas                  false
% 2.68/1.02  --bmc1_k_induction                      false
% 2.68/1.02  --bmc1_non_equiv_states                 false
% 2.68/1.02  --bmc1_deadlock                         false
% 2.68/1.02  --bmc1_ucm                              false
% 2.68/1.02  --bmc1_add_unsat_core                   none
% 2.68/1.02  --bmc1_unsat_core_children              false
% 2.68/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.68/1.02  --bmc1_out_stat                         full
% 2.68/1.02  --bmc1_ground_init                      false
% 2.68/1.02  --bmc1_pre_inst_next_state              false
% 2.68/1.02  --bmc1_pre_inst_state                   false
% 2.68/1.02  --bmc1_pre_inst_reach_state             false
% 2.68/1.02  --bmc1_out_unsat_core                   false
% 2.68/1.02  --bmc1_aig_witness_out                  false
% 2.68/1.02  --bmc1_verbose                          false
% 2.68/1.02  --bmc1_dump_clauses_tptp                false
% 2.68/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.68/1.02  --bmc1_dump_file                        -
% 2.68/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.68/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.68/1.02  --bmc1_ucm_extend_mode                  1
% 2.68/1.02  --bmc1_ucm_init_mode                    2
% 2.68/1.02  --bmc1_ucm_cone_mode                    none
% 2.68/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.68/1.02  --bmc1_ucm_relax_model                  4
% 2.68/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.68/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.68/1.02  --bmc1_ucm_layered_model                none
% 2.68/1.02  --bmc1_ucm_max_lemma_size               10
% 2.68/1.02  
% 2.68/1.02  ------ AIG Options
% 2.68/1.02  
% 2.68/1.02  --aig_mode                              false
% 2.68/1.02  
% 2.68/1.02  ------ Instantiation Options
% 2.68/1.02  
% 2.68/1.02  --instantiation_flag                    true
% 2.68/1.02  --inst_sos_flag                         false
% 2.68/1.02  --inst_sos_phase                        true
% 2.68/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.68/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.68/1.02  --inst_lit_sel_side                     num_symb
% 2.68/1.02  --inst_solver_per_active                1400
% 2.68/1.02  --inst_solver_calls_frac                1.
% 2.68/1.02  --inst_passive_queue_type               priority_queues
% 2.68/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.68/1.02  --inst_passive_queues_freq              [25;2]
% 2.68/1.02  --inst_dismatching                      true
% 2.68/1.02  --inst_eager_unprocessed_to_passive     true
% 2.68/1.02  --inst_prop_sim_given                   true
% 2.68/1.02  --inst_prop_sim_new                     false
% 2.68/1.02  --inst_subs_new                         false
% 2.68/1.02  --inst_eq_res_simp                      false
% 2.68/1.02  --inst_subs_given                       false
% 2.68/1.02  --inst_orphan_elimination               true
% 2.68/1.02  --inst_learning_loop_flag               true
% 2.68/1.02  --inst_learning_start                   3000
% 2.68/1.02  --inst_learning_factor                  2
% 2.68/1.02  --inst_start_prop_sim_after_learn       3
% 2.68/1.02  --inst_sel_renew                        solver
% 2.68/1.02  --inst_lit_activity_flag                true
% 2.68/1.02  --inst_restr_to_given                   false
% 2.68/1.02  --inst_activity_threshold               500
% 2.68/1.02  --inst_out_proof                        true
% 2.68/1.02  
% 2.68/1.02  ------ Resolution Options
% 2.68/1.02  
% 2.68/1.02  --resolution_flag                       true
% 2.68/1.02  --res_lit_sel                           adaptive
% 2.68/1.02  --res_lit_sel_side                      none
% 2.68/1.02  --res_ordering                          kbo
% 2.68/1.02  --res_to_prop_solver                    active
% 2.68/1.02  --res_prop_simpl_new                    false
% 2.68/1.02  --res_prop_simpl_given                  true
% 2.68/1.02  --res_passive_queue_type                priority_queues
% 2.68/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.68/1.02  --res_passive_queues_freq               [15;5]
% 2.68/1.02  --res_forward_subs                      full
% 2.68/1.02  --res_backward_subs                     full
% 2.68/1.02  --res_forward_subs_resolution           true
% 2.68/1.02  --res_backward_subs_resolution          true
% 2.68/1.02  --res_orphan_elimination                true
% 2.68/1.02  --res_time_limit                        2.
% 2.68/1.02  --res_out_proof                         true
% 2.68/1.02  
% 2.68/1.02  ------ Superposition Options
% 2.68/1.02  
% 2.68/1.02  --superposition_flag                    true
% 2.68/1.02  --sup_passive_queue_type                priority_queues
% 2.68/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.68/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.68/1.02  --demod_completeness_check              fast
% 2.68/1.02  --demod_use_ground                      true
% 2.68/1.02  --sup_to_prop_solver                    passive
% 2.68/1.02  --sup_prop_simpl_new                    true
% 2.68/1.02  --sup_prop_simpl_given                  true
% 2.68/1.02  --sup_fun_splitting                     false
% 2.68/1.02  --sup_smt_interval                      50000
% 2.68/1.02  
% 2.68/1.02  ------ Superposition Simplification Setup
% 2.68/1.02  
% 2.68/1.02  --sup_indices_passive                   []
% 2.68/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.68/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/1.02  --sup_full_bw                           [BwDemod]
% 2.68/1.02  --sup_immed_triv                        [TrivRules]
% 2.68/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.68/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/1.02  --sup_immed_bw_main                     []
% 2.68/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.68/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.68/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.68/1.02  
% 2.68/1.02  ------ Combination Options
% 2.68/1.02  
% 2.68/1.02  --comb_res_mult                         3
% 2.68/1.02  --comb_sup_mult                         2
% 2.68/1.02  --comb_inst_mult                        10
% 2.68/1.02  
% 2.68/1.02  ------ Debug Options
% 2.68/1.02  
% 2.68/1.02  --dbg_backtrace                         false
% 2.68/1.02  --dbg_dump_prop_clauses                 false
% 2.68/1.02  --dbg_dump_prop_clauses_file            -
% 2.68/1.02  --dbg_out_stat                          false
% 2.68/1.02  ------ Parsing...
% 2.68/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.68/1.02  
% 2.68/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.68/1.02  
% 2.68/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.68/1.02  
% 2.68/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.68/1.02  ------ Proving...
% 2.68/1.02  ------ Problem Properties 
% 2.68/1.02  
% 2.68/1.02  
% 2.68/1.02  clauses                                 26
% 2.68/1.02  conjectures                             5
% 2.68/1.02  EPR                                     6
% 2.68/1.02  Horn                                    20
% 2.68/1.02  unary                                   10
% 2.68/1.02  binary                                  6
% 2.68/1.02  lits                                    62
% 2.68/1.02  lits eq                                 28
% 2.68/1.02  fd_pure                                 0
% 2.68/1.02  fd_pseudo                               0
% 2.68/1.02  fd_cond                                 1
% 2.68/1.02  fd_pseudo_cond                          3
% 2.68/1.02  AC symbols                              0
% 2.68/1.02  
% 2.68/1.02  ------ Schedule dynamic 5 is on 
% 2.68/1.02  
% 2.68/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.68/1.02  
% 2.68/1.02  
% 2.68/1.02  ------ 
% 2.68/1.02  Current options:
% 2.68/1.02  ------ 
% 2.68/1.02  
% 2.68/1.02  ------ Input Options
% 2.68/1.02  
% 2.68/1.02  --out_options                           all
% 2.68/1.02  --tptp_safe_out                         true
% 2.68/1.02  --problem_path                          ""
% 2.68/1.02  --include_path                          ""
% 2.68/1.02  --clausifier                            res/vclausify_rel
% 2.68/1.02  --clausifier_options                    --mode clausify
% 2.68/1.02  --stdin                                 false
% 2.68/1.02  --stats_out                             all
% 2.68/1.02  
% 2.68/1.02  ------ General Options
% 2.68/1.02  
% 2.68/1.02  --fof                                   false
% 2.68/1.02  --time_out_real                         305.
% 2.68/1.02  --time_out_virtual                      -1.
% 2.68/1.02  --symbol_type_check                     false
% 2.68/1.02  --clausify_out                          false
% 2.68/1.02  --sig_cnt_out                           false
% 2.68/1.02  --trig_cnt_out                          false
% 2.68/1.02  --trig_cnt_out_tolerance                1.
% 2.68/1.02  --trig_cnt_out_sk_spl                   false
% 2.68/1.02  --abstr_cl_out                          false
% 2.68/1.02  
% 2.68/1.02  ------ Global Options
% 2.68/1.02  
% 2.68/1.02  --schedule                              default
% 2.68/1.02  --add_important_lit                     false
% 2.68/1.02  --prop_solver_per_cl                    1000
% 2.68/1.02  --min_unsat_core                        false
% 2.68/1.02  --soft_assumptions                      false
% 2.68/1.02  --soft_lemma_size                       3
% 2.68/1.02  --prop_impl_unit_size                   0
% 2.68/1.02  --prop_impl_unit                        []
% 2.68/1.02  --share_sel_clauses                     true
% 2.68/1.02  --reset_solvers                         false
% 2.68/1.02  --bc_imp_inh                            [conj_cone]
% 2.68/1.02  --conj_cone_tolerance                   3.
% 2.68/1.02  --extra_neg_conj                        none
% 2.68/1.02  --large_theory_mode                     true
% 2.68/1.02  --prolific_symb_bound                   200
% 2.68/1.02  --lt_threshold                          2000
% 2.68/1.02  --clause_weak_htbl                      true
% 2.68/1.02  --gc_record_bc_elim                     false
% 2.68/1.02  
% 2.68/1.02  ------ Preprocessing Options
% 2.68/1.02  
% 2.68/1.02  --preprocessing_flag                    true
% 2.68/1.02  --time_out_prep_mult                    0.1
% 2.68/1.02  --splitting_mode                        input
% 2.68/1.02  --splitting_grd                         true
% 2.68/1.02  --splitting_cvd                         false
% 2.68/1.02  --splitting_cvd_svl                     false
% 2.68/1.02  --splitting_nvd                         32
% 2.68/1.02  --sub_typing                            true
% 2.68/1.02  --prep_gs_sim                           true
% 2.68/1.02  --prep_unflatten                        true
% 2.68/1.02  --prep_res_sim                          true
% 2.68/1.02  --prep_upred                            true
% 2.68/1.02  --prep_sem_filter                       exhaustive
% 2.68/1.02  --prep_sem_filter_out                   false
% 2.68/1.02  --pred_elim                             true
% 2.68/1.02  --res_sim_input                         true
% 2.68/1.02  --eq_ax_congr_red                       true
% 2.68/1.02  --pure_diseq_elim                       true
% 2.68/1.02  --brand_transform                       false
% 2.68/1.02  --non_eq_to_eq                          false
% 2.68/1.02  --prep_def_merge                        true
% 2.68/1.02  --prep_def_merge_prop_impl              false
% 2.68/1.02  --prep_def_merge_mbd                    true
% 2.68/1.02  --prep_def_merge_tr_red                 false
% 2.68/1.02  --prep_def_merge_tr_cl                  false
% 2.68/1.02  --smt_preprocessing                     true
% 2.68/1.02  --smt_ac_axioms                         fast
% 2.68/1.02  --preprocessed_out                      false
% 2.68/1.02  --preprocessed_stats                    false
% 2.68/1.02  
% 2.68/1.02  ------ Abstraction refinement Options
% 2.68/1.02  
% 2.68/1.02  --abstr_ref                             []
% 2.68/1.02  --abstr_ref_prep                        false
% 2.68/1.02  --abstr_ref_until_sat                   false
% 2.68/1.02  --abstr_ref_sig_restrict                funpre
% 2.68/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.68/1.02  --abstr_ref_under                       []
% 2.68/1.02  
% 2.68/1.02  ------ SAT Options
% 2.68/1.02  
% 2.68/1.02  --sat_mode                              false
% 2.68/1.02  --sat_fm_restart_options                ""
% 2.68/1.02  --sat_gr_def                            false
% 2.68/1.02  --sat_epr_types                         true
% 2.68/1.02  --sat_non_cyclic_types                  false
% 2.68/1.02  --sat_finite_models                     false
% 2.68/1.02  --sat_fm_lemmas                         false
% 2.68/1.02  --sat_fm_prep                           false
% 2.68/1.02  --sat_fm_uc_incr                        true
% 2.68/1.02  --sat_out_model                         small
% 2.68/1.02  --sat_out_clauses                       false
% 2.68/1.02  
% 2.68/1.02  ------ QBF Options
% 2.68/1.02  
% 2.68/1.02  --qbf_mode                              false
% 2.68/1.02  --qbf_elim_univ                         false
% 2.68/1.02  --qbf_dom_inst                          none
% 2.68/1.02  --qbf_dom_pre_inst                      false
% 2.68/1.02  --qbf_sk_in                             false
% 2.68/1.02  --qbf_pred_elim                         true
% 2.68/1.02  --qbf_split                             512
% 2.68/1.02  
% 2.68/1.02  ------ BMC1 Options
% 2.68/1.02  
% 2.68/1.02  --bmc1_incremental                      false
% 2.68/1.02  --bmc1_axioms                           reachable_all
% 2.68/1.02  --bmc1_min_bound                        0
% 2.68/1.02  --bmc1_max_bound                        -1
% 2.68/1.02  --bmc1_max_bound_default                -1
% 2.68/1.02  --bmc1_symbol_reachability              true
% 2.68/1.02  --bmc1_property_lemmas                  false
% 2.68/1.02  --bmc1_k_induction                      false
% 2.68/1.02  --bmc1_non_equiv_states                 false
% 2.68/1.02  --bmc1_deadlock                         false
% 2.68/1.02  --bmc1_ucm                              false
% 2.68/1.02  --bmc1_add_unsat_core                   none
% 2.68/1.02  --bmc1_unsat_core_children              false
% 2.68/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.68/1.02  --bmc1_out_stat                         full
% 2.68/1.02  --bmc1_ground_init                      false
% 2.68/1.02  --bmc1_pre_inst_next_state              false
% 2.68/1.02  --bmc1_pre_inst_state                   false
% 2.68/1.02  --bmc1_pre_inst_reach_state             false
% 2.68/1.02  --bmc1_out_unsat_core                   false
% 2.68/1.02  --bmc1_aig_witness_out                  false
% 2.68/1.02  --bmc1_verbose                          false
% 2.68/1.02  --bmc1_dump_clauses_tptp                false
% 2.68/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.68/1.02  --bmc1_dump_file                        -
% 2.68/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.68/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.68/1.02  --bmc1_ucm_extend_mode                  1
% 2.68/1.02  --bmc1_ucm_init_mode                    2
% 2.68/1.02  --bmc1_ucm_cone_mode                    none
% 2.68/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.68/1.02  --bmc1_ucm_relax_model                  4
% 2.68/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.68/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.68/1.02  --bmc1_ucm_layered_model                none
% 2.68/1.02  --bmc1_ucm_max_lemma_size               10
% 2.68/1.02  
% 2.68/1.02  ------ AIG Options
% 2.68/1.02  
% 2.68/1.02  --aig_mode                              false
% 2.68/1.02  
% 2.68/1.02  ------ Instantiation Options
% 2.68/1.02  
% 2.68/1.02  --instantiation_flag                    true
% 2.68/1.02  --inst_sos_flag                         false
% 2.68/1.02  --inst_sos_phase                        true
% 2.68/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.68/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.68/1.02  --inst_lit_sel_side                     none
% 2.68/1.02  --inst_solver_per_active                1400
% 2.68/1.02  --inst_solver_calls_frac                1.
% 2.68/1.02  --inst_passive_queue_type               priority_queues
% 2.68/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.68/1.02  --inst_passive_queues_freq              [25;2]
% 2.68/1.02  --inst_dismatching                      true
% 2.68/1.02  --inst_eager_unprocessed_to_passive     true
% 2.68/1.02  --inst_prop_sim_given                   true
% 2.68/1.02  --inst_prop_sim_new                     false
% 2.68/1.02  --inst_subs_new                         false
% 2.68/1.02  --inst_eq_res_simp                      false
% 2.68/1.02  --inst_subs_given                       false
% 2.68/1.02  --inst_orphan_elimination               true
% 2.68/1.02  --inst_learning_loop_flag               true
% 2.68/1.02  --inst_learning_start                   3000
% 2.68/1.02  --inst_learning_factor                  2
% 2.68/1.02  --inst_start_prop_sim_after_learn       3
% 2.68/1.02  --inst_sel_renew                        solver
% 2.68/1.02  --inst_lit_activity_flag                true
% 2.68/1.02  --inst_restr_to_given                   false
% 2.68/1.02  --inst_activity_threshold               500
% 2.68/1.02  --inst_out_proof                        true
% 2.68/1.02  
% 2.68/1.02  ------ Resolution Options
% 2.68/1.02  
% 2.68/1.02  --resolution_flag                       false
% 2.68/1.02  --res_lit_sel                           adaptive
% 2.68/1.02  --res_lit_sel_side                      none
% 2.68/1.02  --res_ordering                          kbo
% 2.68/1.02  --res_to_prop_solver                    active
% 2.68/1.02  --res_prop_simpl_new                    false
% 2.68/1.02  --res_prop_simpl_given                  true
% 2.68/1.02  --res_passive_queue_type                priority_queues
% 2.68/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.68/1.02  --res_passive_queues_freq               [15;5]
% 2.68/1.02  --res_forward_subs                      full
% 2.68/1.02  --res_backward_subs                     full
% 2.68/1.02  --res_forward_subs_resolution           true
% 2.68/1.02  --res_backward_subs_resolution          true
% 2.68/1.02  --res_orphan_elimination                true
% 2.68/1.02  --res_time_limit                        2.
% 2.68/1.02  --res_out_proof                         true
% 2.68/1.02  
% 2.68/1.02  ------ Superposition Options
% 2.68/1.02  
% 2.68/1.02  --superposition_flag                    true
% 2.68/1.02  --sup_passive_queue_type                priority_queues
% 2.68/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.68/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.68/1.02  --demod_completeness_check              fast
% 2.68/1.02  --demod_use_ground                      true
% 2.68/1.02  --sup_to_prop_solver                    passive
% 2.68/1.02  --sup_prop_simpl_new                    true
% 2.68/1.02  --sup_prop_simpl_given                  true
% 2.68/1.02  --sup_fun_splitting                     false
% 2.68/1.02  --sup_smt_interval                      50000
% 2.68/1.02  
% 2.68/1.02  ------ Superposition Simplification Setup
% 2.68/1.02  
% 2.68/1.02  --sup_indices_passive                   []
% 2.68/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.68/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/1.02  --sup_full_bw                           [BwDemod]
% 2.68/1.02  --sup_immed_triv                        [TrivRules]
% 2.68/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.68/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/1.02  --sup_immed_bw_main                     []
% 2.68/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.68/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.68/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.68/1.02  
% 2.68/1.02  ------ Combination Options
% 2.68/1.02  
% 2.68/1.02  --comb_res_mult                         3
% 2.68/1.02  --comb_sup_mult                         2
% 2.68/1.02  --comb_inst_mult                        10
% 2.68/1.02  
% 2.68/1.02  ------ Debug Options
% 2.68/1.02  
% 2.68/1.02  --dbg_backtrace                         false
% 2.68/1.02  --dbg_dump_prop_clauses                 false
% 2.68/1.02  --dbg_dump_prop_clauses_file            -
% 2.68/1.02  --dbg_out_stat                          false
% 2.68/1.02  
% 2.68/1.02  
% 2.68/1.02  
% 2.68/1.02  
% 2.68/1.02  ------ Proving...
% 2.68/1.02  
% 2.68/1.02  
% 2.68/1.02  % SZS status Theorem for theBenchmark.p
% 2.68/1.02  
% 2.68/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.68/1.02  
% 2.68/1.02  fof(f11,axiom,(
% 2.68/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.68/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/1.02  
% 2.68/1.02  fof(f22,plain,(
% 2.68/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.68/1.02    inference(ennf_transformation,[],[f11])).
% 2.68/1.02  
% 2.68/1.02  fof(f23,plain,(
% 2.68/1.02    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.68/1.02    inference(flattening,[],[f22])).
% 2.68/1.02  
% 2.68/1.02  fof(f34,plain,(
% 2.68/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.68/1.02    inference(nnf_transformation,[],[f23])).
% 2.68/1.02  
% 2.68/1.02  fof(f55,plain,(
% 2.68/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.68/1.02    inference(cnf_transformation,[],[f34])).
% 2.68/1.02  
% 2.68/1.02  fof(f12,conjecture,(
% 2.68/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.68/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/1.02  
% 2.68/1.02  fof(f13,negated_conjecture,(
% 2.68/1.02    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.68/1.02    inference(negated_conjecture,[],[f12])).
% 2.68/1.02  
% 2.68/1.02  fof(f24,plain,(
% 2.68/1.02    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.68/1.02    inference(ennf_transformation,[],[f13])).
% 2.68/1.02  
% 2.68/1.02  fof(f25,plain,(
% 2.68/1.02    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.68/1.02    inference(flattening,[],[f24])).
% 2.68/1.02  
% 2.68/1.02  fof(f36,plain,(
% 2.68/1.02    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK4) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK4,X0,X1) & v1_funct_1(sK4))) )),
% 2.68/1.02    introduced(choice_axiom,[])).
% 2.68/1.02  
% 2.68/1.02  fof(f35,plain,(
% 2.68/1.02    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK1,sK2,sK3,X3) & ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 2.68/1.02    introduced(choice_axiom,[])).
% 2.68/1.02  
% 2.68/1.02  fof(f37,plain,(
% 2.68/1.02    (~r2_relset_1(sK1,sK2,sK3,sK4) & ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4) | ~r2_hidden(X4,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 2.68/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f36,f35])).
% 2.68/1.02  
% 2.68/1.02  fof(f65,plain,(
% 2.68/1.02    v1_funct_2(sK4,sK1,sK2)),
% 2.68/1.02    inference(cnf_transformation,[],[f37])).
% 2.68/1.02  
% 2.68/1.02  fof(f66,plain,(
% 2.68/1.02    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.68/1.02    inference(cnf_transformation,[],[f37])).
% 2.68/1.02  
% 2.68/1.02  fof(f9,axiom,(
% 2.68/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.68/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/1.02  
% 2.68/1.02  fof(f19,plain,(
% 2.68/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.68/1.02    inference(ennf_transformation,[],[f9])).
% 2.68/1.02  
% 2.68/1.02  fof(f52,plain,(
% 2.68/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.68/1.02    inference(cnf_transformation,[],[f19])).
% 2.68/1.02  
% 2.68/1.02  fof(f4,axiom,(
% 2.68/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.68/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/1.02  
% 2.68/1.02  fof(f30,plain,(
% 2.68/1.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.68/1.02    inference(nnf_transformation,[],[f4])).
% 2.68/1.02  
% 2.68/1.02  fof(f45,plain,(
% 2.68/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.68/1.02    inference(cnf_transformation,[],[f30])).
% 2.68/1.02  
% 2.68/1.02  fof(f6,axiom,(
% 2.68/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.68/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/1.02  
% 2.68/1.02  fof(f16,plain,(
% 2.68/1.02    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.68/1.02    inference(ennf_transformation,[],[f6])).
% 2.68/1.02  
% 2.68/1.02  fof(f48,plain,(
% 2.68/1.02    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.68/1.02    inference(cnf_transformation,[],[f16])).
% 2.68/1.02  
% 2.68/1.02  fof(f46,plain,(
% 2.68/1.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.68/1.02    inference(cnf_transformation,[],[f30])).
% 2.68/1.02  
% 2.68/1.02  fof(f7,axiom,(
% 2.68/1.02    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.68/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/1.02  
% 2.68/1.02  fof(f49,plain,(
% 2.68/1.02    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.68/1.02    inference(cnf_transformation,[],[f7])).
% 2.68/1.02  
% 2.68/1.02  fof(f62,plain,(
% 2.68/1.02    v1_funct_2(sK3,sK1,sK2)),
% 2.68/1.02    inference(cnf_transformation,[],[f37])).
% 2.68/1.02  
% 2.68/1.02  fof(f63,plain,(
% 2.68/1.02    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.68/1.02    inference(cnf_transformation,[],[f37])).
% 2.68/1.02  
% 2.68/1.02  fof(f8,axiom,(
% 2.68/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 2.68/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/1.02  
% 2.68/1.02  fof(f17,plain,(
% 2.68/1.02    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.68/1.02    inference(ennf_transformation,[],[f8])).
% 2.68/1.02  
% 2.68/1.02  fof(f18,plain,(
% 2.68/1.02    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.68/1.02    inference(flattening,[],[f17])).
% 2.68/1.02  
% 2.68/1.02  fof(f31,plain,(
% 2.68/1.02    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))))),
% 2.68/1.02    introduced(choice_axiom,[])).
% 2.68/1.02  
% 2.68/1.02  fof(f32,plain,(
% 2.68/1.02    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.68/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f31])).
% 2.68/1.02  
% 2.68/1.02  fof(f50,plain,(
% 2.68/1.02    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.68/1.02    inference(cnf_transformation,[],[f32])).
% 2.68/1.02  
% 2.68/1.02  fof(f61,plain,(
% 2.68/1.02    v1_funct_1(sK3)),
% 2.68/1.02    inference(cnf_transformation,[],[f37])).
% 2.68/1.02  
% 2.68/1.02  fof(f64,plain,(
% 2.68/1.02    v1_funct_1(sK4)),
% 2.68/1.02    inference(cnf_transformation,[],[f37])).
% 2.68/1.02  
% 2.68/1.02  fof(f67,plain,(
% 2.68/1.02    ( ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4) | ~r2_hidden(X4,sK1)) )),
% 2.68/1.02    inference(cnf_transformation,[],[f37])).
% 2.68/1.02  
% 2.68/1.02  fof(f51,plain,(
% 2.68/1.02    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.68/1.02    inference(cnf_transformation,[],[f32])).
% 2.68/1.02  
% 2.68/1.02  fof(f10,axiom,(
% 2.68/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.68/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/1.02  
% 2.68/1.02  fof(f20,plain,(
% 2.68/1.02    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.68/1.02    inference(ennf_transformation,[],[f10])).
% 2.68/1.02  
% 2.68/1.02  fof(f21,plain,(
% 2.68/1.02    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.68/1.02    inference(flattening,[],[f20])).
% 2.68/1.02  
% 2.68/1.02  fof(f33,plain,(
% 2.68/1.02    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.68/1.02    inference(nnf_transformation,[],[f21])).
% 2.68/1.02  
% 2.68/1.02  fof(f54,plain,(
% 2.68/1.02    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.68/1.02    inference(cnf_transformation,[],[f33])).
% 2.68/1.02  
% 2.68/1.02  fof(f73,plain,(
% 2.68/1.02    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.68/1.02    inference(equality_resolution,[],[f54])).
% 2.68/1.02  
% 2.68/1.02  fof(f68,plain,(
% 2.68/1.02    ~r2_relset_1(sK1,sK2,sK3,sK4)),
% 2.68/1.02    inference(cnf_transformation,[],[f37])).
% 2.68/1.02  
% 2.68/1.02  fof(f2,axiom,(
% 2.68/1.02    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.68/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/1.02  
% 2.68/1.02  fof(f28,plain,(
% 2.68/1.02    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.68/1.02    inference(nnf_transformation,[],[f2])).
% 2.68/1.02  
% 2.68/1.02  fof(f29,plain,(
% 2.68/1.02    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.68/1.02    inference(flattening,[],[f28])).
% 2.68/1.02  
% 2.68/1.02  fof(f43,plain,(
% 2.68/1.02    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 2.68/1.02    inference(cnf_transformation,[],[f29])).
% 2.68/1.02  
% 2.68/1.02  fof(f71,plain,(
% 2.68/1.02    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 2.68/1.02    inference(equality_resolution,[],[f43])).
% 2.68/1.02  
% 2.68/1.02  fof(f3,axiom,(
% 2.68/1.02    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.68/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/1.02  
% 2.68/1.02  fof(f44,plain,(
% 2.68/1.02    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.68/1.02    inference(cnf_transformation,[],[f3])).
% 2.68/1.02  
% 2.68/1.02  fof(f1,axiom,(
% 2.68/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.68/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/1.02  
% 2.68/1.02  fof(f26,plain,(
% 2.68/1.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.68/1.02    inference(nnf_transformation,[],[f1])).
% 2.68/1.02  
% 2.68/1.02  fof(f27,plain,(
% 2.68/1.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.68/1.02    inference(flattening,[],[f26])).
% 2.68/1.02  
% 2.68/1.02  fof(f40,plain,(
% 2.68/1.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.68/1.02    inference(cnf_transformation,[],[f27])).
% 2.68/1.02  
% 2.68/1.02  cnf(c_22,plain,
% 2.68/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.68/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/1.02      | k1_relset_1(X1,X2,X0) = X1
% 2.68/1.02      | k1_xboole_0 = X2 ),
% 2.68/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_26,negated_conjecture,
% 2.68/1.02      ( v1_funct_2(sK4,sK1,sK2) ),
% 2.68/1.02      inference(cnf_transformation,[],[f65]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_534,plain,
% 2.68/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/1.02      | k1_relset_1(X1,X2,X0) = X1
% 2.68/1.02      | sK4 != X0
% 2.68/1.02      | sK2 != X2
% 2.68/1.02      | sK1 != X1
% 2.68/1.02      | k1_xboole_0 = X2 ),
% 2.68/1.02      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_535,plain,
% 2.68/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.68/1.02      | k1_relset_1(sK1,sK2,sK4) = sK1
% 2.68/1.02      | k1_xboole_0 = sK2 ),
% 2.68/1.02      inference(unflattening,[status(thm)],[c_534]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_25,negated_conjecture,
% 2.68/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.68/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_537,plain,
% 2.68/1.02      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 2.68/1.02      inference(global_propositional_subsumption,
% 2.68/1.02                [status(thm)],
% 2.68/1.02                [c_535,c_25]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_1359,plain,
% 2.68/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.68/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_14,plain,
% 2.68/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.68/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_1361,plain,
% 2.68/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.68/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.68/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_1704,plain,
% 2.68/1.02      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 2.68/1.02      inference(superposition,[status(thm)],[c_1359,c_1361]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_1843,plain,
% 2.68/1.02      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 2.68/1.02      inference(superposition,[status(thm)],[c_537,c_1704]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_8,plain,
% 2.68/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.68/1.02      inference(cnf_transformation,[],[f45]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_1366,plain,
% 2.68/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.68/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 2.68/1.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_2955,plain,
% 2.68/1.02      ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 2.68/1.02      inference(superposition,[status(thm)],[c_1359,c_1366]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_10,plain,
% 2.68/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.68/1.02      | ~ v1_relat_1(X1)
% 2.68/1.02      | v1_relat_1(X0) ),
% 2.68/1.02      inference(cnf_transformation,[],[f48]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_7,plain,
% 2.68/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.68/1.02      inference(cnf_transformation,[],[f46]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_217,plain,
% 2.68/1.02      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.68/1.02      inference(prop_impl,[status(thm)],[c_7]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_218,plain,
% 2.68/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.68/1.02      inference(renaming,[status(thm)],[c_217]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_278,plain,
% 2.68/1.02      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.68/1.02      inference(bin_hyper_res,[status(thm)],[c_10,c_218]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_1355,plain,
% 2.68/1.02      ( r1_tarski(X0,X1) != iProver_top
% 2.68/1.02      | v1_relat_1(X1) != iProver_top
% 2.68/1.02      | v1_relat_1(X0) = iProver_top ),
% 2.68/1.02      inference(predicate_to_equality,[status(thm)],[c_278]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_4025,plain,
% 2.68/1.02      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 2.68/1.02      | v1_relat_1(sK4) = iProver_top ),
% 2.68/1.02      inference(superposition,[status(thm)],[c_2955,c_1355]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_11,plain,
% 2.68/1.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.68/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_1364,plain,
% 2.68/1.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.68/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_4179,plain,
% 2.68/1.02      ( v1_relat_1(sK4) = iProver_top ),
% 2.68/1.02      inference(forward_subsumption_resolution,
% 2.68/1.02                [status(thm)],
% 2.68/1.02                [c_4025,c_1364]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_29,negated_conjecture,
% 2.68/1.02      ( v1_funct_2(sK3,sK1,sK2) ),
% 2.68/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_545,plain,
% 2.68/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/1.02      | k1_relset_1(X1,X2,X0) = X1
% 2.68/1.02      | sK3 != X0
% 2.68/1.02      | sK2 != X2
% 2.68/1.02      | sK1 != X1
% 2.68/1.02      | k1_xboole_0 = X2 ),
% 2.68/1.02      inference(resolution_lifted,[status(thm)],[c_22,c_29]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_546,plain,
% 2.68/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.68/1.02      | k1_relset_1(sK1,sK2,sK3) = sK1
% 2.68/1.02      | k1_xboole_0 = sK2 ),
% 2.68/1.02      inference(unflattening,[status(thm)],[c_545]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_28,negated_conjecture,
% 2.68/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.68/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_548,plain,
% 2.68/1.02      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 2.68/1.02      inference(global_propositional_subsumption,
% 2.68/1.02                [status(thm)],
% 2.68/1.02                [c_546,c_28]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_1357,plain,
% 2.68/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.68/1.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_1705,plain,
% 2.68/1.02      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 2.68/1.02      inference(superposition,[status(thm)],[c_1357,c_1361]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_1935,plain,
% 2.68/1.02      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 2.68/1.02      inference(superposition,[status(thm)],[c_548,c_1705]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_13,plain,
% 2.68/1.02      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 2.68/1.02      | ~ v1_funct_1(X1)
% 2.68/1.02      | ~ v1_funct_1(X0)
% 2.68/1.02      | ~ v1_relat_1(X0)
% 2.68/1.02      | ~ v1_relat_1(X1)
% 2.68/1.02      | X1 = X0
% 2.68/1.02      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 2.68/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_1362,plain,
% 2.68/1.02      ( X0 = X1
% 2.68/1.02      | k1_relat_1(X0) != k1_relat_1(X1)
% 2.68/1.02      | r2_hidden(sK0(X1,X0),k1_relat_1(X1)) = iProver_top
% 2.68/1.02      | v1_funct_1(X0) != iProver_top
% 2.68/1.02      | v1_funct_1(X1) != iProver_top
% 2.68/1.02      | v1_relat_1(X1) != iProver_top
% 2.68/1.02      | v1_relat_1(X0) != iProver_top ),
% 2.68/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_2195,plain,
% 2.68/1.02      ( k1_relat_1(X0) != sK1
% 2.68/1.02      | sK3 = X0
% 2.68/1.02      | sK2 = k1_xboole_0
% 2.68/1.02      | r2_hidden(sK0(X0,sK3),k1_relat_1(X0)) = iProver_top
% 2.68/1.02      | v1_funct_1(X0) != iProver_top
% 2.68/1.02      | v1_funct_1(sK3) != iProver_top
% 2.68/1.02      | v1_relat_1(X0) != iProver_top
% 2.68/1.02      | v1_relat_1(sK3) != iProver_top ),
% 2.68/1.02      inference(superposition,[status(thm)],[c_1935,c_1362]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_30,negated_conjecture,
% 2.68/1.02      ( v1_funct_1(sK3) ),
% 2.68/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_31,plain,
% 2.68/1.02      ( v1_funct_1(sK3) = iProver_top ),
% 2.68/1.02      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_2543,plain,
% 2.68/1.02      ( v1_funct_1(X0) != iProver_top
% 2.68/1.02      | r2_hidden(sK0(X0,sK3),k1_relat_1(X0)) = iProver_top
% 2.68/1.02      | sK2 = k1_xboole_0
% 2.68/1.02      | sK3 = X0
% 2.68/1.02      | k1_relat_1(X0) != sK1
% 2.68/1.02      | v1_relat_1(X0) != iProver_top
% 2.68/1.02      | v1_relat_1(sK3) != iProver_top ),
% 2.68/1.02      inference(global_propositional_subsumption,
% 2.68/1.02                [status(thm)],
% 2.68/1.02                [c_2195,c_31]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_2544,plain,
% 2.68/1.02      ( k1_relat_1(X0) != sK1
% 2.68/1.02      | sK3 = X0
% 2.68/1.02      | sK2 = k1_xboole_0
% 2.68/1.02      | r2_hidden(sK0(X0,sK3),k1_relat_1(X0)) = iProver_top
% 2.68/1.02      | v1_funct_1(X0) != iProver_top
% 2.68/1.02      | v1_relat_1(X0) != iProver_top
% 2.68/1.02      | v1_relat_1(sK3) != iProver_top ),
% 2.68/1.02      inference(renaming,[status(thm)],[c_2543]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_2556,plain,
% 2.68/1.02      ( sK4 = sK3
% 2.68/1.02      | sK2 = k1_xboole_0
% 2.68/1.02      | r2_hidden(sK0(sK4,sK3),k1_relat_1(sK4)) = iProver_top
% 2.68/1.02      | v1_funct_1(sK4) != iProver_top
% 2.68/1.02      | v1_relat_1(sK4) != iProver_top
% 2.68/1.02      | v1_relat_1(sK3) != iProver_top ),
% 2.68/1.02      inference(superposition,[status(thm)],[c_1843,c_2544]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_27,negated_conjecture,
% 2.68/1.02      ( v1_funct_1(sK4) ),
% 2.68/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_34,plain,
% 2.68/1.02      ( v1_funct_1(sK4) = iProver_top ),
% 2.68/1.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_2752,plain,
% 2.68/1.02      ( r2_hidden(sK0(sK4,sK3),k1_relat_1(sK4)) = iProver_top
% 2.68/1.02      | sK2 = k1_xboole_0
% 2.68/1.02      | sK4 = sK3
% 2.68/1.02      | v1_relat_1(sK4) != iProver_top
% 2.68/1.02      | v1_relat_1(sK3) != iProver_top ),
% 2.68/1.02      inference(global_propositional_subsumption,
% 2.68/1.02                [status(thm)],
% 2.68/1.02                [c_2556,c_34]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_2753,plain,
% 2.68/1.02      ( sK4 = sK3
% 2.68/1.02      | sK2 = k1_xboole_0
% 2.68/1.02      | r2_hidden(sK0(sK4,sK3),k1_relat_1(sK4)) = iProver_top
% 2.68/1.02      | v1_relat_1(sK4) != iProver_top
% 2.68/1.02      | v1_relat_1(sK3) != iProver_top ),
% 2.68/1.02      inference(renaming,[status(thm)],[c_2752]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_2761,plain,
% 2.68/1.02      ( sK4 = sK3
% 2.68/1.02      | sK2 = k1_xboole_0
% 2.68/1.02      | r2_hidden(sK0(sK4,sK3),sK1) = iProver_top
% 2.68/1.02      | v1_relat_1(sK4) != iProver_top
% 2.68/1.02      | v1_relat_1(sK3) != iProver_top ),
% 2.68/1.02      inference(superposition,[status(thm)],[c_1843,c_2753]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_24,negated_conjecture,
% 2.68/1.02      ( ~ r2_hidden(X0,sK1) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ),
% 2.68/1.02      inference(cnf_transformation,[],[f67]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_1360,plain,
% 2.68/1.02      ( k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
% 2.68/1.02      | r2_hidden(X0,sK1) != iProver_top ),
% 2.68/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_2769,plain,
% 2.68/1.02      ( k1_funct_1(sK4,sK0(sK4,sK3)) = k1_funct_1(sK3,sK0(sK4,sK3))
% 2.68/1.02      | sK4 = sK3
% 2.68/1.02      | sK2 = k1_xboole_0
% 2.68/1.02      | v1_relat_1(sK4) != iProver_top
% 2.68/1.02      | v1_relat_1(sK3) != iProver_top ),
% 2.68/1.02      inference(superposition,[status(thm)],[c_2761,c_1360]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_4181,plain,
% 2.68/1.02      ( k1_funct_1(sK4,sK0(sK4,sK3)) = k1_funct_1(sK3,sK0(sK4,sK3))
% 2.68/1.02      | sK4 = sK3
% 2.68/1.02      | sK2 = k1_xboole_0
% 2.68/1.02      | v1_relat_1(sK3) != iProver_top ),
% 2.68/1.02      inference(superposition,[status(thm)],[c_4179,c_2769]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_2956,plain,
% 2.68/1.02      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 2.68/1.02      inference(superposition,[status(thm)],[c_1357,c_1366]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_4026,plain,
% 2.68/1.02      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 2.68/1.02      | v1_relat_1(sK3) = iProver_top ),
% 2.68/1.02      inference(superposition,[status(thm)],[c_2956,c_1355]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_4204,plain,
% 2.68/1.02      ( v1_relat_1(sK3) = iProver_top ),
% 2.68/1.02      inference(forward_subsumption_resolution,
% 2.68/1.02                [status(thm)],
% 2.68/1.02                [c_4026,c_1364]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_4342,plain,
% 2.68/1.02      ( sK2 = k1_xboole_0
% 2.68/1.02      | sK4 = sK3
% 2.68/1.02      | k1_funct_1(sK4,sK0(sK4,sK3)) = k1_funct_1(sK3,sK0(sK4,sK3)) ),
% 2.68/1.02      inference(global_propositional_subsumption,
% 2.68/1.02                [status(thm)],
% 2.68/1.02                [c_4181,c_2770,c_4180,c_4205]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_4343,plain,
% 2.68/1.02      ( k1_funct_1(sK4,sK0(sK4,sK3)) = k1_funct_1(sK3,sK0(sK4,sK3))
% 2.68/1.02      | sK4 = sK3
% 2.68/1.02      | sK2 = k1_xboole_0 ),
% 2.68/1.02      inference(renaming,[status(thm)],[c_4342]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_12,plain,
% 2.68/1.02      ( ~ v1_funct_1(X0)
% 2.68/1.02      | ~ v1_funct_1(X1)
% 2.68/1.02      | ~ v1_relat_1(X1)
% 2.68/1.02      | ~ v1_relat_1(X0)
% 2.68/1.02      | X0 = X1
% 2.68/1.02      | k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
% 2.68/1.02      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 2.68/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_1363,plain,
% 2.68/1.02      ( X0 = X1
% 2.68/1.02      | k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
% 2.68/1.02      | k1_relat_1(X0) != k1_relat_1(X1)
% 2.68/1.02      | v1_funct_1(X1) != iProver_top
% 2.68/1.02      | v1_funct_1(X0) != iProver_top
% 2.68/1.02      | v1_relat_1(X0) != iProver_top
% 2.68/1.02      | v1_relat_1(X1) != iProver_top ),
% 2.68/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_4347,plain,
% 2.68/1.02      ( k1_relat_1(sK3) != k1_relat_1(sK4)
% 2.68/1.02      | sK4 = sK3
% 2.68/1.02      | sK2 = k1_xboole_0
% 2.68/1.02      | v1_funct_1(sK4) != iProver_top
% 2.68/1.02      | v1_funct_1(sK3) != iProver_top
% 2.68/1.02      | v1_relat_1(sK4) != iProver_top
% 2.68/1.02      | v1_relat_1(sK3) != iProver_top ),
% 2.68/1.02      inference(superposition,[status(thm)],[c_4343,c_1363]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_4930,plain,
% 2.68/1.02      ( k1_relat_1(sK3) != k1_relat_1(sK4)
% 2.68/1.02      | sK4 = sK3
% 2.68/1.02      | sK2 = k1_xboole_0 ),
% 2.68/1.02      inference(global_propositional_subsumption,
% 2.68/1.02                [status(thm)],
% 2.68/1.02                [c_4347,c_30,c_27,c_4180,c_4205,c_4348]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_4935,plain,
% 2.68/1.02      ( k1_relat_1(sK3) != sK1 | sK4 = sK3 | sK2 = k1_xboole_0 ),
% 2.68/1.02      inference(superposition,[status(thm)],[c_1843,c_4930]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_4936,plain,
% 2.68/1.02      ( sK4 = sK3 | sK2 = k1_xboole_0 ),
% 2.68/1.02      inference(global_propositional_subsumption,
% 2.68/1.02                [status(thm)],
% 2.68/1.02                [c_4935,c_1935]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_15,plain,
% 2.68/1.02      ( r2_relset_1(X0,X1,X2,X2)
% 2.68/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.68/1.02      inference(cnf_transformation,[],[f73]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_23,negated_conjecture,
% 2.68/1.02      ( ~ r2_relset_1(sK1,sK2,sK3,sK4) ),
% 2.68/1.02      inference(cnf_transformation,[],[f68]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_375,plain,
% 2.68/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/1.02      | sK4 != X0
% 2.68/1.02      | sK3 != X0
% 2.68/1.02      | sK2 != X2
% 2.68/1.02      | sK1 != X1 ),
% 2.68/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_23]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_376,plain,
% 2.68/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.68/1.02      | sK3 != sK4 ),
% 2.68/1.02      inference(unflattening,[status(thm)],[c_375]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_378,plain,
% 2.68/1.02      ( sK3 != sK4 ),
% 2.68/1.02      inference(global_propositional_subsumption,
% 2.68/1.02                [status(thm)],
% 2.68/1.02                [c_376,c_25]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_4953,plain,
% 2.68/1.02      ( sK2 = k1_xboole_0 ),
% 2.68/1.02      inference(superposition,[status(thm)],[c_4936,c_378]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_5154,plain,
% 2.68/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 2.68/1.02      inference(demodulation,[status(thm)],[c_4953,c_1359]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_3,plain,
% 2.68/1.02      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.68/1.02      inference(cnf_transformation,[],[f71]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_5160,plain,
% 2.68/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.68/1.02      inference(demodulation,[status(thm)],[c_5154,c_3]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_5155,plain,
% 2.68/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 2.68/1.02      inference(demodulation,[status(thm)],[c_4953,c_1357]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_5157,plain,
% 2.68/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.68/1.02      inference(demodulation,[status(thm)],[c_5155,c_3]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_3078,plain,
% 2.68/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) | r1_tarski(sK3,X0) ),
% 2.68/1.02      inference(instantiation,[status(thm)],[c_8]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_3079,plain,
% 2.68/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 2.68/1.02      | r1_tarski(sK3,X0) = iProver_top ),
% 2.68/1.02      inference(predicate_to_equality,[status(thm)],[c_3078]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_3081,plain,
% 2.68/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.68/1.02      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 2.68/1.02      inference(instantiation,[status(thm)],[c_3079]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_2827,plain,
% 2.68/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0)) | r1_tarski(sK4,X0) ),
% 2.68/1.02      inference(instantiation,[status(thm)],[c_8]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_2828,plain,
% 2.68/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 2.68/1.02      | r1_tarski(sK4,X0) = iProver_top ),
% 2.68/1.02      inference(predicate_to_equality,[status(thm)],[c_2827]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_2830,plain,
% 2.68/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.68/1.02      | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 2.68/1.02      inference(instantiation,[status(thm)],[c_2828]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_6,plain,
% 2.68/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.68/1.02      inference(cnf_transformation,[],[f44]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_2058,plain,
% 2.68/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) ),
% 2.68/1.02      inference(instantiation,[status(thm)],[c_6]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_2061,plain,
% 2.68/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) = iProver_top ),
% 2.68/1.02      inference(predicate_to_equality,[status(thm)],[c_2058]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_2049,plain,
% 2.68/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) ),
% 2.68/1.02      inference(instantiation,[status(thm)],[c_6]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_2052,plain,
% 2.68/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) = iProver_top ),
% 2.68/1.02      inference(predicate_to_equality,[status(thm)],[c_2049]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_0,plain,
% 2.68/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.68/1.02      inference(cnf_transformation,[],[f40]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_1815,plain,
% 2.68/1.02      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 2.68/1.02      inference(instantiation,[status(thm)],[c_0]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_1816,plain,
% 2.68/1.02      ( sK3 = X0
% 2.68/1.02      | r1_tarski(X0,sK3) != iProver_top
% 2.68/1.02      | r1_tarski(sK3,X0) != iProver_top ),
% 2.68/1.02      inference(predicate_to_equality,[status(thm)],[c_1815]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_1818,plain,
% 2.68/1.02      ( sK3 = k1_xboole_0
% 2.68/1.02      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 2.68/1.02      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 2.68/1.02      inference(instantiation,[status(thm)],[c_1816]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_1798,plain,
% 2.68/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3)) | r1_tarski(X0,sK3) ),
% 2.68/1.02      inference(instantiation,[status(thm)],[c_8]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_1799,plain,
% 2.68/1.02      ( m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
% 2.68/1.02      | r1_tarski(X0,sK3) = iProver_top ),
% 2.68/1.02      inference(predicate_to_equality,[status(thm)],[c_1798]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_1801,plain,
% 2.68/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
% 2.68/1.02      | r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 2.68/1.02      inference(instantiation,[status(thm)],[c_1799]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_1779,plain,
% 2.68/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4)) | r1_tarski(X0,sK4) ),
% 2.68/1.02      inference(instantiation,[status(thm)],[c_8]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_1780,plain,
% 2.68/1.02      ( m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
% 2.68/1.02      | r1_tarski(X0,sK4) = iProver_top ),
% 2.68/1.02      inference(predicate_to_equality,[status(thm)],[c_1779]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_1782,plain,
% 2.68/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) != iProver_top
% 2.68/1.02      | r1_tarski(k1_xboole_0,sK4) = iProver_top ),
% 2.68/1.02      inference(instantiation,[status(thm)],[c_1780]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_1726,plain,
% 2.68/1.02      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | sK4 = X0 ),
% 2.68/1.02      inference(instantiation,[status(thm)],[c_0]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_1727,plain,
% 2.68/1.02      ( sK4 = X0
% 2.68/1.02      | r1_tarski(X0,sK4) != iProver_top
% 2.68/1.02      | r1_tarski(sK4,X0) != iProver_top ),
% 2.68/1.02      inference(predicate_to_equality,[status(thm)],[c_1726]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_1729,plain,
% 2.68/1.02      ( sK4 = k1_xboole_0
% 2.68/1.02      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 2.68/1.02      | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 2.68/1.02      inference(instantiation,[status(thm)],[c_1727]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_843,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_1574,plain,
% 2.68/1.02      ( sK4 != X0 | sK3 != X0 | sK3 = sK4 ),
% 2.68/1.02      inference(instantiation,[status(thm)],[c_843]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(c_1575,plain,
% 2.68/1.02      ( sK4 != k1_xboole_0 | sK3 = sK4 | sK3 != k1_xboole_0 ),
% 2.68/1.02      inference(instantiation,[status(thm)],[c_1574]) ).
% 2.68/1.02  
% 2.68/1.02  cnf(contradiction,plain,
% 2.68/1.02      ( $false ),
% 2.68/1.02      inference(minisat,
% 2.68/1.02                [status(thm)],
% 2.68/1.02                [c_5160,c_5157,c_3081,c_2830,c_2061,c_2052,c_1818,c_1801,
% 2.68/1.02                 c_1782,c_1729,c_1575,c_376,c_25]) ).
% 2.68/1.02  
% 2.68/1.02  
% 2.68/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.68/1.02  
% 2.68/1.02  ------                               Statistics
% 2.68/1.02  
% 2.68/1.02  ------ General
% 2.68/1.02  
% 2.68/1.02  abstr_ref_over_cycles:                  0
% 2.68/1.02  abstr_ref_under_cycles:                 0
% 2.68/1.02  gc_basic_clause_elim:                   0
% 2.68/1.02  forced_gc_time:                         0
% 2.68/1.02  parsing_time:                           0.008
% 2.68/1.02  unif_index_cands_time:                  0.
% 2.68/1.02  unif_index_add_time:                    0.
% 2.68/1.02  orderings_time:                         0.
% 2.68/1.02  out_proof_time:                         0.01
% 2.68/1.02  total_time:                             0.142
% 2.68/1.02  num_of_symbols:                         49
% 2.68/1.02  num_of_terms:                           4462
% 2.68/1.02  
% 2.68/1.02  ------ Preprocessing
% 2.68/1.02  
% 2.68/1.02  num_of_splits:                          0
% 2.68/1.02  num_of_split_atoms:                     0
% 2.68/1.02  num_of_reused_defs:                     0
% 2.68/1.02  num_eq_ax_congr_red:                    17
% 2.68/1.02  num_of_sem_filtered_clauses:            1
% 2.68/1.02  num_of_subtypes:                        0
% 2.68/1.02  monotx_restored_types:                  0
% 2.68/1.02  sat_num_of_epr_types:                   0
% 2.68/1.02  sat_num_of_non_cyclic_types:            0
% 2.68/1.02  sat_guarded_non_collapsed_types:        0
% 2.68/1.02  num_pure_diseq_elim:                    0
% 2.68/1.02  simp_replaced_by:                       0
% 2.68/1.02  res_preprocessed:                       129
% 2.68/1.02  prep_upred:                             0
% 2.68/1.02  prep_unflattend:                        47
% 2.68/1.02  smt_new_axioms:                         0
% 2.68/1.02  pred_elim_cands:                        5
% 2.68/1.02  pred_elim:                              2
% 2.68/1.02  pred_elim_cl:                           4
% 2.68/1.02  pred_elim_cycles:                       5
% 2.68/1.02  merged_defs:                            8
% 2.68/1.02  merged_defs_ncl:                        0
% 2.68/1.02  bin_hyper_res:                          9
% 2.68/1.02  prep_cycles:                            4
% 2.68/1.02  pred_elim_time:                         0.004
% 2.68/1.02  splitting_time:                         0.
% 2.68/1.02  sem_filter_time:                        0.
% 2.68/1.02  monotx_time:                            0.
% 2.68/1.02  subtype_inf_time:                       0.
% 2.68/1.02  
% 2.68/1.02  ------ Problem properties
% 2.68/1.02  
% 2.68/1.02  clauses:                                26
% 2.68/1.02  conjectures:                            5
% 2.68/1.02  epr:                                    6
% 2.68/1.02  horn:                                   20
% 2.68/1.02  ground:                                 11
% 2.68/1.02  unary:                                  10
% 2.68/1.02  binary:                                 6
% 2.68/1.02  lits:                                   62
% 2.68/1.02  lits_eq:                                28
% 2.68/1.02  fd_pure:                                0
% 2.68/1.02  fd_pseudo:                              0
% 2.68/1.02  fd_cond:                                1
% 2.68/1.02  fd_pseudo_cond:                         3
% 2.68/1.02  ac_symbols:                             0
% 2.68/1.02  
% 2.68/1.02  ------ Propositional Solver
% 2.68/1.02  
% 2.68/1.02  prop_solver_calls:                      29
% 2.68/1.02  prop_fast_solver_calls:                 984
% 2.68/1.02  smt_solver_calls:                       0
% 2.68/1.02  smt_fast_solver_calls:                  0
% 2.68/1.02  prop_num_of_clauses:                    1673
% 2.68/1.02  prop_preprocess_simplified:             5017
% 2.68/1.02  prop_fo_subsumed:                       27
% 2.68/1.02  prop_solver_time:                       0.
% 2.68/1.02  smt_solver_time:                        0.
% 2.68/1.02  smt_fast_solver_time:                   0.
% 2.68/1.02  prop_fast_solver_time:                  0.
% 2.68/1.02  prop_unsat_core_time:                   0.
% 2.68/1.02  
% 2.68/1.02  ------ QBF
% 2.68/1.02  
% 2.68/1.02  qbf_q_res:                              0
% 2.68/1.02  qbf_num_tautologies:                    0
% 2.68/1.02  qbf_prep_cycles:                        0
% 2.68/1.02  
% 2.68/1.02  ------ BMC1
% 2.68/1.02  
% 2.68/1.02  bmc1_current_bound:                     -1
% 2.68/1.02  bmc1_last_solved_bound:                 -1
% 2.68/1.02  bmc1_unsat_core_size:                   -1
% 2.68/1.02  bmc1_unsat_core_parents_size:           -1
% 2.68/1.02  bmc1_merge_next_fun:                    0
% 2.68/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.68/1.02  
% 2.68/1.02  ------ Instantiation
% 2.68/1.02  
% 2.68/1.02  inst_num_of_clauses:                    607
% 2.68/1.02  inst_num_in_passive:                    219
% 2.68/1.02  inst_num_in_active:                     324
% 2.68/1.02  inst_num_in_unprocessed:                64
% 2.68/1.02  inst_num_of_loops:                      350
% 2.68/1.02  inst_num_of_learning_restarts:          0
% 2.68/1.02  inst_num_moves_active_passive:          22
% 2.68/1.02  inst_lit_activity:                      0
% 2.68/1.02  inst_lit_activity_moves:                0
% 2.68/1.02  inst_num_tautologies:                   0
% 2.68/1.02  inst_num_prop_implied:                  0
% 2.68/1.02  inst_num_existing_simplified:           0
% 2.68/1.02  inst_num_eq_res_simplified:             0
% 2.68/1.02  inst_num_child_elim:                    0
% 2.68/1.02  inst_num_of_dismatching_blockings:      140
% 2.68/1.02  inst_num_of_non_proper_insts:           710
% 2.68/1.02  inst_num_of_duplicates:                 0
% 2.68/1.02  inst_inst_num_from_inst_to_res:         0
% 2.68/1.02  inst_dismatching_checking_time:         0.
% 2.68/1.02  
% 2.68/1.02  ------ Resolution
% 2.68/1.02  
% 2.68/1.02  res_num_of_clauses:                     0
% 2.68/1.02  res_num_in_passive:                     0
% 2.68/1.02  res_num_in_active:                      0
% 2.68/1.02  res_num_of_loops:                       133
% 2.68/1.02  res_forward_subset_subsumed:            29
% 2.68/1.02  res_backward_subset_subsumed:           0
% 2.68/1.02  res_forward_subsumed:                   0
% 2.68/1.02  res_backward_subsumed:                  0
% 2.68/1.02  res_forward_subsumption_resolution:     0
% 2.68/1.02  res_backward_subsumption_resolution:    0
% 2.68/1.02  res_clause_to_clause_subsumption:       251
% 2.68/1.02  res_orphan_elimination:                 0
% 2.68/1.02  res_tautology_del:                      54
% 2.68/1.02  res_num_eq_res_simplified:              0
% 2.68/1.02  res_num_sel_changes:                    0
% 2.68/1.02  res_moves_from_active_to_pass:          0
% 2.68/1.02  
% 2.68/1.02  ------ Superposition
% 2.68/1.02  
% 2.68/1.02  sup_time_total:                         0.
% 2.68/1.02  sup_time_generating:                    0.
% 2.68/1.02  sup_time_sim_full:                      0.
% 2.68/1.02  sup_time_sim_immed:                     0.
% 2.68/1.02  
% 2.68/1.02  sup_num_of_clauses:                     57
% 2.68/1.02  sup_num_in_active:                      36
% 2.68/1.02  sup_num_in_passive:                     21
% 2.68/1.02  sup_num_of_loops:                       68
% 2.68/1.02  sup_fw_superposition:                   60
% 2.68/1.02  sup_bw_superposition:                   47
% 2.68/1.02  sup_immediate_simplified:               24
% 2.68/1.02  sup_given_eliminated:                   1
% 2.68/1.02  comparisons_done:                       0
% 2.68/1.02  comparisons_avoided:                    57
% 2.68/1.02  
% 2.68/1.02  ------ Simplifications
% 2.68/1.02  
% 2.68/1.02  
% 2.68/1.02  sim_fw_subset_subsumed:                 10
% 2.68/1.02  sim_bw_subset_subsumed:                 18
% 2.68/1.02  sim_fw_subsumed:                        4
% 2.68/1.02  sim_bw_subsumed:                        1
% 2.68/1.02  sim_fw_subsumption_res:                 6
% 2.68/1.02  sim_bw_subsumption_res:                 0
% 2.68/1.02  sim_tautology_del:                      2
% 2.68/1.02  sim_eq_tautology_del:                   16
% 2.68/1.02  sim_eq_res_simp:                        2
% 2.68/1.02  sim_fw_demodulated:                     12
% 2.68/1.02  sim_bw_demodulated:                     21
% 2.68/1.02  sim_light_normalised:                   2
% 2.68/1.02  sim_joinable_taut:                      0
% 2.68/1.02  sim_joinable_simp:                      0
% 2.68/1.02  sim_ac_normalised:                      0
% 2.68/1.02  sim_smt_subsumption:                    0
% 2.68/1.02  
%------------------------------------------------------------------------------
