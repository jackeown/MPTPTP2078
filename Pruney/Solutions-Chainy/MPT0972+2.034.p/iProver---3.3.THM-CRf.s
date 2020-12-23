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
% DateTime   : Thu Dec  3 12:01:14 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :  153 (2822 expanded)
%              Number of clauses        :   90 ( 831 expanded)
%              Number of leaves         :   18 ( 710 expanded)
%              Depth                    :   27
%              Number of atoms          :  511 (18509 expanded)
%              Number of equality atoms :  259 (4435 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f43,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK5)
        & ! [X4] :
            ( k1_funct_1(sK5,X4) = k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK5,X0,X1)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
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
          ( ~ r2_relset_1(sK2,sK3,sK4,X3)
          & ! [X4] :
              ( k1_funct_1(sK4,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,sK2) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
          & v1_funct_2(X3,sK2,sK3)
          & v1_funct_1(X3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ~ r2_relset_1(sK2,sK3,sK4,sK5)
    & ! [X4] :
        ( k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4)
        | ~ r2_hidden(X4,sK2) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK5,sK2,sK3)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f28,f40,f39])).

fof(f68,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
            & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f35])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f67,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f57])).

fof(f71,plain,(
    ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f70,plain,(
    ! [X4] :
      ( k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4)
      | ~ r2_hidden(X4,sK2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f33])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f48])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_948,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_386,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_25])).

cnf(c_387,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_389,plain,
    ( k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_387,c_24])).

cnf(c_936,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_938,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1333,plain,
    ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_936,c_938])).

cnf(c_1508,plain,
    ( k1_relat_1(sK5) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_389,c_1333])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_397,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_28])).

cnf(c_398,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_400,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_398,c_27])).

cnf(c_934,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1334,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_934,c_938])).

cnf(c_1583,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_400,c_1334])).

cnf(c_11,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | X1 = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_940,plain,
    ( X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1)
    | r2_hidden(sK1(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2431,plain,
    ( k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1508,c_940])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_33,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_35,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1147,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1148,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1147])).

cnf(c_3095,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2431,c_33,c_35,c_1148])).

cnf(c_3096,plain,
    ( k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3095])).

cnf(c_3108,plain,
    ( sK5 = sK4
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1583,c_3096])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_30,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_32,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_14,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_22,negated_conjecture,
    ( ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_303,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK5 != X0
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_304,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | sK4 != sK5 ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_1150,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1151,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1150])).

cnf(c_567,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1280,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_567])).

cnf(c_568,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1163,plain,
    ( sK5 != X0
    | sK4 != X0
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_568])).

cnf(c_1573,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1163])).

cnf(c_3395,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3108,c_30,c_32,c_24,c_304,c_1151,c_1280,c_1573])).

cnf(c_3401,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1583,c_3395])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_937,plain,
    ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3417,plain,
    ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3401,c_937])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X0 = X1
    | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_941,plain,
    ( X0 = X1
    | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3563,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4
    | sK3 = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3417,c_941])).

cnf(c_3564,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3563])).

cnf(c_3566,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3563,c_29,c_27,c_26,c_24,c_304,c_1147,c_1150,c_1280,c_1573,c_3564])).

cnf(c_3570,plain,
    ( k1_relat_1(sK4) != sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1508,c_3566])).

cnf(c_3650,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3570,c_1583])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_942,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2645,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_934,c_942])).

cnf(c_3659,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3650,c_2645])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3714,plain,
    ( m1_subset_1(X0,k1_xboole_0) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3659,c_4])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_88,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_944,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2712,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_934,c_944])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_947,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2882,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2712,c_947])).

cnf(c_3655,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK2,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3650,c_2882])).

cnf(c_3734,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3655,c_4])).

cnf(c_3869,plain,
    ( r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3714,c_88,c_3734])).

cnf(c_3876,plain,
    ( v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_948,c_3869])).

cnf(c_2644,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_936,c_942])).

cnf(c_3660,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3650,c_2644])).

cnf(c_3709,plain,
    ( m1_subset_1(X0,k1_xboole_0) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3660,c_4])).

cnf(c_2711,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_936,c_944])).

cnf(c_2789,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2711,c_947])).

cnf(c_3656,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK2,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3650,c_2789])).

cnf(c_3729,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3656,c_4])).

cnf(c_3859,plain,
    ( r2_hidden(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3709,c_88,c_3729])).

cnf(c_3866,plain,
    ( v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_948,c_3859])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1126,plain,
    ( ~ v1_xboole_0(sK5)
    | ~ v1_xboole_0(sK4)
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1127,plain,
    ( sK4 = sK5
    | v1_xboole_0(sK5) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1126])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3876,c_3866,c_1127,c_304,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:55:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.34/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.01  
% 2.34/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.34/1.01  
% 2.34/1.01  ------  iProver source info
% 2.34/1.01  
% 2.34/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.34/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.34/1.01  git: non_committed_changes: false
% 2.34/1.01  git: last_make_outside_of_git: false
% 2.34/1.01  
% 2.34/1.01  ------ 
% 2.34/1.01  
% 2.34/1.01  ------ Input Options
% 2.34/1.01  
% 2.34/1.01  --out_options                           all
% 2.34/1.01  --tptp_safe_out                         true
% 2.34/1.01  --problem_path                          ""
% 2.34/1.01  --include_path                          ""
% 2.34/1.01  --clausifier                            res/vclausify_rel
% 2.34/1.01  --clausifier_options                    --mode clausify
% 2.34/1.01  --stdin                                 false
% 2.34/1.01  --stats_out                             all
% 2.34/1.01  
% 2.34/1.01  ------ General Options
% 2.34/1.01  
% 2.34/1.01  --fof                                   false
% 2.34/1.01  --time_out_real                         305.
% 2.34/1.01  --time_out_virtual                      -1.
% 2.34/1.01  --symbol_type_check                     false
% 2.34/1.01  --clausify_out                          false
% 2.34/1.01  --sig_cnt_out                           false
% 2.34/1.01  --trig_cnt_out                          false
% 2.34/1.01  --trig_cnt_out_tolerance                1.
% 2.34/1.01  --trig_cnt_out_sk_spl                   false
% 2.34/1.01  --abstr_cl_out                          false
% 2.34/1.01  
% 2.34/1.01  ------ Global Options
% 2.34/1.01  
% 2.34/1.01  --schedule                              default
% 2.34/1.01  --add_important_lit                     false
% 2.34/1.01  --prop_solver_per_cl                    1000
% 2.34/1.01  --min_unsat_core                        false
% 2.34/1.01  --soft_assumptions                      false
% 2.34/1.01  --soft_lemma_size                       3
% 2.34/1.01  --prop_impl_unit_size                   0
% 2.34/1.01  --prop_impl_unit                        []
% 2.34/1.01  --share_sel_clauses                     true
% 2.34/1.01  --reset_solvers                         false
% 2.34/1.01  --bc_imp_inh                            [conj_cone]
% 2.34/1.01  --conj_cone_tolerance                   3.
% 2.34/1.01  --extra_neg_conj                        none
% 2.34/1.01  --large_theory_mode                     true
% 2.34/1.01  --prolific_symb_bound                   200
% 2.34/1.01  --lt_threshold                          2000
% 2.34/1.01  --clause_weak_htbl                      true
% 2.34/1.01  --gc_record_bc_elim                     false
% 2.34/1.01  
% 2.34/1.01  ------ Preprocessing Options
% 2.34/1.01  
% 2.34/1.01  --preprocessing_flag                    true
% 2.34/1.01  --time_out_prep_mult                    0.1
% 2.34/1.01  --splitting_mode                        input
% 2.34/1.01  --splitting_grd                         true
% 2.34/1.01  --splitting_cvd                         false
% 2.34/1.01  --splitting_cvd_svl                     false
% 2.34/1.01  --splitting_nvd                         32
% 2.34/1.01  --sub_typing                            true
% 2.34/1.01  --prep_gs_sim                           true
% 2.34/1.01  --prep_unflatten                        true
% 2.34/1.01  --prep_res_sim                          true
% 2.34/1.01  --prep_upred                            true
% 2.34/1.01  --prep_sem_filter                       exhaustive
% 2.34/1.01  --prep_sem_filter_out                   false
% 2.34/1.01  --pred_elim                             true
% 2.34/1.01  --res_sim_input                         true
% 2.34/1.01  --eq_ax_congr_red                       true
% 2.34/1.01  --pure_diseq_elim                       true
% 2.34/1.01  --brand_transform                       false
% 2.34/1.01  --non_eq_to_eq                          false
% 2.34/1.01  --prep_def_merge                        true
% 2.34/1.01  --prep_def_merge_prop_impl              false
% 2.34/1.01  --prep_def_merge_mbd                    true
% 2.34/1.01  --prep_def_merge_tr_red                 false
% 2.34/1.01  --prep_def_merge_tr_cl                  false
% 2.34/1.01  --smt_preprocessing                     true
% 2.34/1.01  --smt_ac_axioms                         fast
% 2.34/1.01  --preprocessed_out                      false
% 2.34/1.01  --preprocessed_stats                    false
% 2.34/1.01  
% 2.34/1.01  ------ Abstraction refinement Options
% 2.34/1.01  
% 2.34/1.01  --abstr_ref                             []
% 2.34/1.01  --abstr_ref_prep                        false
% 2.34/1.01  --abstr_ref_until_sat                   false
% 2.34/1.01  --abstr_ref_sig_restrict                funpre
% 2.34/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.34/1.01  --abstr_ref_under                       []
% 2.34/1.01  
% 2.34/1.01  ------ SAT Options
% 2.34/1.01  
% 2.34/1.01  --sat_mode                              false
% 2.34/1.01  --sat_fm_restart_options                ""
% 2.34/1.01  --sat_gr_def                            false
% 2.34/1.01  --sat_epr_types                         true
% 2.34/1.01  --sat_non_cyclic_types                  false
% 2.34/1.01  --sat_finite_models                     false
% 2.34/1.01  --sat_fm_lemmas                         false
% 2.34/1.01  --sat_fm_prep                           false
% 2.34/1.01  --sat_fm_uc_incr                        true
% 2.34/1.01  --sat_out_model                         small
% 2.34/1.01  --sat_out_clauses                       false
% 2.34/1.01  
% 2.34/1.01  ------ QBF Options
% 2.34/1.01  
% 2.34/1.01  --qbf_mode                              false
% 2.34/1.01  --qbf_elim_univ                         false
% 2.34/1.01  --qbf_dom_inst                          none
% 2.34/1.01  --qbf_dom_pre_inst                      false
% 2.34/1.01  --qbf_sk_in                             false
% 2.34/1.01  --qbf_pred_elim                         true
% 2.34/1.01  --qbf_split                             512
% 2.34/1.01  
% 2.34/1.01  ------ BMC1 Options
% 2.34/1.01  
% 2.34/1.01  --bmc1_incremental                      false
% 2.34/1.01  --bmc1_axioms                           reachable_all
% 2.34/1.01  --bmc1_min_bound                        0
% 2.34/1.01  --bmc1_max_bound                        -1
% 2.34/1.01  --bmc1_max_bound_default                -1
% 2.34/1.01  --bmc1_symbol_reachability              true
% 2.34/1.01  --bmc1_property_lemmas                  false
% 2.34/1.01  --bmc1_k_induction                      false
% 2.34/1.01  --bmc1_non_equiv_states                 false
% 2.34/1.01  --bmc1_deadlock                         false
% 2.34/1.01  --bmc1_ucm                              false
% 2.34/1.01  --bmc1_add_unsat_core                   none
% 2.34/1.01  --bmc1_unsat_core_children              false
% 2.34/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.34/1.01  --bmc1_out_stat                         full
% 2.34/1.01  --bmc1_ground_init                      false
% 2.34/1.01  --bmc1_pre_inst_next_state              false
% 2.34/1.01  --bmc1_pre_inst_state                   false
% 2.34/1.01  --bmc1_pre_inst_reach_state             false
% 2.34/1.01  --bmc1_out_unsat_core                   false
% 2.34/1.01  --bmc1_aig_witness_out                  false
% 2.34/1.01  --bmc1_verbose                          false
% 2.34/1.01  --bmc1_dump_clauses_tptp                false
% 2.34/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.34/1.01  --bmc1_dump_file                        -
% 2.34/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.34/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.34/1.01  --bmc1_ucm_extend_mode                  1
% 2.34/1.01  --bmc1_ucm_init_mode                    2
% 2.34/1.01  --bmc1_ucm_cone_mode                    none
% 2.34/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.34/1.01  --bmc1_ucm_relax_model                  4
% 2.34/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.34/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.34/1.01  --bmc1_ucm_layered_model                none
% 2.34/1.01  --bmc1_ucm_max_lemma_size               10
% 2.34/1.01  
% 2.34/1.01  ------ AIG Options
% 2.34/1.01  
% 2.34/1.01  --aig_mode                              false
% 2.34/1.01  
% 2.34/1.01  ------ Instantiation Options
% 2.34/1.01  
% 2.34/1.01  --instantiation_flag                    true
% 2.34/1.01  --inst_sos_flag                         false
% 2.34/1.01  --inst_sos_phase                        true
% 2.34/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.34/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.34/1.01  --inst_lit_sel_side                     num_symb
% 2.34/1.01  --inst_solver_per_active                1400
% 2.34/1.01  --inst_solver_calls_frac                1.
% 2.34/1.01  --inst_passive_queue_type               priority_queues
% 2.34/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.34/1.01  --inst_passive_queues_freq              [25;2]
% 2.34/1.01  --inst_dismatching                      true
% 2.34/1.01  --inst_eager_unprocessed_to_passive     true
% 2.34/1.01  --inst_prop_sim_given                   true
% 2.34/1.01  --inst_prop_sim_new                     false
% 2.34/1.01  --inst_subs_new                         false
% 2.34/1.01  --inst_eq_res_simp                      false
% 2.34/1.01  --inst_subs_given                       false
% 2.34/1.01  --inst_orphan_elimination               true
% 2.34/1.01  --inst_learning_loop_flag               true
% 2.34/1.01  --inst_learning_start                   3000
% 2.34/1.01  --inst_learning_factor                  2
% 2.34/1.01  --inst_start_prop_sim_after_learn       3
% 2.34/1.01  --inst_sel_renew                        solver
% 2.34/1.01  --inst_lit_activity_flag                true
% 2.34/1.01  --inst_restr_to_given                   false
% 2.34/1.01  --inst_activity_threshold               500
% 2.34/1.01  --inst_out_proof                        true
% 2.34/1.01  
% 2.34/1.01  ------ Resolution Options
% 2.34/1.01  
% 2.34/1.01  --resolution_flag                       true
% 2.34/1.01  --res_lit_sel                           adaptive
% 2.34/1.01  --res_lit_sel_side                      none
% 2.34/1.01  --res_ordering                          kbo
% 2.34/1.01  --res_to_prop_solver                    active
% 2.34/1.01  --res_prop_simpl_new                    false
% 2.34/1.01  --res_prop_simpl_given                  true
% 2.34/1.01  --res_passive_queue_type                priority_queues
% 2.34/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.34/1.01  --res_passive_queues_freq               [15;5]
% 2.34/1.01  --res_forward_subs                      full
% 2.34/1.01  --res_backward_subs                     full
% 2.34/1.01  --res_forward_subs_resolution           true
% 2.34/1.01  --res_backward_subs_resolution          true
% 2.34/1.01  --res_orphan_elimination                true
% 2.34/1.01  --res_time_limit                        2.
% 2.34/1.01  --res_out_proof                         true
% 2.34/1.01  
% 2.34/1.01  ------ Superposition Options
% 2.34/1.01  
% 2.34/1.01  --superposition_flag                    true
% 2.34/1.01  --sup_passive_queue_type                priority_queues
% 2.34/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.34/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.34/1.01  --demod_completeness_check              fast
% 2.34/1.01  --demod_use_ground                      true
% 2.34/1.01  --sup_to_prop_solver                    passive
% 2.34/1.01  --sup_prop_simpl_new                    true
% 2.34/1.01  --sup_prop_simpl_given                  true
% 2.34/1.01  --sup_fun_splitting                     false
% 2.34/1.01  --sup_smt_interval                      50000
% 2.34/1.01  
% 2.34/1.01  ------ Superposition Simplification Setup
% 2.34/1.01  
% 2.34/1.01  --sup_indices_passive                   []
% 2.34/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.34/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.01  --sup_full_bw                           [BwDemod]
% 2.34/1.01  --sup_immed_triv                        [TrivRules]
% 2.34/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.34/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.01  --sup_immed_bw_main                     []
% 2.34/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.34/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/1.01  
% 2.34/1.01  ------ Combination Options
% 2.34/1.01  
% 2.34/1.01  --comb_res_mult                         3
% 2.34/1.01  --comb_sup_mult                         2
% 2.34/1.01  --comb_inst_mult                        10
% 2.34/1.01  
% 2.34/1.01  ------ Debug Options
% 2.34/1.01  
% 2.34/1.01  --dbg_backtrace                         false
% 2.34/1.01  --dbg_dump_prop_clauses                 false
% 2.34/1.01  --dbg_dump_prop_clauses_file            -
% 2.34/1.01  --dbg_out_stat                          false
% 2.34/1.01  ------ Parsing...
% 2.34/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.34/1.01  
% 2.34/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.34/1.01  
% 2.34/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.34/1.01  
% 2.34/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.34/1.01  ------ Proving...
% 2.34/1.01  ------ Problem Properties 
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  clauses                                 26
% 2.34/1.01  conjectures                             5
% 2.34/1.01  EPR                                     6
% 2.34/1.01  Horn                                    19
% 2.34/1.01  unary                                   9
% 2.34/1.01  binary                                  7
% 2.34/1.01  lits                                    63
% 2.34/1.01  lits eq                                 28
% 2.34/1.01  fd_pure                                 0
% 2.34/1.01  fd_pseudo                               0
% 2.34/1.01  fd_cond                                 1
% 2.34/1.01  fd_pseudo_cond                          3
% 2.34/1.01  AC symbols                              0
% 2.34/1.01  
% 2.34/1.01  ------ Schedule dynamic 5 is on 
% 2.34/1.01  
% 2.34/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  ------ 
% 2.34/1.01  Current options:
% 2.34/1.01  ------ 
% 2.34/1.01  
% 2.34/1.01  ------ Input Options
% 2.34/1.01  
% 2.34/1.01  --out_options                           all
% 2.34/1.01  --tptp_safe_out                         true
% 2.34/1.01  --problem_path                          ""
% 2.34/1.01  --include_path                          ""
% 2.34/1.01  --clausifier                            res/vclausify_rel
% 2.34/1.01  --clausifier_options                    --mode clausify
% 2.34/1.01  --stdin                                 false
% 2.34/1.01  --stats_out                             all
% 2.34/1.01  
% 2.34/1.01  ------ General Options
% 2.34/1.01  
% 2.34/1.01  --fof                                   false
% 2.34/1.01  --time_out_real                         305.
% 2.34/1.01  --time_out_virtual                      -1.
% 2.34/1.01  --symbol_type_check                     false
% 2.34/1.01  --clausify_out                          false
% 2.34/1.01  --sig_cnt_out                           false
% 2.34/1.01  --trig_cnt_out                          false
% 2.34/1.01  --trig_cnt_out_tolerance                1.
% 2.34/1.01  --trig_cnt_out_sk_spl                   false
% 2.34/1.01  --abstr_cl_out                          false
% 2.34/1.01  
% 2.34/1.01  ------ Global Options
% 2.34/1.01  
% 2.34/1.01  --schedule                              default
% 2.34/1.01  --add_important_lit                     false
% 2.34/1.01  --prop_solver_per_cl                    1000
% 2.34/1.01  --min_unsat_core                        false
% 2.34/1.01  --soft_assumptions                      false
% 2.34/1.01  --soft_lemma_size                       3
% 2.34/1.01  --prop_impl_unit_size                   0
% 2.34/1.01  --prop_impl_unit                        []
% 2.34/1.01  --share_sel_clauses                     true
% 2.34/1.01  --reset_solvers                         false
% 2.34/1.01  --bc_imp_inh                            [conj_cone]
% 2.34/1.01  --conj_cone_tolerance                   3.
% 2.34/1.01  --extra_neg_conj                        none
% 2.34/1.01  --large_theory_mode                     true
% 2.34/1.01  --prolific_symb_bound                   200
% 2.34/1.01  --lt_threshold                          2000
% 2.34/1.01  --clause_weak_htbl                      true
% 2.34/1.01  --gc_record_bc_elim                     false
% 2.34/1.01  
% 2.34/1.01  ------ Preprocessing Options
% 2.34/1.01  
% 2.34/1.01  --preprocessing_flag                    true
% 2.34/1.01  --time_out_prep_mult                    0.1
% 2.34/1.01  --splitting_mode                        input
% 2.34/1.01  --splitting_grd                         true
% 2.34/1.01  --splitting_cvd                         false
% 2.34/1.01  --splitting_cvd_svl                     false
% 2.34/1.01  --splitting_nvd                         32
% 2.34/1.01  --sub_typing                            true
% 2.34/1.01  --prep_gs_sim                           true
% 2.34/1.01  --prep_unflatten                        true
% 2.34/1.01  --prep_res_sim                          true
% 2.34/1.01  --prep_upred                            true
% 2.34/1.01  --prep_sem_filter                       exhaustive
% 2.34/1.01  --prep_sem_filter_out                   false
% 2.34/1.01  --pred_elim                             true
% 2.34/1.01  --res_sim_input                         true
% 2.34/1.01  --eq_ax_congr_red                       true
% 2.34/1.01  --pure_diseq_elim                       true
% 2.34/1.01  --brand_transform                       false
% 2.34/1.01  --non_eq_to_eq                          false
% 2.34/1.01  --prep_def_merge                        true
% 2.34/1.01  --prep_def_merge_prop_impl              false
% 2.34/1.01  --prep_def_merge_mbd                    true
% 2.34/1.01  --prep_def_merge_tr_red                 false
% 2.34/1.01  --prep_def_merge_tr_cl                  false
% 2.34/1.01  --smt_preprocessing                     true
% 2.34/1.01  --smt_ac_axioms                         fast
% 2.34/1.01  --preprocessed_out                      false
% 2.34/1.01  --preprocessed_stats                    false
% 2.34/1.01  
% 2.34/1.01  ------ Abstraction refinement Options
% 2.34/1.01  
% 2.34/1.01  --abstr_ref                             []
% 2.34/1.01  --abstr_ref_prep                        false
% 2.34/1.01  --abstr_ref_until_sat                   false
% 2.34/1.01  --abstr_ref_sig_restrict                funpre
% 2.34/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.34/1.01  --abstr_ref_under                       []
% 2.34/1.01  
% 2.34/1.01  ------ SAT Options
% 2.34/1.01  
% 2.34/1.01  --sat_mode                              false
% 2.34/1.01  --sat_fm_restart_options                ""
% 2.34/1.01  --sat_gr_def                            false
% 2.34/1.01  --sat_epr_types                         true
% 2.34/1.01  --sat_non_cyclic_types                  false
% 2.34/1.01  --sat_finite_models                     false
% 2.34/1.01  --sat_fm_lemmas                         false
% 2.34/1.01  --sat_fm_prep                           false
% 2.34/1.01  --sat_fm_uc_incr                        true
% 2.34/1.01  --sat_out_model                         small
% 2.34/1.01  --sat_out_clauses                       false
% 2.34/1.01  
% 2.34/1.01  ------ QBF Options
% 2.34/1.01  
% 2.34/1.01  --qbf_mode                              false
% 2.34/1.01  --qbf_elim_univ                         false
% 2.34/1.01  --qbf_dom_inst                          none
% 2.34/1.01  --qbf_dom_pre_inst                      false
% 2.34/1.01  --qbf_sk_in                             false
% 2.34/1.01  --qbf_pred_elim                         true
% 2.34/1.01  --qbf_split                             512
% 2.34/1.01  
% 2.34/1.01  ------ BMC1 Options
% 2.34/1.01  
% 2.34/1.01  --bmc1_incremental                      false
% 2.34/1.01  --bmc1_axioms                           reachable_all
% 2.34/1.01  --bmc1_min_bound                        0
% 2.34/1.01  --bmc1_max_bound                        -1
% 2.34/1.01  --bmc1_max_bound_default                -1
% 2.34/1.01  --bmc1_symbol_reachability              true
% 2.34/1.01  --bmc1_property_lemmas                  false
% 2.34/1.01  --bmc1_k_induction                      false
% 2.34/1.01  --bmc1_non_equiv_states                 false
% 2.34/1.01  --bmc1_deadlock                         false
% 2.34/1.01  --bmc1_ucm                              false
% 2.34/1.01  --bmc1_add_unsat_core                   none
% 2.34/1.01  --bmc1_unsat_core_children              false
% 2.34/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.34/1.01  --bmc1_out_stat                         full
% 2.34/1.01  --bmc1_ground_init                      false
% 2.34/1.01  --bmc1_pre_inst_next_state              false
% 2.34/1.01  --bmc1_pre_inst_state                   false
% 2.34/1.01  --bmc1_pre_inst_reach_state             false
% 2.34/1.01  --bmc1_out_unsat_core                   false
% 2.34/1.01  --bmc1_aig_witness_out                  false
% 2.34/1.01  --bmc1_verbose                          false
% 2.34/1.01  --bmc1_dump_clauses_tptp                false
% 2.34/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.34/1.01  --bmc1_dump_file                        -
% 2.34/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.34/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.34/1.01  --bmc1_ucm_extend_mode                  1
% 2.34/1.01  --bmc1_ucm_init_mode                    2
% 2.34/1.01  --bmc1_ucm_cone_mode                    none
% 2.34/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.34/1.01  --bmc1_ucm_relax_model                  4
% 2.34/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.34/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.34/1.01  --bmc1_ucm_layered_model                none
% 2.34/1.01  --bmc1_ucm_max_lemma_size               10
% 2.34/1.01  
% 2.34/1.01  ------ AIG Options
% 2.34/1.01  
% 2.34/1.01  --aig_mode                              false
% 2.34/1.01  
% 2.34/1.01  ------ Instantiation Options
% 2.34/1.01  
% 2.34/1.01  --instantiation_flag                    true
% 2.34/1.01  --inst_sos_flag                         false
% 2.34/1.01  --inst_sos_phase                        true
% 2.34/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.34/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.34/1.01  --inst_lit_sel_side                     none
% 2.34/1.01  --inst_solver_per_active                1400
% 2.34/1.01  --inst_solver_calls_frac                1.
% 2.34/1.01  --inst_passive_queue_type               priority_queues
% 2.34/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.34/1.01  --inst_passive_queues_freq              [25;2]
% 2.34/1.01  --inst_dismatching                      true
% 2.34/1.01  --inst_eager_unprocessed_to_passive     true
% 2.34/1.01  --inst_prop_sim_given                   true
% 2.34/1.01  --inst_prop_sim_new                     false
% 2.34/1.01  --inst_subs_new                         false
% 2.34/1.01  --inst_eq_res_simp                      false
% 2.34/1.01  --inst_subs_given                       false
% 2.34/1.01  --inst_orphan_elimination               true
% 2.34/1.01  --inst_learning_loop_flag               true
% 2.34/1.01  --inst_learning_start                   3000
% 2.34/1.01  --inst_learning_factor                  2
% 2.34/1.01  --inst_start_prop_sim_after_learn       3
% 2.34/1.01  --inst_sel_renew                        solver
% 2.34/1.01  --inst_lit_activity_flag                true
% 2.34/1.01  --inst_restr_to_given                   false
% 2.34/1.01  --inst_activity_threshold               500
% 2.34/1.01  --inst_out_proof                        true
% 2.34/1.01  
% 2.34/1.01  ------ Resolution Options
% 2.34/1.01  
% 2.34/1.01  --resolution_flag                       false
% 2.34/1.01  --res_lit_sel                           adaptive
% 2.34/1.01  --res_lit_sel_side                      none
% 2.34/1.01  --res_ordering                          kbo
% 2.34/1.01  --res_to_prop_solver                    active
% 2.34/1.01  --res_prop_simpl_new                    false
% 2.34/1.01  --res_prop_simpl_given                  true
% 2.34/1.01  --res_passive_queue_type                priority_queues
% 2.34/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.34/1.01  --res_passive_queues_freq               [15;5]
% 2.34/1.01  --res_forward_subs                      full
% 2.34/1.01  --res_backward_subs                     full
% 2.34/1.01  --res_forward_subs_resolution           true
% 2.34/1.01  --res_backward_subs_resolution          true
% 2.34/1.01  --res_orphan_elimination                true
% 2.34/1.01  --res_time_limit                        2.
% 2.34/1.01  --res_out_proof                         true
% 2.34/1.01  
% 2.34/1.01  ------ Superposition Options
% 2.34/1.01  
% 2.34/1.01  --superposition_flag                    true
% 2.34/1.01  --sup_passive_queue_type                priority_queues
% 2.34/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.34/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.34/1.01  --demod_completeness_check              fast
% 2.34/1.01  --demod_use_ground                      true
% 2.34/1.01  --sup_to_prop_solver                    passive
% 2.34/1.01  --sup_prop_simpl_new                    true
% 2.34/1.01  --sup_prop_simpl_given                  true
% 2.34/1.01  --sup_fun_splitting                     false
% 2.34/1.01  --sup_smt_interval                      50000
% 2.34/1.01  
% 2.34/1.01  ------ Superposition Simplification Setup
% 2.34/1.01  
% 2.34/1.01  --sup_indices_passive                   []
% 2.34/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.34/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.01  --sup_full_bw                           [BwDemod]
% 2.34/1.01  --sup_immed_triv                        [TrivRules]
% 2.34/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.34/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.01  --sup_immed_bw_main                     []
% 2.34/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.34/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/1.01  
% 2.34/1.01  ------ Combination Options
% 2.34/1.01  
% 2.34/1.01  --comb_res_mult                         3
% 2.34/1.01  --comb_sup_mult                         2
% 2.34/1.01  --comb_inst_mult                        10
% 2.34/1.01  
% 2.34/1.01  ------ Debug Options
% 2.34/1.01  
% 2.34/1.01  --dbg_backtrace                         false
% 2.34/1.01  --dbg_dump_prop_clauses                 false
% 2.34/1.01  --dbg_dump_prop_clauses_file            -
% 2.34/1.01  --dbg_out_stat                          false
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  ------ Proving...
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  % SZS status Theorem for theBenchmark.p
% 2.34/1.01  
% 2.34/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.34/1.01  
% 2.34/1.01  fof(f1,axiom,(
% 2.34/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f29,plain,(
% 2.34/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.34/1.01    inference(nnf_transformation,[],[f1])).
% 2.34/1.01  
% 2.34/1.01  fof(f30,plain,(
% 2.34/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.34/1.01    inference(rectify,[],[f29])).
% 2.34/1.01  
% 2.34/1.01  fof(f31,plain,(
% 2.34/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.34/1.01    introduced(choice_axiom,[])).
% 2.34/1.01  
% 2.34/1.01  fof(f32,plain,(
% 2.34/1.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.34/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 2.34/1.01  
% 2.34/1.01  fof(f43,plain,(
% 2.34/1.01    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f32])).
% 2.34/1.01  
% 2.34/1.01  fof(f12,axiom,(
% 2.34/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f25,plain,(
% 2.34/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/1.01    inference(ennf_transformation,[],[f12])).
% 2.34/1.01  
% 2.34/1.01  fof(f26,plain,(
% 2.34/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/1.01    inference(flattening,[],[f25])).
% 2.34/1.01  
% 2.34/1.01  fof(f38,plain,(
% 2.34/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/1.01    inference(nnf_transformation,[],[f26])).
% 2.34/1.01  
% 2.34/1.01  fof(f58,plain,(
% 2.34/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.34/1.01    inference(cnf_transformation,[],[f38])).
% 2.34/1.01  
% 2.34/1.01  fof(f13,conjecture,(
% 2.34/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f14,negated_conjecture,(
% 2.34/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.34/1.01    inference(negated_conjecture,[],[f13])).
% 2.34/1.01  
% 2.34/1.01  fof(f27,plain,(
% 2.34/1.01    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.34/1.01    inference(ennf_transformation,[],[f14])).
% 2.34/1.01  
% 2.34/1.01  fof(f28,plain,(
% 2.34/1.01    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.34/1.01    inference(flattening,[],[f27])).
% 2.34/1.01  
% 2.34/1.01  fof(f40,plain,(
% 2.34/1.01    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK5) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK5,X0,X1) & v1_funct_1(sK5))) )),
% 2.34/1.01    introduced(choice_axiom,[])).
% 2.34/1.01  
% 2.34/1.01  fof(f39,plain,(
% 2.34/1.01    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK2,sK3,sK4,X3) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 2.34/1.01    introduced(choice_axiom,[])).
% 2.34/1.01  
% 2.34/1.01  fof(f41,plain,(
% 2.34/1.01    (~r2_relset_1(sK2,sK3,sK4,sK5) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4) | ~r2_hidden(X4,sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 2.34/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f28,f40,f39])).
% 2.34/1.01  
% 2.34/1.01  fof(f68,plain,(
% 2.34/1.01    v1_funct_2(sK5,sK2,sK3)),
% 2.34/1.01    inference(cnf_transformation,[],[f41])).
% 2.34/1.01  
% 2.34/1.01  fof(f69,plain,(
% 2.34/1.01    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.34/1.01    inference(cnf_transformation,[],[f41])).
% 2.34/1.01  
% 2.34/1.01  fof(f10,axiom,(
% 2.34/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f22,plain,(
% 2.34/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/1.01    inference(ennf_transformation,[],[f10])).
% 2.34/1.01  
% 2.34/1.01  fof(f55,plain,(
% 2.34/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.34/1.01    inference(cnf_transformation,[],[f22])).
% 2.34/1.01  
% 2.34/1.01  fof(f65,plain,(
% 2.34/1.01    v1_funct_2(sK4,sK2,sK3)),
% 2.34/1.01    inference(cnf_transformation,[],[f41])).
% 2.34/1.01  
% 2.34/1.01  fof(f66,plain,(
% 2.34/1.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.34/1.01    inference(cnf_transformation,[],[f41])).
% 2.34/1.01  
% 2.34/1.01  fof(f8,axiom,(
% 2.34/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 2.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f19,plain,(
% 2.34/1.01    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.34/1.01    inference(ennf_transformation,[],[f8])).
% 2.34/1.01  
% 2.34/1.01  fof(f20,plain,(
% 2.34/1.01    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.34/1.01    inference(flattening,[],[f19])).
% 2.34/1.01  
% 2.34/1.01  fof(f35,plain,(
% 2.34/1.01    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))),
% 2.34/1.01    introduced(choice_axiom,[])).
% 2.34/1.01  
% 2.34/1.01  fof(f36,plain,(
% 2.34/1.01    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.34/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f35])).
% 2.34/1.01  
% 2.34/1.01  fof(f52,plain,(
% 2.34/1.01    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f36])).
% 2.34/1.01  
% 2.34/1.01  fof(f67,plain,(
% 2.34/1.01    v1_funct_1(sK5)),
% 2.34/1.01    inference(cnf_transformation,[],[f41])).
% 2.34/1.01  
% 2.34/1.01  fof(f9,axiom,(
% 2.34/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f21,plain,(
% 2.34/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/1.01    inference(ennf_transformation,[],[f9])).
% 2.34/1.01  
% 2.34/1.01  fof(f54,plain,(
% 2.34/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.34/1.01    inference(cnf_transformation,[],[f21])).
% 2.34/1.01  
% 2.34/1.01  fof(f64,plain,(
% 2.34/1.01    v1_funct_1(sK4)),
% 2.34/1.01    inference(cnf_transformation,[],[f41])).
% 2.34/1.01  
% 2.34/1.01  fof(f11,axiom,(
% 2.34/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f23,plain,(
% 2.34/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.34/1.01    inference(ennf_transformation,[],[f11])).
% 2.34/1.01  
% 2.34/1.01  fof(f24,plain,(
% 2.34/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/1.01    inference(flattening,[],[f23])).
% 2.34/1.01  
% 2.34/1.01  fof(f37,plain,(
% 2.34/1.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/1.01    inference(nnf_transformation,[],[f24])).
% 2.34/1.01  
% 2.34/1.01  fof(f57,plain,(
% 2.34/1.01    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.34/1.01    inference(cnf_transformation,[],[f37])).
% 2.34/1.01  
% 2.34/1.01  fof(f74,plain,(
% 2.34/1.01    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.34/1.01    inference(equality_resolution,[],[f57])).
% 2.34/1.01  
% 2.34/1.01  fof(f71,plain,(
% 2.34/1.01    ~r2_relset_1(sK2,sK3,sK4,sK5)),
% 2.34/1.01    inference(cnf_transformation,[],[f41])).
% 2.34/1.01  
% 2.34/1.01  fof(f70,plain,(
% 2.34/1.01    ( ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4) | ~r2_hidden(X4,sK2)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f41])).
% 2.34/1.01  
% 2.34/1.01  fof(f53,plain,(
% 2.34/1.01    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f36])).
% 2.34/1.01  
% 2.34/1.01  fof(f7,axiom,(
% 2.34/1.01    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f17,plain,(
% 2.34/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.34/1.01    inference(ennf_transformation,[],[f7])).
% 2.34/1.01  
% 2.34/1.01  fof(f18,plain,(
% 2.34/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.34/1.01    inference(flattening,[],[f17])).
% 2.34/1.01  
% 2.34/1.01  fof(f51,plain,(
% 2.34/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f18])).
% 2.34/1.01  
% 2.34/1.01  fof(f4,axiom,(
% 2.34/1.01    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f33,plain,(
% 2.34/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.34/1.01    inference(nnf_transformation,[],[f4])).
% 2.34/1.01  
% 2.34/1.01  fof(f34,plain,(
% 2.34/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.34/1.01    inference(flattening,[],[f33])).
% 2.34/1.01  
% 2.34/1.01  fof(f48,plain,(
% 2.34/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.34/1.01    inference(cnf_transformation,[],[f34])).
% 2.34/1.01  
% 2.34/1.01  fof(f72,plain,(
% 2.34/1.01    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.34/1.01    inference(equality_resolution,[],[f48])).
% 2.34/1.01  
% 2.34/1.01  fof(f2,axiom,(
% 2.34/1.01    v1_xboole_0(k1_xboole_0)),
% 2.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f44,plain,(
% 2.34/1.01    v1_xboole_0(k1_xboole_0)),
% 2.34/1.01    inference(cnf_transformation,[],[f2])).
% 2.34/1.01  
% 2.34/1.01  fof(f5,axiom,(
% 2.34/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f16,plain,(
% 2.34/1.01    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.34/1.01    inference(ennf_transformation,[],[f5])).
% 2.34/1.01  
% 2.34/1.01  fof(f49,plain,(
% 2.34/1.01    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.34/1.01    inference(cnf_transformation,[],[f16])).
% 2.34/1.01  
% 2.34/1.01  fof(f42,plain,(
% 2.34/1.01    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f32])).
% 2.34/1.01  
% 2.34/1.01  fof(f3,axiom,(
% 2.34/1.01    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f15,plain,(
% 2.34/1.01    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.34/1.01    inference(ennf_transformation,[],[f3])).
% 2.34/1.01  
% 2.34/1.01  fof(f45,plain,(
% 2.34/1.01    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f15])).
% 2.34/1.01  
% 2.34/1.01  cnf(c_0,plain,
% 2.34/1.01      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.34/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_948,plain,
% 2.34/1.01      ( r2_hidden(sK0(X0),X0) = iProver_top
% 2.34/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_21,plain,
% 2.34/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.34/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.34/1.01      | k1_xboole_0 = X2 ),
% 2.34/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_25,negated_conjecture,
% 2.34/1.01      ( v1_funct_2(sK5,sK2,sK3) ),
% 2.34/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_386,plain,
% 2.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.34/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.34/1.01      | sK5 != X0
% 2.34/1.01      | sK3 != X2
% 2.34/1.01      | sK2 != X1
% 2.34/1.01      | k1_xboole_0 = X2 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_25]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_387,plain,
% 2.34/1.01      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.34/1.01      | k1_relset_1(sK2,sK3,sK5) = sK2
% 2.34/1.01      | k1_xboole_0 = sK3 ),
% 2.34/1.01      inference(unflattening,[status(thm)],[c_386]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_24,negated_conjecture,
% 2.34/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.34/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_389,plain,
% 2.34/1.01      ( k1_relset_1(sK2,sK3,sK5) = sK2 | k1_xboole_0 = sK3 ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_387,c_24]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_936,plain,
% 2.34/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_13,plain,
% 2.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.34/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.34/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_938,plain,
% 2.34/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.34/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1333,plain,
% 2.34/1.01      ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_936,c_938]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1508,plain,
% 2.34/1.01      ( k1_relat_1(sK5) = sK2 | sK3 = k1_xboole_0 ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_389,c_1333]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_28,negated_conjecture,
% 2.34/1.01      ( v1_funct_2(sK4,sK2,sK3) ),
% 2.34/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_397,plain,
% 2.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.34/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.34/1.01      | sK4 != X0
% 2.34/1.01      | sK3 != X2
% 2.34/1.01      | sK2 != X1
% 2.34/1.01      | k1_xboole_0 = X2 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_28]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_398,plain,
% 2.34/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.34/1.01      | k1_relset_1(sK2,sK3,sK4) = sK2
% 2.34/1.01      | k1_xboole_0 = sK3 ),
% 2.34/1.01      inference(unflattening,[status(thm)],[c_397]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_27,negated_conjecture,
% 2.34/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.34/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_400,plain,
% 2.34/1.01      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_398,c_27]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_934,plain,
% 2.34/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1334,plain,
% 2.34/1.01      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_934,c_938]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1583,plain,
% 2.34/1.01      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_400,c_1334]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_11,plain,
% 2.34/1.01      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 2.34/1.01      | ~ v1_relat_1(X1)
% 2.34/1.01      | ~ v1_relat_1(X0)
% 2.34/1.01      | ~ v1_funct_1(X1)
% 2.34/1.01      | ~ v1_funct_1(X0)
% 2.34/1.01      | X1 = X0
% 2.34/1.01      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 2.34/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_940,plain,
% 2.34/1.01      ( X0 = X1
% 2.34/1.01      | k1_relat_1(X0) != k1_relat_1(X1)
% 2.34/1.01      | r2_hidden(sK1(X1,X0),k1_relat_1(X1)) = iProver_top
% 2.34/1.01      | v1_relat_1(X1) != iProver_top
% 2.34/1.01      | v1_relat_1(X0) != iProver_top
% 2.34/1.01      | v1_funct_1(X0) != iProver_top
% 2.34/1.01      | v1_funct_1(X1) != iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2431,plain,
% 2.34/1.01      ( k1_relat_1(X0) != sK2
% 2.34/1.01      | sK5 = X0
% 2.34/1.01      | sK3 = k1_xboole_0
% 2.34/1.01      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 2.34/1.01      | v1_relat_1(X0) != iProver_top
% 2.34/1.01      | v1_relat_1(sK5) != iProver_top
% 2.34/1.01      | v1_funct_1(X0) != iProver_top
% 2.34/1.01      | v1_funct_1(sK5) != iProver_top ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_1508,c_940]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_26,negated_conjecture,
% 2.34/1.01      ( v1_funct_1(sK5) ),
% 2.34/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_33,plain,
% 2.34/1.01      ( v1_funct_1(sK5) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_35,plain,
% 2.34/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_12,plain,
% 2.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.34/1.01      | v1_relat_1(X0) ),
% 2.34/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1147,plain,
% 2.34/1.01      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.34/1.01      | v1_relat_1(sK5) ),
% 2.34/1.01      inference(instantiation,[status(thm)],[c_12]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1148,plain,
% 2.34/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.34/1.01      | v1_relat_1(sK5) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_1147]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3095,plain,
% 2.34/1.01      ( v1_funct_1(X0) != iProver_top
% 2.34/1.01      | k1_relat_1(X0) != sK2
% 2.34/1.01      | sK5 = X0
% 2.34/1.01      | sK3 = k1_xboole_0
% 2.34/1.01      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 2.34/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_2431,c_33,c_35,c_1148]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3096,plain,
% 2.34/1.01      ( k1_relat_1(X0) != sK2
% 2.34/1.01      | sK5 = X0
% 2.34/1.01      | sK3 = k1_xboole_0
% 2.34/1.01      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 2.34/1.01      | v1_relat_1(X0) != iProver_top
% 2.34/1.01      | v1_funct_1(X0) != iProver_top ),
% 2.34/1.01      inference(renaming,[status(thm)],[c_3095]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3108,plain,
% 2.34/1.01      ( sK5 = sK4
% 2.34/1.01      | sK3 = k1_xboole_0
% 2.34/1.01      | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top
% 2.34/1.01      | v1_relat_1(sK4) != iProver_top
% 2.34/1.01      | v1_funct_1(sK4) != iProver_top ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_1583,c_3096]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_29,negated_conjecture,
% 2.34/1.01      ( v1_funct_1(sK4) ),
% 2.34/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_30,plain,
% 2.34/1.01      ( v1_funct_1(sK4) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_32,plain,
% 2.34/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_14,plain,
% 2.34/1.01      ( r2_relset_1(X0,X1,X2,X2)
% 2.34/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.34/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_22,negated_conjecture,
% 2.34/1.01      ( ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
% 2.34/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_303,plain,
% 2.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.34/1.01      | sK5 != X0
% 2.34/1.01      | sK4 != X0
% 2.34/1.01      | sK3 != X2
% 2.34/1.01      | sK2 != X1 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_304,plain,
% 2.34/1.01      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.34/1.01      | sK4 != sK5 ),
% 2.34/1.01      inference(unflattening,[status(thm)],[c_303]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1150,plain,
% 2.34/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.34/1.01      | v1_relat_1(sK4) ),
% 2.34/1.01      inference(instantiation,[status(thm)],[c_12]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1151,plain,
% 2.34/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.34/1.01      | v1_relat_1(sK4) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_1150]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_567,plain,( X0 = X0 ),theory(equality) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1280,plain,
% 2.34/1.01      ( sK4 = sK4 ),
% 2.34/1.01      inference(instantiation,[status(thm)],[c_567]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_568,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1163,plain,
% 2.34/1.01      ( sK5 != X0 | sK4 != X0 | sK4 = sK5 ),
% 2.34/1.01      inference(instantiation,[status(thm)],[c_568]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1573,plain,
% 2.34/1.01      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 2.34/1.01      inference(instantiation,[status(thm)],[c_1163]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3395,plain,
% 2.34/1.01      ( sK3 = k1_xboole_0
% 2.34/1.01      | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_3108,c_30,c_32,c_24,c_304,c_1151,c_1280,c_1573]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3401,plain,
% 2.34/1.01      ( sK3 = k1_xboole_0 | r2_hidden(sK1(sK4,sK5),sK2) = iProver_top ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_1583,c_3395]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_23,negated_conjecture,
% 2.34/1.01      ( ~ r2_hidden(X0,sK2) | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
% 2.34/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_937,plain,
% 2.34/1.01      ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
% 2.34/1.01      | r2_hidden(X0,sK2) != iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3417,plain,
% 2.34/1.01      ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
% 2.34/1.01      | sK3 = k1_xboole_0 ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_3401,c_937]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_10,plain,
% 2.34/1.01      ( ~ v1_relat_1(X0)
% 2.34/1.01      | ~ v1_relat_1(X1)
% 2.34/1.01      | ~ v1_funct_1(X0)
% 2.34/1.01      | ~ v1_funct_1(X1)
% 2.34/1.01      | X0 = X1
% 2.34/1.01      | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 2.34/1.01      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 2.34/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_941,plain,
% 2.34/1.01      ( X0 = X1
% 2.34/1.01      | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 2.34/1.01      | k1_relat_1(X0) != k1_relat_1(X1)
% 2.34/1.01      | v1_relat_1(X0) != iProver_top
% 2.34/1.01      | v1_relat_1(X1) != iProver_top
% 2.34/1.01      | v1_funct_1(X1) != iProver_top
% 2.34/1.01      | v1_funct_1(X0) != iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3563,plain,
% 2.34/1.01      ( k1_relat_1(sK4) != k1_relat_1(sK5)
% 2.34/1.01      | sK5 = sK4
% 2.34/1.01      | sK3 = k1_xboole_0
% 2.34/1.01      | v1_relat_1(sK5) != iProver_top
% 2.34/1.01      | v1_relat_1(sK4) != iProver_top
% 2.34/1.01      | v1_funct_1(sK5) != iProver_top
% 2.34/1.01      | v1_funct_1(sK4) != iProver_top ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_3417,c_941]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3564,plain,
% 2.34/1.01      ( ~ v1_relat_1(sK5)
% 2.34/1.01      | ~ v1_relat_1(sK4)
% 2.34/1.01      | ~ v1_funct_1(sK5)
% 2.34/1.01      | ~ v1_funct_1(sK4)
% 2.34/1.01      | k1_relat_1(sK4) != k1_relat_1(sK5)
% 2.34/1.01      | sK5 = sK4
% 2.34/1.01      | sK3 = k1_xboole_0 ),
% 2.34/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_3563]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3566,plain,
% 2.34/1.01      ( k1_relat_1(sK4) != k1_relat_1(sK5) | sK3 = k1_xboole_0 ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_3563,c_29,c_27,c_26,c_24,c_304,c_1147,c_1150,c_1280,
% 2.34/1.01                 c_1573,c_3564]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3570,plain,
% 2.34/1.01      ( k1_relat_1(sK4) != sK2 | sK3 = k1_xboole_0 ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_1508,c_3566]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3650,plain,
% 2.34/1.01      ( sK3 = k1_xboole_0 ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_3570,c_1583]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_9,plain,
% 2.34/1.01      ( m1_subset_1(X0,X1)
% 2.34/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.34/1.01      | ~ r2_hidden(X0,X2) ),
% 2.34/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_942,plain,
% 2.34/1.01      ( m1_subset_1(X0,X1) = iProver_top
% 2.34/1.01      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.34/1.01      | r2_hidden(X0,X2) != iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2645,plain,
% 2.34/1.01      ( m1_subset_1(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
% 2.34/1.01      | r2_hidden(X0,sK4) != iProver_top ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_934,c_942]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3659,plain,
% 2.34/1.01      ( m1_subset_1(X0,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top
% 2.34/1.01      | r2_hidden(X0,sK4) != iProver_top ),
% 2.34/1.01      inference(demodulation,[status(thm)],[c_3650,c_2645]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_4,plain,
% 2.34/1.01      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.34/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3714,plain,
% 2.34/1.01      ( m1_subset_1(X0,k1_xboole_0) = iProver_top
% 2.34/1.01      | r2_hidden(X0,sK4) != iProver_top ),
% 2.34/1.01      inference(demodulation,[status(thm)],[c_3659,c_4]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2,plain,
% 2.34/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 2.34/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_88,plain,
% 2.34/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_7,plain,
% 2.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.34/1.01      | ~ r2_hidden(X2,X0)
% 2.34/1.01      | r2_hidden(X2,X1) ),
% 2.34/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_944,plain,
% 2.34/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.34/1.01      | r2_hidden(X2,X0) != iProver_top
% 2.34/1.01      | r2_hidden(X2,X1) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2712,plain,
% 2.34/1.01      ( r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
% 2.34/1.01      | r2_hidden(X0,sK4) != iProver_top ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_934,c_944]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1,plain,
% 2.34/1.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.34/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_947,plain,
% 2.34/1.01      ( r2_hidden(X0,X1) != iProver_top
% 2.34/1.01      | v1_xboole_0(X1) != iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2882,plain,
% 2.34/1.01      ( r2_hidden(X0,sK4) != iProver_top
% 2.34/1.01      | v1_xboole_0(k2_zfmisc_1(sK2,sK3)) != iProver_top ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_2712,c_947]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3655,plain,
% 2.34/1.01      ( r2_hidden(X0,sK4) != iProver_top
% 2.34/1.01      | v1_xboole_0(k2_zfmisc_1(sK2,k1_xboole_0)) != iProver_top ),
% 2.34/1.01      inference(demodulation,[status(thm)],[c_3650,c_2882]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3734,plain,
% 2.34/1.01      ( r2_hidden(X0,sK4) != iProver_top
% 2.34/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.34/1.01      inference(demodulation,[status(thm)],[c_3655,c_4]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3869,plain,
% 2.34/1.01      ( r2_hidden(X0,sK4) != iProver_top ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_3714,c_88,c_3734]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3876,plain,
% 2.34/1.01      ( v1_xboole_0(sK4) = iProver_top ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_948,c_3869]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2644,plain,
% 2.34/1.01      ( m1_subset_1(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
% 2.34/1.01      | r2_hidden(X0,sK5) != iProver_top ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_936,c_942]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3660,plain,
% 2.34/1.01      ( m1_subset_1(X0,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top
% 2.34/1.01      | r2_hidden(X0,sK5) != iProver_top ),
% 2.34/1.01      inference(demodulation,[status(thm)],[c_3650,c_2644]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3709,plain,
% 2.34/1.01      ( m1_subset_1(X0,k1_xboole_0) = iProver_top
% 2.34/1.01      | r2_hidden(X0,sK5) != iProver_top ),
% 2.34/1.01      inference(demodulation,[status(thm)],[c_3660,c_4]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2711,plain,
% 2.34/1.01      ( r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
% 2.34/1.01      | r2_hidden(X0,sK5) != iProver_top ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_936,c_944]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2789,plain,
% 2.34/1.01      ( r2_hidden(X0,sK5) != iProver_top
% 2.34/1.01      | v1_xboole_0(k2_zfmisc_1(sK2,sK3)) != iProver_top ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_2711,c_947]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3656,plain,
% 2.34/1.01      ( r2_hidden(X0,sK5) != iProver_top
% 2.34/1.01      | v1_xboole_0(k2_zfmisc_1(sK2,k1_xboole_0)) != iProver_top ),
% 2.34/1.01      inference(demodulation,[status(thm)],[c_3650,c_2789]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3729,plain,
% 2.34/1.01      ( r2_hidden(X0,sK5) != iProver_top
% 2.34/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.34/1.01      inference(demodulation,[status(thm)],[c_3656,c_4]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3859,plain,
% 2.34/1.01      ( r2_hidden(X0,sK5) != iProver_top ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_3709,c_88,c_3729]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3866,plain,
% 2.34/1.01      ( v1_xboole_0(sK5) = iProver_top ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_948,c_3859]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3,plain,
% 2.34/1.01      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 2.34/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1126,plain,
% 2.34/1.01      ( ~ v1_xboole_0(sK5) | ~ v1_xboole_0(sK4) | sK4 = sK5 ),
% 2.34/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1127,plain,
% 2.34/1.01      ( sK4 = sK5
% 2.34/1.01      | v1_xboole_0(sK5) != iProver_top
% 2.34/1.01      | v1_xboole_0(sK4) != iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_1126]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(contradiction,plain,
% 2.34/1.01      ( $false ),
% 2.34/1.01      inference(minisat,[status(thm)],[c_3876,c_3866,c_1127,c_304,c_24]) ).
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.34/1.01  
% 2.34/1.01  ------                               Statistics
% 2.34/1.01  
% 2.34/1.01  ------ General
% 2.34/1.01  
% 2.34/1.01  abstr_ref_over_cycles:                  0
% 2.34/1.01  abstr_ref_under_cycles:                 0
% 2.34/1.01  gc_basic_clause_elim:                   0
% 2.34/1.01  forced_gc_time:                         0
% 2.34/1.01  parsing_time:                           0.013
% 2.34/1.01  unif_index_cands_time:                  0.
% 2.34/1.01  unif_index_add_time:                    0.
% 2.34/1.01  orderings_time:                         0.
% 2.34/1.01  out_proof_time:                         0.01
% 2.34/1.01  total_time:                             0.142
% 2.34/1.01  num_of_symbols:                         50
% 2.34/1.01  num_of_terms:                           3003
% 2.34/1.01  
% 2.34/1.01  ------ Preprocessing
% 2.34/1.01  
% 2.34/1.01  num_of_splits:                          0
% 2.34/1.01  num_of_split_atoms:                     0
% 2.34/1.01  num_of_reused_defs:                     0
% 2.34/1.01  num_eq_ax_congr_red:                    17
% 2.34/1.01  num_of_sem_filtered_clauses:            1
% 2.34/1.01  num_of_subtypes:                        0
% 2.34/1.01  monotx_restored_types:                  0
% 2.34/1.01  sat_num_of_epr_types:                   0
% 2.34/1.01  sat_num_of_non_cyclic_types:            0
% 2.34/1.01  sat_guarded_non_collapsed_types:        0
% 2.34/1.01  num_pure_diseq_elim:                    0
% 2.34/1.01  simp_replaced_by:                       0
% 2.34/1.01  res_preprocessed:                       129
% 2.34/1.01  prep_upred:                             0
% 2.34/1.01  prep_unflattend:                        41
% 2.34/1.01  smt_new_axioms:                         0
% 2.34/1.01  pred_elim_cands:                        5
% 2.34/1.01  pred_elim:                              2
% 2.34/1.01  pred_elim_cl:                           4
% 2.34/1.01  pred_elim_cycles:                       4
% 2.34/1.01  merged_defs:                            0
% 2.34/1.01  merged_defs_ncl:                        0
% 2.34/1.01  bin_hyper_res:                          0
% 2.34/1.01  prep_cycles:                            4
% 2.34/1.01  pred_elim_time:                         0.004
% 2.34/1.01  splitting_time:                         0.
% 2.34/1.01  sem_filter_time:                        0.
% 2.34/1.01  monotx_time:                            0.001
% 2.34/1.01  subtype_inf_time:                       0.
% 2.34/1.01  
% 2.34/1.01  ------ Problem properties
% 2.34/1.01  
% 2.34/1.01  clauses:                                26
% 2.34/1.01  conjectures:                            5
% 2.34/1.01  epr:                                    6
% 2.34/1.01  horn:                                   19
% 2.34/1.01  ground:                                 12
% 2.34/1.01  unary:                                  9
% 2.34/1.01  binary:                                 7
% 2.34/1.01  lits:                                   63
% 2.34/1.01  lits_eq:                                28
% 2.34/1.01  fd_pure:                                0
% 2.34/1.01  fd_pseudo:                              0
% 2.34/1.01  fd_cond:                                1
% 2.34/1.01  fd_pseudo_cond:                         3
% 2.34/1.01  ac_symbols:                             0
% 2.34/1.01  
% 2.34/1.01  ------ Propositional Solver
% 2.34/1.01  
% 2.34/1.01  prop_solver_calls:                      27
% 2.34/1.01  prop_fast_solver_calls:                 834
% 2.34/1.01  smt_solver_calls:                       0
% 2.34/1.01  smt_fast_solver_calls:                  0
% 2.34/1.01  prop_num_of_clauses:                    1288
% 2.34/1.01  prop_preprocess_simplified:             4258
% 2.34/1.01  prop_fo_subsumed:                       23
% 2.34/1.01  prop_solver_time:                       0.
% 2.34/1.01  smt_solver_time:                        0.
% 2.34/1.01  smt_fast_solver_time:                   0.
% 2.34/1.01  prop_fast_solver_time:                  0.
% 2.34/1.01  prop_unsat_core_time:                   0.
% 2.34/1.01  
% 2.34/1.01  ------ QBF
% 2.34/1.01  
% 2.34/1.01  qbf_q_res:                              0
% 2.34/1.01  qbf_num_tautologies:                    0
% 2.34/1.01  qbf_prep_cycles:                        0
% 2.34/1.01  
% 2.34/1.01  ------ BMC1
% 2.34/1.01  
% 2.34/1.01  bmc1_current_bound:                     -1
% 2.34/1.01  bmc1_last_solved_bound:                 -1
% 2.34/1.01  bmc1_unsat_core_size:                   -1
% 2.34/1.01  bmc1_unsat_core_parents_size:           -1
% 2.34/1.01  bmc1_merge_next_fun:                    0
% 2.34/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.34/1.01  
% 2.34/1.01  ------ Instantiation
% 2.34/1.01  
% 2.34/1.01  inst_num_of_clauses:                    430
% 2.34/1.01  inst_num_in_passive:                    73
% 2.34/1.01  inst_num_in_active:                     235
% 2.34/1.01  inst_num_in_unprocessed:                122
% 2.34/1.01  inst_num_of_loops:                      300
% 2.34/1.01  inst_num_of_learning_restarts:          0
% 2.34/1.01  inst_num_moves_active_passive:          62
% 2.34/1.01  inst_lit_activity:                      0
% 2.34/1.01  inst_lit_activity_moves:                0
% 2.34/1.01  inst_num_tautologies:                   0
% 2.34/1.01  inst_num_prop_implied:                  0
% 2.34/1.01  inst_num_existing_simplified:           0
% 2.34/1.01  inst_num_eq_res_simplified:             0
% 2.34/1.01  inst_num_child_elim:                    0
% 2.34/1.01  inst_num_of_dismatching_blockings:      182
% 2.34/1.01  inst_num_of_non_proper_insts:           594
% 2.34/1.01  inst_num_of_duplicates:                 0
% 2.34/1.01  inst_inst_num_from_inst_to_res:         0
% 2.34/1.01  inst_dismatching_checking_time:         0.
% 2.34/1.01  
% 2.34/1.01  ------ Resolution
% 2.34/1.01  
% 2.34/1.01  res_num_of_clauses:                     0
% 2.34/1.01  res_num_in_passive:                     0
% 2.34/1.01  res_num_in_active:                      0
% 2.34/1.01  res_num_of_loops:                       133
% 2.34/1.01  res_forward_subset_subsumed:            38
% 2.34/1.01  res_backward_subset_subsumed:           0
% 2.34/1.01  res_forward_subsumed:                   0
% 2.34/1.01  res_backward_subsumed:                  0
% 2.34/1.01  res_forward_subsumption_resolution:     0
% 2.34/1.01  res_backward_subsumption_resolution:    0
% 2.34/1.01  res_clause_to_clause_subsumption:       101
% 2.34/1.01  res_orphan_elimination:                 0
% 2.34/1.01  res_tautology_del:                      30
% 2.34/1.01  res_num_eq_res_simplified:              0
% 2.34/1.01  res_num_sel_changes:                    0
% 2.34/1.01  res_moves_from_active_to_pass:          0
% 2.34/1.01  
% 2.34/1.01  ------ Superposition
% 2.34/1.01  
% 2.34/1.01  sup_time_total:                         0.
% 2.34/1.01  sup_time_generating:                    0.
% 2.34/1.01  sup_time_sim_full:                      0.
% 2.34/1.01  sup_time_sim_immed:                     0.
% 2.34/1.01  
% 2.34/1.01  sup_num_of_clauses:                     56
% 2.34/1.01  sup_num_in_active:                      40
% 2.34/1.01  sup_num_in_passive:                     16
% 2.34/1.01  sup_num_of_loops:                       59
% 2.34/1.01  sup_fw_superposition:                   38
% 2.34/1.01  sup_bw_superposition:                   23
% 2.34/1.01  sup_immediate_simplified:               16
% 2.34/1.01  sup_given_eliminated:                   0
% 2.34/1.01  comparisons_done:                       0
% 2.34/1.01  comparisons_avoided:                    13
% 2.34/1.01  
% 2.34/1.01  ------ Simplifications
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  sim_fw_subset_subsumed:                 2
% 2.34/1.01  sim_bw_subset_subsumed:                 8
% 2.34/1.01  sim_fw_subsumed:                        2
% 2.34/1.01  sim_bw_subsumed:                        0
% 2.34/1.01  sim_fw_subsumption_res:                 4
% 2.34/1.01  sim_bw_subsumption_res:                 0
% 2.34/1.01  sim_tautology_del:                      1
% 2.34/1.01  sim_eq_tautology_del:                   9
% 2.34/1.01  sim_eq_res_simp:                        2
% 2.34/1.01  sim_fw_demodulated:                     12
% 2.34/1.01  sim_bw_demodulated:                     18
% 2.34/1.01  sim_light_normalised:                   0
% 2.34/1.01  sim_joinable_taut:                      0
% 2.34/1.01  sim_joinable_simp:                      0
% 2.34/1.01  sim_ac_normalised:                      0
% 2.34/1.01  sim_smt_subsumption:                    0
% 2.34/1.01  
%------------------------------------------------------------------------------
