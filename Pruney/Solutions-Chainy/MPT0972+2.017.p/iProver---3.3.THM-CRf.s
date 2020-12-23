%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:11 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :  150 (1471 expanded)
%              Number of clauses        :   86 ( 443 expanded)
%              Number of leaves         :   19 ( 370 expanded)
%              Depth                    :   29
%              Number of atoms          :  518 (9481 expanded)
%              Number of equality atoms :  236 (2239 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f34])).

fof(f50,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f24,plain,(
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
    inference(flattening,[],[f24])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f26,plain,(
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
    inference(flattening,[],[f26])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK6)
        & ! [X4] :
            ( k1_funct_1(sK6,X4) = k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK6,X0,X1)
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
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
          ( ~ r2_relset_1(sK3,sK4,sK5,X3)
          & ! [X4] :
              ( k1_funct_1(sK5,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,sK3) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
          & v1_funct_2(X3,sK3,sK4)
          & v1_funct_1(X3) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK5,sK3,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK6)
    & ! [X4] :
        ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
        | ~ r2_hidden(X4,sK3) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f27,f41,f40])).

fof(f70,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f67,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f68,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

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

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
            & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f36])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f69,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f66,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f59])).

fof(f73,plain,(
    ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f72,plain,(
    ! [X4] :
      ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
      | ~ r2_hidden(X4,sK3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1924,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0))
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1918,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1913,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2636,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top
    | v1_xboole_0(sK1(k2_zfmisc_1(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1918,c_1913])).

cnf(c_7,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(sK1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1919,plain,
    ( v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4514,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2636,c_1919])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_417,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK6 != X0
    | sK4 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_418,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_420,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_418,c_25])).

cnf(c_1910,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1912,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2619,plain,
    ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1910,c_1912])).

cnf(c_2886,plain,
    ( k1_relat_1(sK6) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_420,c_2619])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_428,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_29])).

cnf(c_429,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_431,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_429,c_28])).

cnf(c_1908,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2620,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1908,c_1912])).

cnf(c_2889,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_431,c_2620])).

cnf(c_11,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | X1 = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1915,plain,
    ( X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1)
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3363,plain,
    ( k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2886,c_1915])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_34,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_36,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2109,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2110,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2109])).

cnf(c_3557,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3363,c_34,c_36,c_2110])).

cnf(c_3558,plain,
    ( k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3557])).

cnf(c_3570,plain,
    ( sK6 = sK5
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2889,c_3558])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_31,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_33,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_15,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_23,negated_conjecture,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_334,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK6 != X0
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_23])).

cnf(c_335,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | sK5 != sK6 ),
    inference(unflattening,[status(thm)],[c_334])).

cnf(c_2112,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2113,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2112])).

cnf(c_1495,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2235,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1495])).

cnf(c_1496,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2138,plain,
    ( sK6 != X0
    | sK5 != X0
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_1496])).

cnf(c_2803,plain,
    ( sK6 != sK5
    | sK5 = sK6
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2138])).

cnf(c_3637,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3570,c_31,c_33,c_25,c_335,c_2113,c_2235,c_2803])).

cnf(c_3643,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,sK6),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2889,c_3637])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1911,plain,
    ( k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3663,plain,
    ( k1_funct_1(sK5,sK2(sK5,sK6)) = k1_funct_1(sK6,sK2(sK5,sK6))
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3643,c_1911])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X0 = X1
    | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1916,plain,
    ( X0 = X1
    | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3716,plain,
    ( k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK6 = sK5
    | sK4 = k1_xboole_0
    | v1_relat_1(sK6) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3663,c_1916])).

cnf(c_3717,plain,
    ( ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5)
    | k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK6 = sK5
    | sK4 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3716])).

cnf(c_3719,plain,
    ( k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3716,c_30,c_28,c_27,c_25,c_335,c_2109,c_2112,c_2235,c_2803,c_3717])).

cnf(c_3723,plain,
    ( k1_relat_1(sK5) != sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2886,c_3719])).

cnf(c_3751,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3723,c_2889])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1917,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2841,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1908,c_1917])).

cnf(c_3756,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3751,c_2841])).

cnf(c_4519,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4514,c_3756])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_94,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5228,plain,
    ( r2_hidden(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4519,c_94])).

cnf(c_5235,plain,
    ( r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1924,c_5228])).

cnf(c_2840,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1910,c_1917])).

cnf(c_3757,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3751,c_2840])).

cnf(c_4518,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4514,c_3757])).

cnf(c_4827,plain,
    ( r2_hidden(X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4518,c_94])).

cnf(c_4834,plain,
    ( r1_tarski(sK6,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1924,c_4827])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1921,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4848,plain,
    ( sK6 = X0
    | r1_tarski(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4834,c_1921])).

cnf(c_5412,plain,
    ( sK6 = sK5 ),
    inference(superposition,[status(thm)],[c_5235,c_4848])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5412,c_2803,c_2235,c_335,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:09:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 1.95/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.01  
% 1.95/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.95/1.01  
% 1.95/1.01  ------  iProver source info
% 1.95/1.01  
% 1.95/1.01  git: date: 2020-06-30 10:37:57 +0100
% 1.95/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.95/1.01  git: non_committed_changes: false
% 1.95/1.01  git: last_make_outside_of_git: false
% 1.95/1.01  
% 1.95/1.01  ------ 
% 1.95/1.01  
% 1.95/1.01  ------ Input Options
% 1.95/1.01  
% 1.95/1.01  --out_options                           all
% 1.95/1.01  --tptp_safe_out                         true
% 1.95/1.01  --problem_path                          ""
% 1.95/1.01  --include_path                          ""
% 1.95/1.01  --clausifier                            res/vclausify_rel
% 1.95/1.01  --clausifier_options                    --mode clausify
% 1.95/1.01  --stdin                                 false
% 1.95/1.01  --stats_out                             all
% 1.95/1.01  
% 1.95/1.01  ------ General Options
% 1.95/1.01  
% 1.95/1.01  --fof                                   false
% 1.95/1.01  --time_out_real                         305.
% 1.95/1.01  --time_out_virtual                      -1.
% 1.95/1.01  --symbol_type_check                     false
% 1.95/1.01  --clausify_out                          false
% 1.95/1.01  --sig_cnt_out                           false
% 1.95/1.01  --trig_cnt_out                          false
% 1.95/1.01  --trig_cnt_out_tolerance                1.
% 1.95/1.01  --trig_cnt_out_sk_spl                   false
% 1.95/1.01  --abstr_cl_out                          false
% 1.95/1.01  
% 1.95/1.01  ------ Global Options
% 1.95/1.01  
% 1.95/1.01  --schedule                              default
% 1.95/1.01  --add_important_lit                     false
% 1.95/1.01  --prop_solver_per_cl                    1000
% 1.95/1.01  --min_unsat_core                        false
% 1.95/1.01  --soft_assumptions                      false
% 1.95/1.01  --soft_lemma_size                       3
% 1.95/1.01  --prop_impl_unit_size                   0
% 1.95/1.01  --prop_impl_unit                        []
% 1.95/1.01  --share_sel_clauses                     true
% 1.95/1.01  --reset_solvers                         false
% 1.95/1.01  --bc_imp_inh                            [conj_cone]
% 1.95/1.01  --conj_cone_tolerance                   3.
% 1.95/1.01  --extra_neg_conj                        none
% 1.95/1.01  --large_theory_mode                     true
% 1.95/1.01  --prolific_symb_bound                   200
% 1.95/1.01  --lt_threshold                          2000
% 1.95/1.01  --clause_weak_htbl                      true
% 1.95/1.01  --gc_record_bc_elim                     false
% 1.95/1.01  
% 1.95/1.01  ------ Preprocessing Options
% 1.95/1.01  
% 1.95/1.01  --preprocessing_flag                    true
% 1.95/1.01  --time_out_prep_mult                    0.1
% 1.95/1.01  --splitting_mode                        input
% 1.95/1.01  --splitting_grd                         true
% 1.95/1.01  --splitting_cvd                         false
% 1.95/1.01  --splitting_cvd_svl                     false
% 1.95/1.01  --splitting_nvd                         32
% 1.95/1.01  --sub_typing                            true
% 1.95/1.01  --prep_gs_sim                           true
% 1.95/1.01  --prep_unflatten                        true
% 1.95/1.01  --prep_res_sim                          true
% 1.95/1.01  --prep_upred                            true
% 1.95/1.01  --prep_sem_filter                       exhaustive
% 1.95/1.01  --prep_sem_filter_out                   false
% 1.95/1.01  --pred_elim                             true
% 1.95/1.01  --res_sim_input                         true
% 1.95/1.01  --eq_ax_congr_red                       true
% 1.95/1.01  --pure_diseq_elim                       true
% 1.95/1.01  --brand_transform                       false
% 1.95/1.01  --non_eq_to_eq                          false
% 1.95/1.01  --prep_def_merge                        true
% 1.95/1.01  --prep_def_merge_prop_impl              false
% 1.95/1.01  --prep_def_merge_mbd                    true
% 1.95/1.01  --prep_def_merge_tr_red                 false
% 1.95/1.01  --prep_def_merge_tr_cl                  false
% 1.95/1.01  --smt_preprocessing                     true
% 1.95/1.01  --smt_ac_axioms                         fast
% 1.95/1.01  --preprocessed_out                      false
% 1.95/1.01  --preprocessed_stats                    false
% 1.95/1.01  
% 1.95/1.01  ------ Abstraction refinement Options
% 1.95/1.01  
% 1.95/1.01  --abstr_ref                             []
% 1.95/1.01  --abstr_ref_prep                        false
% 1.95/1.01  --abstr_ref_until_sat                   false
% 1.95/1.01  --abstr_ref_sig_restrict                funpre
% 1.95/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.95/1.01  --abstr_ref_under                       []
% 1.95/1.01  
% 1.95/1.01  ------ SAT Options
% 1.95/1.01  
% 1.95/1.01  --sat_mode                              false
% 1.95/1.01  --sat_fm_restart_options                ""
% 1.95/1.01  --sat_gr_def                            false
% 1.95/1.01  --sat_epr_types                         true
% 1.95/1.01  --sat_non_cyclic_types                  false
% 1.95/1.01  --sat_finite_models                     false
% 1.95/1.01  --sat_fm_lemmas                         false
% 1.95/1.01  --sat_fm_prep                           false
% 1.95/1.01  --sat_fm_uc_incr                        true
% 1.95/1.01  --sat_out_model                         small
% 1.95/1.01  --sat_out_clauses                       false
% 1.95/1.01  
% 1.95/1.01  ------ QBF Options
% 1.95/1.01  
% 1.95/1.01  --qbf_mode                              false
% 1.95/1.01  --qbf_elim_univ                         false
% 1.95/1.01  --qbf_dom_inst                          none
% 1.95/1.01  --qbf_dom_pre_inst                      false
% 1.95/1.01  --qbf_sk_in                             false
% 1.95/1.01  --qbf_pred_elim                         true
% 1.95/1.01  --qbf_split                             512
% 1.95/1.01  
% 1.95/1.01  ------ BMC1 Options
% 1.95/1.01  
% 1.95/1.01  --bmc1_incremental                      false
% 1.95/1.01  --bmc1_axioms                           reachable_all
% 1.95/1.01  --bmc1_min_bound                        0
% 1.95/1.01  --bmc1_max_bound                        -1
% 1.95/1.01  --bmc1_max_bound_default                -1
% 1.95/1.01  --bmc1_symbol_reachability              true
% 1.95/1.01  --bmc1_property_lemmas                  false
% 1.95/1.01  --bmc1_k_induction                      false
% 1.95/1.01  --bmc1_non_equiv_states                 false
% 1.95/1.01  --bmc1_deadlock                         false
% 1.95/1.01  --bmc1_ucm                              false
% 1.95/1.01  --bmc1_add_unsat_core                   none
% 1.95/1.01  --bmc1_unsat_core_children              false
% 1.95/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.95/1.01  --bmc1_out_stat                         full
% 1.95/1.01  --bmc1_ground_init                      false
% 1.95/1.01  --bmc1_pre_inst_next_state              false
% 1.95/1.01  --bmc1_pre_inst_state                   false
% 1.95/1.01  --bmc1_pre_inst_reach_state             false
% 1.95/1.01  --bmc1_out_unsat_core                   false
% 1.95/1.01  --bmc1_aig_witness_out                  false
% 1.95/1.01  --bmc1_verbose                          false
% 1.95/1.01  --bmc1_dump_clauses_tptp                false
% 1.95/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.95/1.01  --bmc1_dump_file                        -
% 1.95/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.95/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.95/1.01  --bmc1_ucm_extend_mode                  1
% 1.95/1.01  --bmc1_ucm_init_mode                    2
% 1.95/1.01  --bmc1_ucm_cone_mode                    none
% 1.95/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.95/1.01  --bmc1_ucm_relax_model                  4
% 1.95/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.95/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.95/1.01  --bmc1_ucm_layered_model                none
% 1.95/1.01  --bmc1_ucm_max_lemma_size               10
% 1.95/1.01  
% 1.95/1.01  ------ AIG Options
% 1.95/1.01  
% 1.95/1.01  --aig_mode                              false
% 1.95/1.01  
% 1.95/1.01  ------ Instantiation Options
% 1.95/1.01  
% 1.95/1.01  --instantiation_flag                    true
% 1.95/1.01  --inst_sos_flag                         false
% 1.95/1.01  --inst_sos_phase                        true
% 1.95/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.95/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.95/1.01  --inst_lit_sel_side                     num_symb
% 1.95/1.01  --inst_solver_per_active                1400
% 1.95/1.01  --inst_solver_calls_frac                1.
% 1.95/1.01  --inst_passive_queue_type               priority_queues
% 1.95/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.95/1.01  --inst_passive_queues_freq              [25;2]
% 1.95/1.01  --inst_dismatching                      true
% 1.95/1.01  --inst_eager_unprocessed_to_passive     true
% 1.95/1.01  --inst_prop_sim_given                   true
% 1.95/1.01  --inst_prop_sim_new                     false
% 1.95/1.01  --inst_subs_new                         false
% 1.95/1.01  --inst_eq_res_simp                      false
% 1.95/1.01  --inst_subs_given                       false
% 1.95/1.01  --inst_orphan_elimination               true
% 1.95/1.01  --inst_learning_loop_flag               true
% 1.95/1.01  --inst_learning_start                   3000
% 1.95/1.01  --inst_learning_factor                  2
% 1.95/1.01  --inst_start_prop_sim_after_learn       3
% 1.95/1.01  --inst_sel_renew                        solver
% 1.95/1.01  --inst_lit_activity_flag                true
% 1.95/1.01  --inst_restr_to_given                   false
% 1.95/1.01  --inst_activity_threshold               500
% 1.95/1.01  --inst_out_proof                        true
% 1.95/1.01  
% 1.95/1.01  ------ Resolution Options
% 1.95/1.01  
% 1.95/1.01  --resolution_flag                       true
% 1.95/1.01  --res_lit_sel                           adaptive
% 1.95/1.01  --res_lit_sel_side                      none
% 1.95/1.01  --res_ordering                          kbo
% 1.95/1.01  --res_to_prop_solver                    active
% 1.95/1.01  --res_prop_simpl_new                    false
% 1.95/1.01  --res_prop_simpl_given                  true
% 1.95/1.01  --res_passive_queue_type                priority_queues
% 1.95/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.95/1.01  --res_passive_queues_freq               [15;5]
% 1.95/1.01  --res_forward_subs                      full
% 1.95/1.01  --res_backward_subs                     full
% 1.95/1.01  --res_forward_subs_resolution           true
% 1.95/1.01  --res_backward_subs_resolution          true
% 1.95/1.01  --res_orphan_elimination                true
% 1.95/1.01  --res_time_limit                        2.
% 1.95/1.01  --res_out_proof                         true
% 1.95/1.01  
% 1.95/1.01  ------ Superposition Options
% 1.95/1.01  
% 1.95/1.01  --superposition_flag                    true
% 1.95/1.01  --sup_passive_queue_type                priority_queues
% 1.95/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.95/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.95/1.01  --demod_completeness_check              fast
% 1.95/1.01  --demod_use_ground                      true
% 1.95/1.01  --sup_to_prop_solver                    passive
% 1.95/1.01  --sup_prop_simpl_new                    true
% 1.95/1.01  --sup_prop_simpl_given                  true
% 1.95/1.01  --sup_fun_splitting                     false
% 1.95/1.01  --sup_smt_interval                      50000
% 1.95/1.01  
% 1.95/1.01  ------ Superposition Simplification Setup
% 1.95/1.01  
% 1.95/1.01  --sup_indices_passive                   []
% 1.95/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.95/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/1.01  --sup_full_bw                           [BwDemod]
% 1.95/1.01  --sup_immed_triv                        [TrivRules]
% 1.95/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.95/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/1.01  --sup_immed_bw_main                     []
% 1.95/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.95/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.95/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.95/1.01  
% 1.95/1.01  ------ Combination Options
% 1.95/1.01  
% 1.95/1.01  --comb_res_mult                         3
% 1.95/1.01  --comb_sup_mult                         2
% 1.95/1.01  --comb_inst_mult                        10
% 1.95/1.01  
% 1.95/1.01  ------ Debug Options
% 1.95/1.01  
% 1.95/1.01  --dbg_backtrace                         false
% 1.95/1.01  --dbg_dump_prop_clauses                 false
% 1.95/1.01  --dbg_dump_prop_clauses_file            -
% 1.95/1.01  --dbg_out_stat                          false
% 1.95/1.01  ------ Parsing...
% 1.95/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.95/1.01  
% 1.95/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.95/1.01  
% 1.95/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.95/1.01  
% 1.95/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.95/1.01  ------ Proving...
% 1.95/1.01  ------ Problem Properties 
% 1.95/1.01  
% 1.95/1.01  
% 1.95/1.01  clauses                                 26
% 1.95/1.01  conjectures                             5
% 1.95/1.01  EPR                                     7
% 1.95/1.01  Horn                                    19
% 1.95/1.01  unary                                   7
% 1.95/1.01  binary                                  9
% 1.95/1.01  lits                                    65
% 1.95/1.01  lits eq                                 23
% 1.95/1.01  fd_pure                                 0
% 1.95/1.01  fd_pseudo                               0
% 1.95/1.01  fd_cond                                 0
% 1.95/1.01  fd_pseudo_cond                          3
% 1.95/1.01  AC symbols                              0
% 1.95/1.01  
% 1.95/1.01  ------ Schedule dynamic 5 is on 
% 1.95/1.01  
% 1.95/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.95/1.01  
% 1.95/1.01  
% 1.95/1.01  ------ 
% 1.95/1.01  Current options:
% 1.95/1.01  ------ 
% 1.95/1.01  
% 1.95/1.01  ------ Input Options
% 1.95/1.01  
% 1.95/1.01  --out_options                           all
% 1.95/1.01  --tptp_safe_out                         true
% 1.95/1.01  --problem_path                          ""
% 1.95/1.01  --include_path                          ""
% 1.95/1.01  --clausifier                            res/vclausify_rel
% 1.95/1.01  --clausifier_options                    --mode clausify
% 1.95/1.01  --stdin                                 false
% 1.95/1.01  --stats_out                             all
% 1.95/1.01  
% 1.95/1.01  ------ General Options
% 1.95/1.01  
% 1.95/1.01  --fof                                   false
% 1.95/1.01  --time_out_real                         305.
% 1.95/1.01  --time_out_virtual                      -1.
% 1.95/1.01  --symbol_type_check                     false
% 1.95/1.01  --clausify_out                          false
% 1.95/1.01  --sig_cnt_out                           false
% 1.95/1.01  --trig_cnt_out                          false
% 1.95/1.01  --trig_cnt_out_tolerance                1.
% 1.95/1.01  --trig_cnt_out_sk_spl                   false
% 1.95/1.01  --abstr_cl_out                          false
% 1.95/1.01  
% 1.95/1.01  ------ Global Options
% 1.95/1.01  
% 1.95/1.01  --schedule                              default
% 1.95/1.01  --add_important_lit                     false
% 1.95/1.01  --prop_solver_per_cl                    1000
% 1.95/1.01  --min_unsat_core                        false
% 1.95/1.01  --soft_assumptions                      false
% 1.95/1.01  --soft_lemma_size                       3
% 1.95/1.01  --prop_impl_unit_size                   0
% 1.95/1.01  --prop_impl_unit                        []
% 1.95/1.01  --share_sel_clauses                     true
% 1.95/1.01  --reset_solvers                         false
% 1.95/1.01  --bc_imp_inh                            [conj_cone]
% 1.95/1.01  --conj_cone_tolerance                   3.
% 1.95/1.01  --extra_neg_conj                        none
% 1.95/1.01  --large_theory_mode                     true
% 1.95/1.01  --prolific_symb_bound                   200
% 1.95/1.01  --lt_threshold                          2000
% 1.95/1.01  --clause_weak_htbl                      true
% 1.95/1.01  --gc_record_bc_elim                     false
% 1.95/1.01  
% 1.95/1.01  ------ Preprocessing Options
% 1.95/1.01  
% 1.95/1.01  --preprocessing_flag                    true
% 1.95/1.01  --time_out_prep_mult                    0.1
% 1.95/1.01  --splitting_mode                        input
% 1.95/1.01  --splitting_grd                         true
% 1.95/1.01  --splitting_cvd                         false
% 1.95/1.01  --splitting_cvd_svl                     false
% 1.95/1.01  --splitting_nvd                         32
% 1.95/1.01  --sub_typing                            true
% 1.95/1.01  --prep_gs_sim                           true
% 1.95/1.01  --prep_unflatten                        true
% 1.95/1.01  --prep_res_sim                          true
% 1.95/1.01  --prep_upred                            true
% 1.95/1.01  --prep_sem_filter                       exhaustive
% 1.95/1.01  --prep_sem_filter_out                   false
% 1.95/1.01  --pred_elim                             true
% 1.95/1.01  --res_sim_input                         true
% 1.95/1.01  --eq_ax_congr_red                       true
% 1.95/1.01  --pure_diseq_elim                       true
% 1.95/1.01  --brand_transform                       false
% 1.95/1.01  --non_eq_to_eq                          false
% 1.95/1.01  --prep_def_merge                        true
% 1.95/1.01  --prep_def_merge_prop_impl              false
% 1.95/1.01  --prep_def_merge_mbd                    true
% 1.95/1.01  --prep_def_merge_tr_red                 false
% 1.95/1.01  --prep_def_merge_tr_cl                  false
% 1.95/1.01  --smt_preprocessing                     true
% 1.95/1.01  --smt_ac_axioms                         fast
% 1.95/1.01  --preprocessed_out                      false
% 1.95/1.01  --preprocessed_stats                    false
% 1.95/1.01  
% 1.95/1.01  ------ Abstraction refinement Options
% 1.95/1.01  
% 1.95/1.01  --abstr_ref                             []
% 1.95/1.01  --abstr_ref_prep                        false
% 1.95/1.01  --abstr_ref_until_sat                   false
% 1.95/1.01  --abstr_ref_sig_restrict                funpre
% 1.95/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.95/1.01  --abstr_ref_under                       []
% 1.95/1.01  
% 1.95/1.01  ------ SAT Options
% 1.95/1.01  
% 1.95/1.01  --sat_mode                              false
% 1.95/1.01  --sat_fm_restart_options                ""
% 1.95/1.01  --sat_gr_def                            false
% 1.95/1.01  --sat_epr_types                         true
% 1.95/1.01  --sat_non_cyclic_types                  false
% 1.95/1.01  --sat_finite_models                     false
% 1.95/1.01  --sat_fm_lemmas                         false
% 1.95/1.01  --sat_fm_prep                           false
% 1.95/1.01  --sat_fm_uc_incr                        true
% 1.95/1.01  --sat_out_model                         small
% 1.95/1.01  --sat_out_clauses                       false
% 1.95/1.01  
% 1.95/1.01  ------ QBF Options
% 1.95/1.01  
% 1.95/1.01  --qbf_mode                              false
% 1.95/1.01  --qbf_elim_univ                         false
% 1.95/1.01  --qbf_dom_inst                          none
% 1.95/1.01  --qbf_dom_pre_inst                      false
% 1.95/1.01  --qbf_sk_in                             false
% 1.95/1.01  --qbf_pred_elim                         true
% 1.95/1.01  --qbf_split                             512
% 1.95/1.01  
% 1.95/1.01  ------ BMC1 Options
% 1.95/1.01  
% 1.95/1.01  --bmc1_incremental                      false
% 1.95/1.01  --bmc1_axioms                           reachable_all
% 1.95/1.01  --bmc1_min_bound                        0
% 1.95/1.01  --bmc1_max_bound                        -1
% 1.95/1.01  --bmc1_max_bound_default                -1
% 1.95/1.01  --bmc1_symbol_reachability              true
% 1.95/1.01  --bmc1_property_lemmas                  false
% 1.95/1.01  --bmc1_k_induction                      false
% 1.95/1.01  --bmc1_non_equiv_states                 false
% 1.95/1.01  --bmc1_deadlock                         false
% 1.95/1.01  --bmc1_ucm                              false
% 1.95/1.01  --bmc1_add_unsat_core                   none
% 1.95/1.01  --bmc1_unsat_core_children              false
% 1.95/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.95/1.01  --bmc1_out_stat                         full
% 1.95/1.01  --bmc1_ground_init                      false
% 1.95/1.01  --bmc1_pre_inst_next_state              false
% 1.95/1.01  --bmc1_pre_inst_state                   false
% 1.95/1.01  --bmc1_pre_inst_reach_state             false
% 1.95/1.01  --bmc1_out_unsat_core                   false
% 1.95/1.01  --bmc1_aig_witness_out                  false
% 1.95/1.01  --bmc1_verbose                          false
% 1.95/1.01  --bmc1_dump_clauses_tptp                false
% 1.95/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.95/1.01  --bmc1_dump_file                        -
% 1.95/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.95/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.95/1.01  --bmc1_ucm_extend_mode                  1
% 1.95/1.01  --bmc1_ucm_init_mode                    2
% 1.95/1.01  --bmc1_ucm_cone_mode                    none
% 1.95/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.95/1.01  --bmc1_ucm_relax_model                  4
% 1.95/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.95/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.95/1.01  --bmc1_ucm_layered_model                none
% 1.95/1.01  --bmc1_ucm_max_lemma_size               10
% 1.95/1.01  
% 1.95/1.01  ------ AIG Options
% 1.95/1.01  
% 1.95/1.01  --aig_mode                              false
% 1.95/1.01  
% 1.95/1.01  ------ Instantiation Options
% 1.95/1.01  
% 1.95/1.01  --instantiation_flag                    true
% 1.95/1.01  --inst_sos_flag                         false
% 1.95/1.01  --inst_sos_phase                        true
% 1.95/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.95/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.95/1.01  --inst_lit_sel_side                     none
% 1.95/1.01  --inst_solver_per_active                1400
% 1.95/1.01  --inst_solver_calls_frac                1.
% 1.95/1.01  --inst_passive_queue_type               priority_queues
% 1.95/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.95/1.01  --inst_passive_queues_freq              [25;2]
% 1.95/1.01  --inst_dismatching                      true
% 1.95/1.01  --inst_eager_unprocessed_to_passive     true
% 1.95/1.01  --inst_prop_sim_given                   true
% 1.95/1.01  --inst_prop_sim_new                     false
% 1.95/1.01  --inst_subs_new                         false
% 1.95/1.01  --inst_eq_res_simp                      false
% 1.95/1.01  --inst_subs_given                       false
% 1.95/1.01  --inst_orphan_elimination               true
% 1.95/1.01  --inst_learning_loop_flag               true
% 1.95/1.01  --inst_learning_start                   3000
% 1.95/1.01  --inst_learning_factor                  2
% 1.95/1.01  --inst_start_prop_sim_after_learn       3
% 1.95/1.01  --inst_sel_renew                        solver
% 1.95/1.01  --inst_lit_activity_flag                true
% 1.95/1.01  --inst_restr_to_given                   false
% 1.95/1.01  --inst_activity_threshold               500
% 1.95/1.01  --inst_out_proof                        true
% 1.95/1.01  
% 1.95/1.01  ------ Resolution Options
% 1.95/1.01  
% 1.95/1.01  --resolution_flag                       false
% 1.95/1.01  --res_lit_sel                           adaptive
% 1.95/1.01  --res_lit_sel_side                      none
% 1.95/1.01  --res_ordering                          kbo
% 1.95/1.01  --res_to_prop_solver                    active
% 1.95/1.01  --res_prop_simpl_new                    false
% 1.95/1.01  --res_prop_simpl_given                  true
% 1.95/1.01  --res_passive_queue_type                priority_queues
% 1.95/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.95/1.01  --res_passive_queues_freq               [15;5]
% 1.95/1.01  --res_forward_subs                      full
% 1.95/1.01  --res_backward_subs                     full
% 1.95/1.01  --res_forward_subs_resolution           true
% 1.95/1.01  --res_backward_subs_resolution          true
% 1.95/1.01  --res_orphan_elimination                true
% 1.95/1.01  --res_time_limit                        2.
% 1.95/1.01  --res_out_proof                         true
% 1.95/1.01  
% 1.95/1.01  ------ Superposition Options
% 1.95/1.01  
% 1.95/1.01  --superposition_flag                    true
% 1.95/1.01  --sup_passive_queue_type                priority_queues
% 1.95/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.95/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.95/1.01  --demod_completeness_check              fast
% 1.95/1.01  --demod_use_ground                      true
% 1.95/1.01  --sup_to_prop_solver                    passive
% 1.95/1.01  --sup_prop_simpl_new                    true
% 1.95/1.01  --sup_prop_simpl_given                  true
% 1.95/1.01  --sup_fun_splitting                     false
% 1.95/1.01  --sup_smt_interval                      50000
% 1.95/1.01  
% 1.95/1.01  ------ Superposition Simplification Setup
% 1.95/1.01  
% 1.95/1.01  --sup_indices_passive                   []
% 1.95/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.95/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/1.01  --sup_full_bw                           [BwDemod]
% 1.95/1.01  --sup_immed_triv                        [TrivRules]
% 1.95/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.95/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/1.01  --sup_immed_bw_main                     []
% 1.95/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.95/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.95/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.95/1.01  
% 1.95/1.01  ------ Combination Options
% 1.95/1.01  
% 1.95/1.01  --comb_res_mult                         3
% 1.95/1.01  --comb_sup_mult                         2
% 1.95/1.01  --comb_inst_mult                        10
% 1.95/1.01  
% 1.95/1.01  ------ Debug Options
% 1.95/1.01  
% 1.95/1.01  --dbg_backtrace                         false
% 1.95/1.01  --dbg_dump_prop_clauses                 false
% 1.95/1.01  --dbg_dump_prop_clauses_file            -
% 1.95/1.01  --dbg_out_stat                          false
% 1.95/1.01  
% 1.95/1.01  
% 1.95/1.01  
% 1.95/1.01  
% 1.95/1.01  ------ Proving...
% 1.95/1.01  
% 1.95/1.01  
% 1.95/1.01  % SZS status Theorem for theBenchmark.p
% 1.95/1.01  
% 1.95/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.95/1.01  
% 1.95/1.01  fof(f1,axiom,(
% 1.95/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.95/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.95/1.01  
% 1.95/1.01  fof(f14,plain,(
% 1.95/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.95/1.01    inference(ennf_transformation,[],[f1])).
% 1.95/1.01  
% 1.95/1.01  fof(f28,plain,(
% 1.95/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.95/1.01    inference(nnf_transformation,[],[f14])).
% 1.95/1.01  
% 1.95/1.01  fof(f29,plain,(
% 1.95/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.95/1.01    inference(rectify,[],[f28])).
% 1.95/1.01  
% 1.95/1.01  fof(f30,plain,(
% 1.95/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.95/1.01    introduced(choice_axiom,[])).
% 1.95/1.01  
% 1.95/1.01  fof(f31,plain,(
% 1.95/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.95/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 1.95/1.01  
% 1.95/1.01  fof(f44,plain,(
% 1.95/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 1.95/1.01    inference(cnf_transformation,[],[f31])).
% 1.95/1.01  
% 1.95/1.01  fof(f4,axiom,(
% 1.95/1.01    ! [X0] : (~v1_xboole_0(X0) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.95/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.95/1.01  
% 1.95/1.01  fof(f15,plain,(
% 1.95/1.01    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.95/1.01    inference(ennf_transformation,[],[f4])).
% 1.95/1.01  
% 1.95/1.01  fof(f34,plain,(
% 1.95/1.01    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0))))),
% 1.95/1.01    introduced(choice_axiom,[])).
% 1.95/1.01  
% 1.95/1.01  fof(f35,plain,(
% 1.95/1.01    ! [X0] : ((~v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.95/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f34])).
% 1.95/1.01  
% 1.95/1.01  fof(f50,plain,(
% 1.95/1.01    ( ! [X0] : (m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 1.95/1.01    inference(cnf_transformation,[],[f35])).
% 1.95/1.01  
% 1.95/1.01  fof(f8,axiom,(
% 1.95/1.01    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 1.95/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.95/1.01  
% 1.95/1.01  fof(f20,plain,(
% 1.95/1.01    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 1.95/1.01    inference(ennf_transformation,[],[f8])).
% 1.95/1.01  
% 1.95/1.01  fof(f56,plain,(
% 1.95/1.01    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 1.95/1.01    inference(cnf_transformation,[],[f20])).
% 1.95/1.01  
% 1.95/1.01  fof(f51,plain,(
% 1.95/1.01    ( ! [X0] : (~v1_xboole_0(sK1(X0)) | v1_xboole_0(X0)) )),
% 1.95/1.01    inference(cnf_transformation,[],[f35])).
% 1.95/1.01  
% 1.95/1.01  fof(f11,axiom,(
% 1.95/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.95/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.95/1.01  
% 1.95/1.01  fof(f24,plain,(
% 1.95/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.95/1.01    inference(ennf_transformation,[],[f11])).
% 1.95/1.01  
% 1.95/1.01  fof(f25,plain,(
% 1.95/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.95/1.01    inference(flattening,[],[f24])).
% 1.95/1.01  
% 1.95/1.01  fof(f39,plain,(
% 1.95/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.95/1.01    inference(nnf_transformation,[],[f25])).
% 1.95/1.01  
% 1.95/1.01  fof(f60,plain,(
% 1.95/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.95/1.01    inference(cnf_transformation,[],[f39])).
% 1.95/1.01  
% 1.95/1.01  fof(f12,conjecture,(
% 1.95/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.95/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.95/1.01  
% 1.95/1.01  fof(f13,negated_conjecture,(
% 1.95/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.95/1.01    inference(negated_conjecture,[],[f12])).
% 1.95/1.01  
% 1.95/1.01  fof(f26,plain,(
% 1.95/1.01    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.95/1.01    inference(ennf_transformation,[],[f13])).
% 1.95/1.01  
% 1.95/1.01  fof(f27,plain,(
% 1.95/1.01    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.95/1.01    inference(flattening,[],[f26])).
% 1.95/1.01  
% 1.95/1.01  fof(f41,plain,(
% 1.95/1.01    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK6) & ! [X4] : (k1_funct_1(sK6,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK6,X0,X1) & v1_funct_1(sK6))) )),
% 1.95/1.01    introduced(choice_axiom,[])).
% 1.95/1.01  
% 1.95/1.01  fof(f40,plain,(
% 1.95/1.01    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK3,sK4,sK5,X3) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 1.95/1.01    introduced(choice_axiom,[])).
% 1.95/1.01  
% 1.95/1.01  fof(f42,plain,(
% 1.95/1.01    (~r2_relset_1(sK3,sK4,sK5,sK6) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~r2_hidden(X4,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 1.95/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f27,f41,f40])).
% 1.95/1.01  
% 1.95/1.01  fof(f70,plain,(
% 1.95/1.01    v1_funct_2(sK6,sK3,sK4)),
% 1.95/1.01    inference(cnf_transformation,[],[f42])).
% 1.95/1.01  
% 1.95/1.01  fof(f71,plain,(
% 1.95/1.01    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 1.95/1.01    inference(cnf_transformation,[],[f42])).
% 1.95/1.01  
% 1.95/1.01  fof(f9,axiom,(
% 1.95/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.95/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.95/1.01  
% 1.95/1.01  fof(f21,plain,(
% 1.95/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.95/1.01    inference(ennf_transformation,[],[f9])).
% 1.95/1.01  
% 1.95/1.01  fof(f57,plain,(
% 1.95/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.95/1.01    inference(cnf_transformation,[],[f21])).
% 1.95/1.01  
% 1.95/1.01  fof(f67,plain,(
% 1.95/1.01    v1_funct_2(sK5,sK3,sK4)),
% 1.95/1.01    inference(cnf_transformation,[],[f42])).
% 1.95/1.01  
% 1.95/1.01  fof(f68,plain,(
% 1.95/1.01    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 1.95/1.01    inference(cnf_transformation,[],[f42])).
% 1.95/1.01  
% 1.95/1.01  fof(f6,axiom,(
% 1.95/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 1.95/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.95/1.01  
% 1.95/1.01  fof(f17,plain,(
% 1.95/1.01    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.95/1.01    inference(ennf_transformation,[],[f6])).
% 1.95/1.01  
% 1.95/1.01  fof(f18,plain,(
% 1.95/1.01    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.95/1.01    inference(flattening,[],[f17])).
% 1.95/1.01  
% 1.95/1.01  fof(f36,plain,(
% 1.95/1.01    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))),
% 1.95/1.01    introduced(choice_axiom,[])).
% 1.95/1.01  
% 1.95/1.01  fof(f37,plain,(
% 1.95/1.01    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.95/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f36])).
% 1.95/1.01  
% 1.95/1.01  fof(f53,plain,(
% 1.95/1.01    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.95/1.01    inference(cnf_transformation,[],[f37])).
% 1.95/1.01  
% 1.95/1.01  fof(f69,plain,(
% 1.95/1.01    v1_funct_1(sK6)),
% 1.95/1.01    inference(cnf_transformation,[],[f42])).
% 1.95/1.01  
% 1.95/1.01  fof(f7,axiom,(
% 1.95/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.95/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.95/1.01  
% 1.95/1.01  fof(f19,plain,(
% 1.95/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.95/1.01    inference(ennf_transformation,[],[f7])).
% 1.95/1.01  
% 1.95/1.01  fof(f55,plain,(
% 1.95/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.95/1.01    inference(cnf_transformation,[],[f19])).
% 1.95/1.01  
% 1.95/1.01  fof(f66,plain,(
% 1.95/1.01    v1_funct_1(sK5)),
% 1.95/1.01    inference(cnf_transformation,[],[f42])).
% 1.95/1.01  
% 1.95/1.01  fof(f10,axiom,(
% 1.95/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.95/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.95/1.01  
% 1.95/1.01  fof(f22,plain,(
% 1.95/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.95/1.01    inference(ennf_transformation,[],[f10])).
% 1.95/1.01  
% 1.95/1.01  fof(f23,plain,(
% 1.95/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.95/1.01    inference(flattening,[],[f22])).
% 1.95/1.01  
% 1.95/1.01  fof(f38,plain,(
% 1.95/1.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.95/1.01    inference(nnf_transformation,[],[f23])).
% 1.95/1.01  
% 1.95/1.01  fof(f59,plain,(
% 1.95/1.01    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.95/1.01    inference(cnf_transformation,[],[f38])).
% 1.95/1.01  
% 1.95/1.01  fof(f76,plain,(
% 1.95/1.01    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.95/1.01    inference(equality_resolution,[],[f59])).
% 1.95/1.01  
% 1.95/1.01  fof(f73,plain,(
% 1.95/1.01    ~r2_relset_1(sK3,sK4,sK5,sK6)),
% 1.95/1.01    inference(cnf_transformation,[],[f42])).
% 1.95/1.01  
% 1.95/1.01  fof(f72,plain,(
% 1.95/1.01    ( ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~r2_hidden(X4,sK3)) )),
% 1.95/1.01    inference(cnf_transformation,[],[f42])).
% 1.95/1.01  
% 1.95/1.01  fof(f54,plain,(
% 1.95/1.01    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.95/1.01    inference(cnf_transformation,[],[f37])).
% 1.95/1.01  
% 1.95/1.01  fof(f5,axiom,(
% 1.95/1.01    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.95/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.95/1.01  
% 1.95/1.01  fof(f16,plain,(
% 1.95/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.95/1.01    inference(ennf_transformation,[],[f5])).
% 1.95/1.01  
% 1.95/1.01  fof(f52,plain,(
% 1.95/1.01    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.95/1.01    inference(cnf_transformation,[],[f16])).
% 1.95/1.01  
% 1.95/1.01  fof(f2,axiom,(
% 1.95/1.01    v1_xboole_0(k1_xboole_0)),
% 1.95/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.95/1.01  
% 1.95/1.01  fof(f46,plain,(
% 1.95/1.01    v1_xboole_0(k1_xboole_0)),
% 1.95/1.01    inference(cnf_transformation,[],[f2])).
% 1.95/1.01  
% 1.95/1.01  fof(f3,axiom,(
% 1.95/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.95/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.95/1.01  
% 1.95/1.01  fof(f32,plain,(
% 1.95/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.95/1.01    inference(nnf_transformation,[],[f3])).
% 1.95/1.01  
% 1.95/1.01  fof(f33,plain,(
% 1.95/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.95/1.01    inference(flattening,[],[f32])).
% 1.95/1.01  
% 1.95/1.01  fof(f49,plain,(
% 1.95/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.95/1.01    inference(cnf_transformation,[],[f33])).
% 1.95/1.01  
% 1.95/1.01  cnf(c_1,plain,
% 1.95/1.01      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 1.95/1.01      inference(cnf_transformation,[],[f44]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_1924,plain,
% 1.95/1.01      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 1.95/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 1.95/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_8,plain,
% 1.95/1.01      ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) | v1_xboole_0(X0) ),
% 1.95/1.01      inference(cnf_transformation,[],[f50]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_1918,plain,
% 1.95/1.01      ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) = iProver_top
% 1.95/1.01      | v1_xboole_0(X0) = iProver_top ),
% 1.95/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_13,plain,
% 1.95/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.95/1.01      | ~ v1_xboole_0(X2)
% 1.95/1.01      | v1_xboole_0(X0) ),
% 1.95/1.01      inference(cnf_transformation,[],[f56]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_1913,plain,
% 1.95/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 1.95/1.01      | v1_xboole_0(X2) != iProver_top
% 1.95/1.01      | v1_xboole_0(X0) = iProver_top ),
% 1.95/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_2636,plain,
% 1.95/1.01      ( v1_xboole_0(X0) != iProver_top
% 1.95/1.01      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top
% 1.95/1.01      | v1_xboole_0(sK1(k2_zfmisc_1(X1,X0))) = iProver_top ),
% 1.95/1.01      inference(superposition,[status(thm)],[c_1918,c_1913]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_7,plain,
% 1.95/1.01      ( v1_xboole_0(X0) | ~ v1_xboole_0(sK1(X0)) ),
% 1.95/1.01      inference(cnf_transformation,[],[f51]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_1919,plain,
% 1.95/1.01      ( v1_xboole_0(X0) = iProver_top
% 1.95/1.01      | v1_xboole_0(sK1(X0)) != iProver_top ),
% 1.95/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_4514,plain,
% 1.95/1.01      ( v1_xboole_0(X0) != iProver_top
% 1.95/1.01      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 1.95/1.01      inference(forward_subsumption_resolution,
% 1.95/1.01                [status(thm)],
% 1.95/1.01                [c_2636,c_1919]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_22,plain,
% 1.95/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 1.95/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.95/1.01      | k1_relset_1(X1,X2,X0) = X1
% 1.95/1.01      | k1_xboole_0 = X2 ),
% 1.95/1.01      inference(cnf_transformation,[],[f60]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_26,negated_conjecture,
% 1.95/1.01      ( v1_funct_2(sK6,sK3,sK4) ),
% 1.95/1.01      inference(cnf_transformation,[],[f70]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_417,plain,
% 1.95/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.95/1.01      | k1_relset_1(X1,X2,X0) = X1
% 1.95/1.01      | sK6 != X0
% 1.95/1.01      | sK4 != X2
% 1.95/1.01      | sK3 != X1
% 1.95/1.01      | k1_xboole_0 = X2 ),
% 1.95/1.01      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_418,plain,
% 1.95/1.01      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 1.95/1.01      | k1_relset_1(sK3,sK4,sK6) = sK3
% 1.95/1.01      | k1_xboole_0 = sK4 ),
% 1.95/1.01      inference(unflattening,[status(thm)],[c_417]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_25,negated_conjecture,
% 1.95/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 1.95/1.01      inference(cnf_transformation,[],[f71]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_420,plain,
% 1.95/1.01      ( k1_relset_1(sK3,sK4,sK6) = sK3 | k1_xboole_0 = sK4 ),
% 1.95/1.01      inference(global_propositional_subsumption,
% 1.95/1.01                [status(thm)],
% 1.95/1.01                [c_418,c_25]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_1910,plain,
% 1.95/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 1.95/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_14,plain,
% 1.95/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.95/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.95/1.01      inference(cnf_transformation,[],[f57]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_1912,plain,
% 1.95/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.95/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.95/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_2619,plain,
% 1.95/1.01      ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
% 1.95/1.01      inference(superposition,[status(thm)],[c_1910,c_1912]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_2886,plain,
% 1.95/1.01      ( k1_relat_1(sK6) = sK3 | sK4 = k1_xboole_0 ),
% 1.95/1.01      inference(superposition,[status(thm)],[c_420,c_2619]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_29,negated_conjecture,
% 1.95/1.01      ( v1_funct_2(sK5,sK3,sK4) ),
% 1.95/1.01      inference(cnf_transformation,[],[f67]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_428,plain,
% 1.95/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.95/1.01      | k1_relset_1(X1,X2,X0) = X1
% 1.95/1.01      | sK5 != X0
% 1.95/1.01      | sK4 != X2
% 1.95/1.01      | sK3 != X1
% 1.95/1.01      | k1_xboole_0 = X2 ),
% 1.95/1.01      inference(resolution_lifted,[status(thm)],[c_22,c_29]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_429,plain,
% 1.95/1.01      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 1.95/1.01      | k1_relset_1(sK3,sK4,sK5) = sK3
% 1.95/1.01      | k1_xboole_0 = sK4 ),
% 1.95/1.01      inference(unflattening,[status(thm)],[c_428]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_28,negated_conjecture,
% 1.95/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 1.95/1.01      inference(cnf_transformation,[],[f68]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_431,plain,
% 1.95/1.01      ( k1_relset_1(sK3,sK4,sK5) = sK3 | k1_xboole_0 = sK4 ),
% 1.95/1.01      inference(global_propositional_subsumption,
% 1.95/1.01                [status(thm)],
% 1.95/1.01                [c_429,c_28]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_1908,plain,
% 1.95/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 1.95/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_2620,plain,
% 1.95/1.01      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 1.95/1.01      inference(superposition,[status(thm)],[c_1908,c_1912]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_2889,plain,
% 1.95/1.01      ( k1_relat_1(sK5) = sK3 | sK4 = k1_xboole_0 ),
% 1.95/1.01      inference(superposition,[status(thm)],[c_431,c_2620]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_11,plain,
% 1.95/1.01      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 1.95/1.01      | ~ v1_relat_1(X1)
% 1.95/1.01      | ~ v1_relat_1(X0)
% 1.95/1.01      | ~ v1_funct_1(X1)
% 1.95/1.01      | ~ v1_funct_1(X0)
% 1.95/1.01      | X1 = X0
% 1.95/1.01      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 1.95/1.01      inference(cnf_transformation,[],[f53]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_1915,plain,
% 1.95/1.01      ( X0 = X1
% 1.95/1.01      | k1_relat_1(X0) != k1_relat_1(X1)
% 1.95/1.01      | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
% 1.95/1.01      | v1_relat_1(X1) != iProver_top
% 1.95/1.01      | v1_relat_1(X0) != iProver_top
% 1.95/1.01      | v1_funct_1(X0) != iProver_top
% 1.95/1.01      | v1_funct_1(X1) != iProver_top ),
% 1.95/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_3363,plain,
% 1.95/1.01      ( k1_relat_1(X0) != sK3
% 1.95/1.01      | sK6 = X0
% 1.95/1.01      | sK4 = k1_xboole_0
% 1.95/1.01      | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
% 1.95/1.01      | v1_relat_1(X0) != iProver_top
% 1.95/1.01      | v1_relat_1(sK6) != iProver_top
% 1.95/1.01      | v1_funct_1(X0) != iProver_top
% 1.95/1.01      | v1_funct_1(sK6) != iProver_top ),
% 1.95/1.01      inference(superposition,[status(thm)],[c_2886,c_1915]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_27,negated_conjecture,
% 1.95/1.01      ( v1_funct_1(sK6) ),
% 1.95/1.01      inference(cnf_transformation,[],[f69]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_34,plain,
% 1.95/1.01      ( v1_funct_1(sK6) = iProver_top ),
% 1.95/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_36,plain,
% 1.95/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 1.95/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_12,plain,
% 1.95/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.95/1.01      | v1_relat_1(X0) ),
% 1.95/1.01      inference(cnf_transformation,[],[f55]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_2109,plain,
% 1.95/1.01      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 1.95/1.01      | v1_relat_1(sK6) ),
% 1.95/1.01      inference(instantiation,[status(thm)],[c_12]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_2110,plain,
% 1.95/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 1.95/1.01      | v1_relat_1(sK6) = iProver_top ),
% 1.95/1.01      inference(predicate_to_equality,[status(thm)],[c_2109]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_3557,plain,
% 1.95/1.01      ( v1_funct_1(X0) != iProver_top
% 1.95/1.01      | k1_relat_1(X0) != sK3
% 1.95/1.01      | sK6 = X0
% 1.95/1.01      | sK4 = k1_xboole_0
% 1.95/1.01      | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
% 1.95/1.01      | v1_relat_1(X0) != iProver_top ),
% 1.95/1.01      inference(global_propositional_subsumption,
% 1.95/1.01                [status(thm)],
% 1.95/1.01                [c_3363,c_34,c_36,c_2110]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_3558,plain,
% 1.95/1.01      ( k1_relat_1(X0) != sK3
% 1.95/1.01      | sK6 = X0
% 1.95/1.01      | sK4 = k1_xboole_0
% 1.95/1.01      | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
% 1.95/1.01      | v1_relat_1(X0) != iProver_top
% 1.95/1.01      | v1_funct_1(X0) != iProver_top ),
% 1.95/1.01      inference(renaming,[status(thm)],[c_3557]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_3570,plain,
% 1.95/1.01      ( sK6 = sK5
% 1.95/1.01      | sK4 = k1_xboole_0
% 1.95/1.01      | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top
% 1.95/1.01      | v1_relat_1(sK5) != iProver_top
% 1.95/1.01      | v1_funct_1(sK5) != iProver_top ),
% 1.95/1.01      inference(superposition,[status(thm)],[c_2889,c_3558]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_30,negated_conjecture,
% 1.95/1.01      ( v1_funct_1(sK5) ),
% 1.95/1.01      inference(cnf_transformation,[],[f66]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_31,plain,
% 1.95/1.01      ( v1_funct_1(sK5) = iProver_top ),
% 1.95/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_33,plain,
% 1.95/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 1.95/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_15,plain,
% 1.95/1.01      ( r2_relset_1(X0,X1,X2,X2)
% 1.95/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 1.95/1.01      inference(cnf_transformation,[],[f76]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_23,negated_conjecture,
% 1.95/1.01      ( ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
% 1.95/1.01      inference(cnf_transformation,[],[f73]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_334,plain,
% 1.95/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.95/1.01      | sK6 != X0
% 1.95/1.01      | sK5 != X0
% 1.95/1.01      | sK4 != X2
% 1.95/1.01      | sK3 != X1 ),
% 1.95/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_23]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_335,plain,
% 1.95/1.01      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 1.95/1.01      | sK5 != sK6 ),
% 1.95/1.01      inference(unflattening,[status(thm)],[c_334]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_2112,plain,
% 1.95/1.01      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 1.95/1.01      | v1_relat_1(sK5) ),
% 1.95/1.01      inference(instantiation,[status(thm)],[c_12]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_2113,plain,
% 1.95/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 1.95/1.01      | v1_relat_1(sK5) = iProver_top ),
% 1.95/1.01      inference(predicate_to_equality,[status(thm)],[c_2112]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_1495,plain,( X0 = X0 ),theory(equality) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_2235,plain,
% 1.95/1.01      ( sK5 = sK5 ),
% 1.95/1.01      inference(instantiation,[status(thm)],[c_1495]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_1496,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_2138,plain,
% 1.95/1.01      ( sK6 != X0 | sK5 != X0 | sK5 = sK6 ),
% 1.95/1.01      inference(instantiation,[status(thm)],[c_1496]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_2803,plain,
% 1.95/1.01      ( sK6 != sK5 | sK5 = sK6 | sK5 != sK5 ),
% 1.95/1.01      inference(instantiation,[status(thm)],[c_2138]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_3637,plain,
% 1.95/1.01      ( sK4 = k1_xboole_0
% 1.95/1.01      | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top ),
% 1.95/1.01      inference(global_propositional_subsumption,
% 1.95/1.01                [status(thm)],
% 1.95/1.01                [c_3570,c_31,c_33,c_25,c_335,c_2113,c_2235,c_2803]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_3643,plain,
% 1.95/1.01      ( sK4 = k1_xboole_0 | r2_hidden(sK2(sK5,sK6),sK3) = iProver_top ),
% 1.95/1.01      inference(superposition,[status(thm)],[c_2889,c_3637]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_24,negated_conjecture,
% 1.95/1.01      ( ~ r2_hidden(X0,sK3) | k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0) ),
% 1.95/1.01      inference(cnf_transformation,[],[f72]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_1911,plain,
% 1.95/1.01      ( k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0)
% 1.95/1.01      | r2_hidden(X0,sK3) != iProver_top ),
% 1.95/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_3663,plain,
% 1.95/1.01      ( k1_funct_1(sK5,sK2(sK5,sK6)) = k1_funct_1(sK6,sK2(sK5,sK6))
% 1.95/1.01      | sK4 = k1_xboole_0 ),
% 1.95/1.01      inference(superposition,[status(thm)],[c_3643,c_1911]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_10,plain,
% 1.95/1.01      ( ~ v1_relat_1(X0)
% 1.95/1.01      | ~ v1_relat_1(X1)
% 1.95/1.01      | ~ v1_funct_1(X0)
% 1.95/1.01      | ~ v1_funct_1(X1)
% 1.95/1.01      | X0 = X1
% 1.95/1.01      | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
% 1.95/1.01      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 1.95/1.01      inference(cnf_transformation,[],[f54]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_1916,plain,
% 1.95/1.01      ( X0 = X1
% 1.95/1.01      | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
% 1.95/1.01      | k1_relat_1(X0) != k1_relat_1(X1)
% 1.95/1.01      | v1_relat_1(X0) != iProver_top
% 1.95/1.01      | v1_relat_1(X1) != iProver_top
% 1.95/1.01      | v1_funct_1(X1) != iProver_top
% 1.95/1.01      | v1_funct_1(X0) != iProver_top ),
% 1.95/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_3716,plain,
% 1.95/1.01      ( k1_relat_1(sK5) != k1_relat_1(sK6)
% 1.95/1.01      | sK6 = sK5
% 1.95/1.01      | sK4 = k1_xboole_0
% 1.95/1.01      | v1_relat_1(sK6) != iProver_top
% 1.95/1.01      | v1_relat_1(sK5) != iProver_top
% 1.95/1.01      | v1_funct_1(sK6) != iProver_top
% 1.95/1.01      | v1_funct_1(sK5) != iProver_top ),
% 1.95/1.01      inference(superposition,[status(thm)],[c_3663,c_1916]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_3717,plain,
% 1.95/1.01      ( ~ v1_relat_1(sK6)
% 1.95/1.01      | ~ v1_relat_1(sK5)
% 1.95/1.01      | ~ v1_funct_1(sK6)
% 1.95/1.01      | ~ v1_funct_1(sK5)
% 1.95/1.01      | k1_relat_1(sK5) != k1_relat_1(sK6)
% 1.95/1.01      | sK6 = sK5
% 1.95/1.01      | sK4 = k1_xboole_0 ),
% 1.95/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_3716]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_3719,plain,
% 1.95/1.01      ( k1_relat_1(sK5) != k1_relat_1(sK6) | sK4 = k1_xboole_0 ),
% 1.95/1.01      inference(global_propositional_subsumption,
% 1.95/1.01                [status(thm)],
% 1.95/1.01                [c_3716,c_30,c_28,c_27,c_25,c_335,c_2109,c_2112,c_2235,
% 1.95/1.01                 c_2803,c_3717]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_3723,plain,
% 1.95/1.01      ( k1_relat_1(sK5) != sK3 | sK4 = k1_xboole_0 ),
% 1.95/1.01      inference(superposition,[status(thm)],[c_2886,c_3719]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_3751,plain,
% 1.95/1.01      ( sK4 = k1_xboole_0 ),
% 1.95/1.01      inference(global_propositional_subsumption,
% 1.95/1.01                [status(thm)],
% 1.95/1.01                [c_3723,c_2889]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_9,plain,
% 1.95/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.95/1.01      | ~ r2_hidden(X2,X0)
% 1.95/1.01      | ~ v1_xboole_0(X1) ),
% 1.95/1.01      inference(cnf_transformation,[],[f52]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_1917,plain,
% 1.95/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.95/1.01      | r2_hidden(X2,X0) != iProver_top
% 1.95/1.01      | v1_xboole_0(X1) != iProver_top ),
% 1.95/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_2841,plain,
% 1.95/1.01      ( r2_hidden(X0,sK5) != iProver_top
% 1.95/1.01      | v1_xboole_0(k2_zfmisc_1(sK3,sK4)) != iProver_top ),
% 1.95/1.01      inference(superposition,[status(thm)],[c_1908,c_1917]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_3756,plain,
% 1.95/1.01      ( r2_hidden(X0,sK5) != iProver_top
% 1.95/1.01      | v1_xboole_0(k2_zfmisc_1(sK3,k1_xboole_0)) != iProver_top ),
% 1.95/1.01      inference(demodulation,[status(thm)],[c_3751,c_2841]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_4519,plain,
% 1.95/1.01      ( r2_hidden(X0,sK5) != iProver_top
% 1.95/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 1.95/1.01      inference(superposition,[status(thm)],[c_4514,c_3756]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_3,plain,
% 1.95/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 1.95/1.01      inference(cnf_transformation,[],[f46]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_94,plain,
% 1.95/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 1.95/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_5228,plain,
% 1.95/1.01      ( r2_hidden(X0,sK5) != iProver_top ),
% 1.95/1.01      inference(global_propositional_subsumption,
% 1.95/1.01                [status(thm)],
% 1.95/1.01                [c_4519,c_94]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_5235,plain,
% 1.95/1.01      ( r1_tarski(sK5,X0) = iProver_top ),
% 1.95/1.01      inference(superposition,[status(thm)],[c_1924,c_5228]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_2840,plain,
% 1.95/1.01      ( r2_hidden(X0,sK6) != iProver_top
% 1.95/1.01      | v1_xboole_0(k2_zfmisc_1(sK3,sK4)) != iProver_top ),
% 1.95/1.01      inference(superposition,[status(thm)],[c_1910,c_1917]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_3757,plain,
% 1.95/1.01      ( r2_hidden(X0,sK6) != iProver_top
% 1.95/1.01      | v1_xboole_0(k2_zfmisc_1(sK3,k1_xboole_0)) != iProver_top ),
% 1.95/1.01      inference(demodulation,[status(thm)],[c_3751,c_2840]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_4518,plain,
% 1.95/1.01      ( r2_hidden(X0,sK6) != iProver_top
% 1.95/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 1.95/1.01      inference(superposition,[status(thm)],[c_4514,c_3757]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_4827,plain,
% 1.95/1.01      ( r2_hidden(X0,sK6) != iProver_top ),
% 1.95/1.01      inference(global_propositional_subsumption,
% 1.95/1.01                [status(thm)],
% 1.95/1.01                [c_4518,c_94]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_4834,plain,
% 1.95/1.01      ( r1_tarski(sK6,X0) = iProver_top ),
% 1.95/1.01      inference(superposition,[status(thm)],[c_1924,c_4827]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_4,plain,
% 1.95/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 1.95/1.01      inference(cnf_transformation,[],[f49]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_1921,plain,
% 1.95/1.01      ( X0 = X1
% 1.95/1.01      | r1_tarski(X1,X0) != iProver_top
% 1.95/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 1.95/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_4848,plain,
% 1.95/1.01      ( sK6 = X0 | r1_tarski(X0,sK6) != iProver_top ),
% 1.95/1.01      inference(superposition,[status(thm)],[c_4834,c_1921]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_5412,plain,
% 1.95/1.01      ( sK6 = sK5 ),
% 1.95/1.01      inference(superposition,[status(thm)],[c_5235,c_4848]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(contradiction,plain,
% 1.95/1.01      ( $false ),
% 1.95/1.01      inference(minisat,[status(thm)],[c_5412,c_2803,c_2235,c_335,c_25]) ).
% 1.95/1.01  
% 1.95/1.01  
% 1.95/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.95/1.01  
% 1.95/1.01  ------                               Statistics
% 1.95/1.01  
% 1.95/1.01  ------ General
% 1.95/1.01  
% 1.95/1.01  abstr_ref_over_cycles:                  0
% 1.95/1.01  abstr_ref_under_cycles:                 0
% 1.95/1.01  gc_basic_clause_elim:                   0
% 1.95/1.01  forced_gc_time:                         0
% 1.95/1.01  parsing_time:                           0.029
% 1.95/1.01  unif_index_cands_time:                  0.
% 1.95/1.01  unif_index_add_time:                    0.
% 1.95/1.01  orderings_time:                         0.
% 1.95/1.01  out_proof_time:                         0.012
% 1.95/1.01  total_time:                             0.188
% 1.95/1.01  num_of_symbols:                         52
% 1.95/1.01  num_of_terms:                           3826
% 1.95/1.01  
% 1.95/1.01  ------ Preprocessing
% 1.95/1.01  
% 1.95/1.01  num_of_splits:                          0
% 1.95/1.01  num_of_split_atoms:                     0
% 1.95/1.01  num_of_reused_defs:                     0
% 1.95/1.01  num_eq_ax_congr_red:                    29
% 1.95/1.01  num_of_sem_filtered_clauses:            1
% 1.95/1.01  num_of_subtypes:                        0
% 1.95/1.01  monotx_restored_types:                  0
% 1.95/1.01  sat_num_of_epr_types:                   0
% 1.95/1.01  sat_num_of_non_cyclic_types:            0
% 1.95/1.01  sat_guarded_non_collapsed_types:        0
% 1.95/1.01  num_pure_diseq_elim:                    0
% 1.95/1.01  simp_replaced_by:                       0
% 1.95/1.01  res_preprocessed:                       129
% 1.95/1.01  prep_upred:                             0
% 1.95/1.01  prep_unflattend:                        65
% 1.95/1.01  smt_new_axioms:                         0
% 1.95/1.01  pred_elim_cands:                        6
% 1.95/1.01  pred_elim:                              2
% 1.95/1.01  pred_elim_cl:                           4
% 1.95/1.01  pred_elim_cycles:                       4
% 1.95/1.01  merged_defs:                            0
% 1.95/1.01  merged_defs_ncl:                        0
% 1.95/1.01  bin_hyper_res:                          0
% 1.95/1.01  prep_cycles:                            4
% 1.95/1.01  pred_elim_time:                         0.019
% 1.95/1.01  splitting_time:                         0.
% 1.95/1.01  sem_filter_time:                        0.
% 1.95/1.01  monotx_time:                            0.001
% 1.95/1.01  subtype_inf_time:                       0.
% 1.95/1.01  
% 1.95/1.01  ------ Problem properties
% 1.95/1.01  
% 1.95/1.01  clauses:                                26
% 1.95/1.01  conjectures:                            5
% 1.95/1.01  epr:                                    7
% 1.95/1.01  horn:                                   19
% 1.95/1.01  ground:                                 12
% 1.95/1.01  unary:                                  7
% 1.95/1.01  binary:                                 9
% 1.95/1.01  lits:                                   65
% 1.95/1.01  lits_eq:                                23
% 1.95/1.01  fd_pure:                                0
% 1.95/1.01  fd_pseudo:                              0
% 1.95/1.01  fd_cond:                                0
% 1.95/1.01  fd_pseudo_cond:                         3
% 1.95/1.01  ac_symbols:                             0
% 1.95/1.01  
% 1.95/1.01  ------ Propositional Solver
% 1.95/1.01  
% 1.95/1.01  prop_solver_calls:                      28
% 1.95/1.01  prop_fast_solver_calls:                 1113
% 1.95/1.01  smt_solver_calls:                       0
% 1.95/1.01  smt_fast_solver_calls:                  0
% 1.95/1.01  prop_num_of_clauses:                    1511
% 1.95/1.01  prop_preprocess_simplified:             5057
% 1.95/1.01  prop_fo_subsumed:                       46
% 1.95/1.01  prop_solver_time:                       0.
% 1.95/1.01  smt_solver_time:                        0.
% 1.95/1.01  smt_fast_solver_time:                   0.
% 1.95/1.01  prop_fast_solver_time:                  0.
% 1.95/1.01  prop_unsat_core_time:                   0.
% 1.95/1.01  
% 1.95/1.01  ------ QBF
% 1.95/1.01  
% 1.95/1.01  qbf_q_res:                              0
% 1.95/1.01  qbf_num_tautologies:                    0
% 1.95/1.01  qbf_prep_cycles:                        0
% 1.95/1.01  
% 1.95/1.01  ------ BMC1
% 1.95/1.01  
% 1.95/1.01  bmc1_current_bound:                     -1
% 1.95/1.01  bmc1_last_solved_bound:                 -1
% 1.95/1.01  bmc1_unsat_core_size:                   -1
% 1.95/1.01  bmc1_unsat_core_parents_size:           -1
% 1.95/1.01  bmc1_merge_next_fun:                    0
% 1.95/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.95/1.01  
% 1.95/1.01  ------ Instantiation
% 1.95/1.01  
% 1.95/1.01  inst_num_of_clauses:                    498
% 1.95/1.01  inst_num_in_passive:                    25
% 1.95/1.01  inst_num_in_active:                     291
% 1.95/1.01  inst_num_in_unprocessed:                182
% 1.95/1.01  inst_num_of_loops:                      380
% 1.95/1.01  inst_num_of_learning_restarts:          0
% 1.95/1.01  inst_num_moves_active_passive:          86
% 1.95/1.01  inst_lit_activity:                      0
% 1.95/1.01  inst_lit_activity_moves:                0
% 1.95/1.01  inst_num_tautologies:                   0
% 1.95/1.01  inst_num_prop_implied:                  0
% 1.95/1.01  inst_num_existing_simplified:           0
% 1.95/1.01  inst_num_eq_res_simplified:             0
% 1.95/1.01  inst_num_child_elim:                    0
% 1.95/1.01  inst_num_of_dismatching_blockings:      119
% 1.95/1.01  inst_num_of_non_proper_insts:           507
% 1.95/1.01  inst_num_of_duplicates:                 0
% 1.95/1.01  inst_inst_num_from_inst_to_res:         0
% 1.95/1.01  inst_dismatching_checking_time:         0.
% 1.95/1.01  
% 1.95/1.01  ------ Resolution
% 1.95/1.01  
% 1.95/1.01  res_num_of_clauses:                     0
% 1.95/1.01  res_num_in_passive:                     0
% 1.95/1.01  res_num_in_active:                      0
% 1.95/1.01  res_num_of_loops:                       133
% 1.95/1.01  res_forward_subset_subsumed:            91
% 1.95/1.01  res_backward_subset_subsumed:           0
% 1.95/1.01  res_forward_subsumed:                   0
% 1.95/1.01  res_backward_subsumed:                  0
% 1.95/1.01  res_forward_subsumption_resolution:     1
% 1.95/1.01  res_backward_subsumption_resolution:    0
% 1.95/1.01  res_clause_to_clause_subsumption:       270
% 1.95/1.01  res_orphan_elimination:                 0
% 1.95/1.01  res_tautology_del:                      54
% 1.95/1.01  res_num_eq_res_simplified:              0
% 1.95/1.01  res_num_sel_changes:                    0
% 1.95/1.01  res_moves_from_active_to_pass:          0
% 1.95/1.01  
% 1.95/1.01  ------ Superposition
% 1.95/1.01  
% 1.95/1.01  sup_time_total:                         0.
% 1.95/1.01  sup_time_generating:                    0.
% 1.95/1.01  sup_time_sim_full:                      0.
% 1.95/1.01  sup_time_sim_immed:                     0.
% 1.95/1.01  
% 1.95/1.01  sup_num_of_clauses:                     57
% 1.95/1.01  sup_num_in_active:                      43
% 1.95/1.01  sup_num_in_passive:                     14
% 1.95/1.01  sup_num_of_loops:                       74
% 1.95/1.01  sup_fw_superposition:                   44
% 1.95/1.01  sup_bw_superposition:                   44
% 1.95/1.01  sup_immediate_simplified:               12
% 1.95/1.01  sup_given_eliminated:                   1
% 1.95/1.01  comparisons_done:                       0
% 1.95/1.01  comparisons_avoided:                    11
% 1.95/1.01  
% 1.95/1.01  ------ Simplifications
% 1.95/1.01  
% 1.95/1.01  
% 1.95/1.01  sim_fw_subset_subsumed:                 6
% 1.95/1.01  sim_bw_subset_subsumed:                 8
% 1.95/1.01  sim_fw_subsumed:                        2
% 1.95/1.01  sim_bw_subsumed:                        0
% 1.95/1.01  sim_fw_subsumption_res:                 3
% 1.95/1.01  sim_bw_subsumption_res:                 0
% 1.95/1.01  sim_tautology_del:                      2
% 1.95/1.01  sim_eq_tautology_del:                   9
% 1.95/1.01  sim_eq_res_simp:                        2
% 1.95/1.01  sim_fw_demodulated:                     0
% 1.95/1.01  sim_bw_demodulated:                     30
% 1.95/1.01  sim_light_normalised:                   5
% 1.95/1.01  sim_joinable_taut:                      0
% 1.95/1.01  sim_joinable_simp:                      0
% 1.95/1.01  sim_ac_normalised:                      0
% 1.95/1.01  sim_smt_subsumption:                    0
% 1.95/1.01  
%------------------------------------------------------------------------------
