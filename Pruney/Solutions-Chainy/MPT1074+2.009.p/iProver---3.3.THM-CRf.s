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
% DateTime   : Thu Dec  3 12:10:14 EST 2020

% Result     : Theorem 4.14s
% Output     : CNFRefutation 4.14s
% Verified   : 
% Statistics : Number of formulae       :  194 (3960 expanded)
%              Number of clauses        :  133 (1460 expanded)
%              Number of leaves         :   19 (1027 expanded)
%              Depth                    :   34
%              Number of atoms          :  627 (21434 expanded)
%              Number of equality atoms :  252 (2702 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(X3,X1,X2)
                & v1_funct_1(X3) )
             => ( ! [X4] :
                    ( m1_subset_1(X4,X1)
                   => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
               => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_2(X3,X1,X2)
                  & v1_funct_1(X3) )
               => ( ! [X4] :
                      ( m1_subset_1(X4,X1)
                     => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
                 => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f25])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
          & ! [X4] :
              ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
              | ~ m1_subset_1(X4,X1) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
     => ( ~ r1_tarski(k2_relset_1(X1,X2,sK4),X0)
        & ! [X4] :
            ( r2_hidden(k3_funct_2(X1,X2,sK4,X4),X0)
            | ~ m1_subset_1(X4,X1) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK4,X1,X2)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
     => ( ? [X3] :
            ( ~ r1_tarski(k2_relset_1(X1,sK3,X3),X0)
            & ! [X4] :
                ( r2_hidden(k3_funct_2(X1,sK3,X3,X4),X0)
                | ~ m1_subset_1(X4,X1) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
            & v1_funct_2(X3,X1,sK3)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
                & ! [X4] :
                    ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                    | ~ m1_subset_1(X4,X1) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(X3,X1,X2)
                & v1_funct_1(X3) )
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(sK2,X2,X3),sK1)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(sK2,X2,X3,X4),sK1)
                  | ~ m1_subset_1(X4,sK2) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X2)))
              & v1_funct_2(X3,sK2,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1)
        | ~ m1_subset_1(X4,sK2) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f26,f35,f34,f33])).

fof(f65,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
        & r2_hidden(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
        & r2_hidden(sK0(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f31])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK0(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f59])).

fof(f63,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,(
    ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f66,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | ~ r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f58])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f75,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f60])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2229,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2231,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4383,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2229,c_2231])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2238,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3258,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2229,c_2238])).

cnf(c_4387,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4383,c_3258])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_34,plain,
    ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4482,plain,
    ( sK3 = k1_xboole_0
    | k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4387,c_34])).

cnf(c_4483,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4482])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_19,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_589,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_590,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_589])).

cnf(c_729,plain,
    ( m1_subset_1(X0,X1)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X2)))
    | ~ v1_relat_1(sK4)
    | sK0(k1_relat_1(sK4),X2,sK4) != X0
    | k1_relat_1(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_590])).

cnf(c_730,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_729])).

cnf(c_2224,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_730])).

cnf(c_35,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_731,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_730])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2303,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2359,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2303])).

cnf(c_2360,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2359])).

cnf(c_3961,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2224,c_35,c_731,c_2360])).

cnf(c_3962,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3961])).

cnf(c_4488,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4483,c_3962])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2241,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_6287,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
    | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4488,c_2241])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_406,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_30])).

cnf(c_407,plain,
    ( ~ v1_funct_2(X0,sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | ~ m1_subset_1(X2,sK2)
    | ~ v1_funct_1(X0)
    | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_523,plain,
    ( ~ v1_funct_2(X0,sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | ~ m1_subset_1(X2,sK2)
    | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_407,c_28])).

cnf(c_524,plain,
    ( ~ v1_funct_2(sK4,sK2,X0)
    | ~ m1_subset_1(X1,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1) ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_2227,plain,
    ( k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1)
    | v1_funct_2(sK4,sK2,X0) != iProver_top
    | m1_subset_1(X1,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_524])).

cnf(c_2500,plain,
    ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2229,c_2227])).

cnf(c_2505,plain,
    ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2500,c_34])).

cnf(c_11670,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | sK3 = k1_xboole_0
    | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6287,c_2505])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2242,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2237,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3173,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2242,c_2237])).

cnf(c_11796,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11670,c_3173])).

cnf(c_24,negated_conjecture,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_97,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_102,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1494,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2298,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
    | k2_relset_1(sK2,sK3,sK4) != X0
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_1494])).

cnf(c_2351,plain,
    ( ~ r1_tarski(X0,sK1)
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
    | k2_relset_1(sK2,sK3,sK4) != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2298])).

cnf(c_2353,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
    | ~ r1_tarski(k1_xboole_0,sK1)
    | k2_relset_1(sK2,sK3,sK4) != k1_xboole_0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2351])).

cnf(c_1492,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2447,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1492])).

cnf(c_2637,plain,
    ( r1_tarski(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1493,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2821,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_1493])).

cnf(c_2822,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2821])).

cnf(c_2964,plain,
    ( ~ r1_tarski(X0,k2_relset_1(sK2,sK3,sK4))
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),X0)
    | k2_relset_1(sK2,sK3,sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2966,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_relset_1(sK2,sK3,sK4))
    | k2_relset_1(sK2,sK3,sK4) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2964])).

cnf(c_3136,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k2_relset_1(sK2,sK3,sK4))
    | k2_relset_1(sK2,sK3,sK4) = k2_relset_1(sK2,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2964])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_4020,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k2_relset_1(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3586,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
    | m1_subset_1(k2_relset_1(X1,sK3,X0),k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_5284,plain,
    ( m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_3586])).

cnf(c_2511,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2789,plain,
    ( ~ m1_subset_1(k2_relset_1(X0,sK3,X1),k1_zfmisc_1(sK3))
    | r1_tarski(k2_relset_1(X0,sK3,X1),sK3) ),
    inference(instantiation,[status(thm)],[c_2511])).

cnf(c_5879,plain,
    ( ~ m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK3))
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_2789])).

cnf(c_4027,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_xboole_0)
    | k2_relset_1(sK2,sK3,sK4) != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1494])).

cnf(c_4830,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),X0)
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_xboole_0)
    | k2_relset_1(sK2,sK3,sK4) != k2_relset_1(sK2,sK3,sK4)
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_4027])).

cnf(c_7381,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK3)
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_xboole_0)
    | k2_relset_1(sK2,sK3,sK4) != k2_relset_1(sK2,sK3,sK4)
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_4830])).

cnf(c_12043,plain,
    ( r1_tarski(k1_xboole_0,k2_relset_1(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_12055,plain,
    ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
    | k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11796,c_26,c_24,c_97,c_102,c_2353,c_2447,c_2637,c_2822,c_2966,c_3136,c_4020,c_5284,c_5879,c_7381,c_12043])).

cnf(c_12056,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4) ),
    inference(renaming,[status(thm)],[c_12055])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1)
    | ~ m1_subset_1(X0,sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_20,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_574,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_28])).

cnf(c_575,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
    | ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_574])).

cnf(c_777,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
    | ~ m1_subset_1(X1,sK2)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)) != k3_funct_2(sK2,sK3,sK4,X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_575])).

cnf(c_778,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),sK1)
    | ~ m1_subset_1(X0,sK2)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
    inference(unflattening,[status(thm)],[c_777])).

cnf(c_1488,plain,
    ( ~ m1_subset_1(X0,sK2)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_778])).

cnf(c_2220,plain,
    ( k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
    | m1_subset_1(X0,sK2) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1488])).

cnf(c_12059,plain,
    ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | m1_subset_1(sK0(sK2,X0,sK4),sK2) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_12056,c_2220])).

cnf(c_6290,plain,
    ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
    | sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4488,c_2237])).

cnf(c_12071,plain,
    ( k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
    | sP2_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12059,c_26,c_24,c_97,c_102,c_2353,c_2447,c_2637,c_2822,c_2966,c_3136,c_4020,c_5284,c_5879,c_6290,c_7381,c_12043])).

cnf(c_12072,plain,
    ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | sP2_iProver_split != iProver_top ),
    inference(renaming,[status(thm)],[c_12071])).

cnf(c_12077,plain,
    ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
    | k1_funct_1(sK4,sK0(sK2,X0,sK4)) != k1_funct_1(sK4,sK0(sK2,sK1,sK4))
    | sK3 = k1_xboole_0
    | sP2_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_4483,c_12072])).

cnf(c_12603,plain,
    ( k1_funct_1(sK4,sK0(sK2,X0,sK4)) != k1_funct_1(sK4,sK0(sK2,sK1,sK4))
    | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
    | sP2_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12077,c_26,c_24,c_97,c_102,c_2353,c_2447,c_2637,c_2822,c_2966,c_3136,c_4020,c_5284,c_5879,c_7381,c_12043])).

cnf(c_12604,plain,
    ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
    | k1_funct_1(sK4,sK0(sK2,X0,sK4)) != k1_funct_1(sK4,sK0(sK2,sK1,sK4))
    | sP2_iProver_split != iProver_top ),
    inference(renaming,[status(thm)],[c_12603])).

cnf(c_12609,plain,
    ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4)
    | sP2_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_12604])).

cnf(c_18,plain,
    ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_604,plain,
    ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_28])).

cnf(c_605,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_604])).

cnf(c_759,plain,
    ( ~ m1_subset_1(X0,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X1)))
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),X1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_605])).

cnf(c_760,plain,
    ( ~ m1_subset_1(X0,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
    inference(unflattening,[status(thm)],[c_759])).

cnf(c_1490,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
    | ~ v1_relat_1(sK4)
    | sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_760])).

cnf(c_2221,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1490])).

cnf(c_1536,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1490])).

cnf(c_2829,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2221,c_35,c_1536,c_2360])).

cnf(c_3175,plain,
    ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4)
    | sP2_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_2829,c_2237])).

cnf(c_16890,plain,
    ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12609,c_3175])).

cnf(c_2239,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_16901,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_16890,c_2239])).

cnf(c_39,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2969,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
    | ~ r1_tarski(k2_relat_1(sK4),sK1)
    | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2351])).

cnf(c_2970,plain,
    ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
    | sK1 != sK1
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) = iProver_top
    | r1_tarski(k2_relat_1(sK4),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2969])).

cnf(c_3174,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2229,c_2237])).

cnf(c_2527,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r1_tarski(sK4,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2869,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),X0)) ),
    inference(instantiation,[status(thm)],[c_2527])).

cnf(c_3249,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
    | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),sK1)) ),
    inference(instantiation,[status(thm)],[c_2869])).

cnf(c_3250,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) != iProver_top
    | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3249])).

cnf(c_3775,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relset_1(X1,X2,X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2239,c_2241])).

cnf(c_7617,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k2_relset_1(X1,X2,X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2242,c_3775])).

cnf(c_16900,plain,
    ( r1_tarski(k2_relat_1(sK4),sK1) = iProver_top
    | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16890,c_7617])).

cnf(c_17068,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16901,c_39,c_2447,c_2970,c_3174,c_3250,c_16900])).

cnf(c_17072,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2242,c_17068])).

cnf(c_17357,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,sK1,sK4)) = k1_funct_1(sK4,sK0(sK2,sK1,sK4))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11670,c_17072])).

cnf(c_17599,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,sK1,sK4)) = k1_funct_1(sK4,sK0(sK2,sK1,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17357,c_26,c_24,c_97,c_102,c_2353,c_2447,c_2637,c_2822,c_2966,c_3136,c_4020,c_5284,c_5879,c_7381,c_12043])).

cnf(c_4509,plain,
    ( k1_funct_1(sK4,sK0(sK2,sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
    | sK3 = k1_xboole_0
    | m1_subset_1(X0,sK2) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_4483,c_2220])).

cnf(c_17601,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_17599,c_4509])).

cnf(c_7621,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
    | r1_tarski(k2_relset_1(k1_relat_1(sK4),X0,sK4),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4488,c_3775])).

cnf(c_17025,plain,
    ( m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
    | r1_tarski(k2_relset_1(k1_relat_1(sK4),X0,sK4),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7621,c_26,c_24,c_97,c_102,c_2353,c_2447,c_2637,c_2822,c_2966,c_3136,c_4020,c_5284,c_5879,c_7381,c_12043])).

cnf(c_17031,plain,
    ( m1_subset_1(sK0(sK2,sK1,sK4),sK2) = iProver_top
    | r1_tarski(k2_relat_1(sK4),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_16890,c_17025])).

cnf(c_7622,plain,
    ( r1_tarski(k2_relset_1(k1_relat_1(sK4),sK1,sK4),sK1) = iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_2829,c_3775])).

cnf(c_16894,plain,
    ( r1_tarski(k2_relat_1(sK4),sK1) = iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_16890,c_7622])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17601,c_17031,c_16894,c_12043,c_7381,c_5879,c_5284,c_4020,c_3174,c_3136,c_2970,c_2966,c_2822,c_2637,c_2447,c_2353,c_102,c_97,c_39,c_24,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:14:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 4.14/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/0.99  
% 4.14/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.14/0.99  
% 4.14/0.99  ------  iProver source info
% 4.14/0.99  
% 4.14/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.14/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.14/0.99  git: non_committed_changes: false
% 4.14/0.99  git: last_make_outside_of_git: false
% 4.14/0.99  
% 4.14/0.99  ------ 
% 4.14/0.99  
% 4.14/0.99  ------ Input Options
% 4.14/0.99  
% 4.14/0.99  --out_options                           all
% 4.14/0.99  --tptp_safe_out                         true
% 4.14/0.99  --problem_path                          ""
% 4.14/0.99  --include_path                          ""
% 4.14/0.99  --clausifier                            res/vclausify_rel
% 4.14/0.99  --clausifier_options                    ""
% 4.14/0.99  --stdin                                 false
% 4.14/0.99  --stats_out                             all
% 4.14/0.99  
% 4.14/0.99  ------ General Options
% 4.14/0.99  
% 4.14/0.99  --fof                                   false
% 4.14/0.99  --time_out_real                         305.
% 4.14/0.99  --time_out_virtual                      -1.
% 4.14/0.99  --symbol_type_check                     false
% 4.14/0.99  --clausify_out                          false
% 4.14/0.99  --sig_cnt_out                           false
% 4.14/0.99  --trig_cnt_out                          false
% 4.14/0.99  --trig_cnt_out_tolerance                1.
% 4.14/0.99  --trig_cnt_out_sk_spl                   false
% 4.14/0.99  --abstr_cl_out                          false
% 4.14/0.99  
% 4.14/0.99  ------ Global Options
% 4.14/0.99  
% 4.14/0.99  --schedule                              default
% 4.14/0.99  --add_important_lit                     false
% 4.14/0.99  --prop_solver_per_cl                    1000
% 4.14/0.99  --min_unsat_core                        false
% 4.14/0.99  --soft_assumptions                      false
% 4.14/0.99  --soft_lemma_size                       3
% 4.14/0.99  --prop_impl_unit_size                   0
% 4.14/0.99  --prop_impl_unit                        []
% 4.14/0.99  --share_sel_clauses                     true
% 4.14/0.99  --reset_solvers                         false
% 4.14/0.99  --bc_imp_inh                            [conj_cone]
% 4.14/0.99  --conj_cone_tolerance                   3.
% 4.14/0.99  --extra_neg_conj                        none
% 4.14/0.99  --large_theory_mode                     true
% 4.14/0.99  --prolific_symb_bound                   200
% 4.14/0.99  --lt_threshold                          2000
% 4.14/0.99  --clause_weak_htbl                      true
% 4.14/0.99  --gc_record_bc_elim                     false
% 4.14/0.99  
% 4.14/0.99  ------ Preprocessing Options
% 4.14/0.99  
% 4.14/0.99  --preprocessing_flag                    true
% 4.14/0.99  --time_out_prep_mult                    0.1
% 4.14/0.99  --splitting_mode                        input
% 4.14/0.99  --splitting_grd                         true
% 4.14/0.99  --splitting_cvd                         false
% 4.14/0.99  --splitting_cvd_svl                     false
% 4.14/0.99  --splitting_nvd                         32
% 4.14/0.99  --sub_typing                            true
% 4.14/0.99  --prep_gs_sim                           true
% 4.14/0.99  --prep_unflatten                        true
% 4.14/0.99  --prep_res_sim                          true
% 4.14/0.99  --prep_upred                            true
% 4.14/0.99  --prep_sem_filter                       exhaustive
% 4.14/0.99  --prep_sem_filter_out                   false
% 4.14/0.99  --pred_elim                             true
% 4.14/0.99  --res_sim_input                         true
% 4.14/0.99  --eq_ax_congr_red                       true
% 4.14/0.99  --pure_diseq_elim                       true
% 4.14/0.99  --brand_transform                       false
% 4.14/0.99  --non_eq_to_eq                          false
% 4.14/0.99  --prep_def_merge                        true
% 4.14/0.99  --prep_def_merge_prop_impl              false
% 4.14/0.99  --prep_def_merge_mbd                    true
% 4.14/0.99  --prep_def_merge_tr_red                 false
% 4.14/0.99  --prep_def_merge_tr_cl                  false
% 4.14/0.99  --smt_preprocessing                     true
% 4.14/0.99  --smt_ac_axioms                         fast
% 4.14/0.99  --preprocessed_out                      false
% 4.14/0.99  --preprocessed_stats                    false
% 4.14/0.99  
% 4.14/0.99  ------ Abstraction refinement Options
% 4.14/0.99  
% 4.14/0.99  --abstr_ref                             []
% 4.14/0.99  --abstr_ref_prep                        false
% 4.14/0.99  --abstr_ref_until_sat                   false
% 4.14/0.99  --abstr_ref_sig_restrict                funpre
% 4.14/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.14/0.99  --abstr_ref_under                       []
% 4.14/0.99  
% 4.14/0.99  ------ SAT Options
% 4.14/0.99  
% 4.14/0.99  --sat_mode                              false
% 4.14/0.99  --sat_fm_restart_options                ""
% 4.14/0.99  --sat_gr_def                            false
% 4.14/0.99  --sat_epr_types                         true
% 4.14/0.99  --sat_non_cyclic_types                  false
% 4.14/0.99  --sat_finite_models                     false
% 4.14/0.99  --sat_fm_lemmas                         false
% 4.14/0.99  --sat_fm_prep                           false
% 4.14/0.99  --sat_fm_uc_incr                        true
% 4.14/0.99  --sat_out_model                         small
% 4.14/0.99  --sat_out_clauses                       false
% 4.14/0.99  
% 4.14/0.99  ------ QBF Options
% 4.14/0.99  
% 4.14/0.99  --qbf_mode                              false
% 4.14/0.99  --qbf_elim_univ                         false
% 4.14/0.99  --qbf_dom_inst                          none
% 4.14/0.99  --qbf_dom_pre_inst                      false
% 4.14/0.99  --qbf_sk_in                             false
% 4.14/0.99  --qbf_pred_elim                         true
% 4.14/0.99  --qbf_split                             512
% 4.14/0.99  
% 4.14/0.99  ------ BMC1 Options
% 4.14/0.99  
% 4.14/0.99  --bmc1_incremental                      false
% 4.14/0.99  --bmc1_axioms                           reachable_all
% 4.14/0.99  --bmc1_min_bound                        0
% 4.14/0.99  --bmc1_max_bound                        -1
% 4.14/0.99  --bmc1_max_bound_default                -1
% 4.14/0.99  --bmc1_symbol_reachability              true
% 4.14/0.99  --bmc1_property_lemmas                  false
% 4.14/0.99  --bmc1_k_induction                      false
% 4.14/0.99  --bmc1_non_equiv_states                 false
% 4.14/0.99  --bmc1_deadlock                         false
% 4.14/0.99  --bmc1_ucm                              false
% 4.14/0.99  --bmc1_add_unsat_core                   none
% 4.14/0.99  --bmc1_unsat_core_children              false
% 4.14/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.14/0.99  --bmc1_out_stat                         full
% 4.14/0.99  --bmc1_ground_init                      false
% 4.14/0.99  --bmc1_pre_inst_next_state              false
% 4.14/0.99  --bmc1_pre_inst_state                   false
% 4.14/0.99  --bmc1_pre_inst_reach_state             false
% 4.14/0.99  --bmc1_out_unsat_core                   false
% 4.14/0.99  --bmc1_aig_witness_out                  false
% 4.14/0.99  --bmc1_verbose                          false
% 4.14/0.99  --bmc1_dump_clauses_tptp                false
% 4.14/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.14/0.99  --bmc1_dump_file                        -
% 4.14/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.14/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.14/0.99  --bmc1_ucm_extend_mode                  1
% 4.14/0.99  --bmc1_ucm_init_mode                    2
% 4.14/0.99  --bmc1_ucm_cone_mode                    none
% 4.14/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.14/0.99  --bmc1_ucm_relax_model                  4
% 4.14/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.14/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.14/0.99  --bmc1_ucm_layered_model                none
% 4.14/0.99  --bmc1_ucm_max_lemma_size               10
% 4.14/0.99  
% 4.14/0.99  ------ AIG Options
% 4.14/0.99  
% 4.14/0.99  --aig_mode                              false
% 4.14/0.99  
% 4.14/0.99  ------ Instantiation Options
% 4.14/0.99  
% 4.14/0.99  --instantiation_flag                    true
% 4.14/0.99  --inst_sos_flag                         true
% 4.14/0.99  --inst_sos_phase                        true
% 4.14/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.14/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.14/0.99  --inst_lit_sel_side                     num_symb
% 4.14/0.99  --inst_solver_per_active                1400
% 4.14/0.99  --inst_solver_calls_frac                1.
% 4.14/0.99  --inst_passive_queue_type               priority_queues
% 4.14/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.14/0.99  --inst_passive_queues_freq              [25;2]
% 4.14/0.99  --inst_dismatching                      true
% 4.14/0.99  --inst_eager_unprocessed_to_passive     true
% 4.14/0.99  --inst_prop_sim_given                   true
% 4.14/0.99  --inst_prop_sim_new                     false
% 4.14/0.99  --inst_subs_new                         false
% 4.14/0.99  --inst_eq_res_simp                      false
% 4.14/0.99  --inst_subs_given                       false
% 4.14/0.99  --inst_orphan_elimination               true
% 4.14/0.99  --inst_learning_loop_flag               true
% 4.14/0.99  --inst_learning_start                   3000
% 4.14/0.99  --inst_learning_factor                  2
% 4.14/0.99  --inst_start_prop_sim_after_learn       3
% 4.14/0.99  --inst_sel_renew                        solver
% 4.14/0.99  --inst_lit_activity_flag                true
% 4.14/0.99  --inst_restr_to_given                   false
% 4.14/0.99  --inst_activity_threshold               500
% 4.14/0.99  --inst_out_proof                        true
% 4.14/0.99  
% 4.14/0.99  ------ Resolution Options
% 4.14/0.99  
% 4.14/0.99  --resolution_flag                       true
% 4.14/0.99  --res_lit_sel                           adaptive
% 4.14/0.99  --res_lit_sel_side                      none
% 4.14/0.99  --res_ordering                          kbo
% 4.14/0.99  --res_to_prop_solver                    active
% 4.14/0.99  --res_prop_simpl_new                    false
% 4.14/0.99  --res_prop_simpl_given                  true
% 4.14/0.99  --res_passive_queue_type                priority_queues
% 4.14/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.14/0.99  --res_passive_queues_freq               [15;5]
% 4.14/0.99  --res_forward_subs                      full
% 4.14/0.99  --res_backward_subs                     full
% 4.14/0.99  --res_forward_subs_resolution           true
% 4.14/0.99  --res_backward_subs_resolution          true
% 4.14/0.99  --res_orphan_elimination                true
% 4.14/0.99  --res_time_limit                        2.
% 4.14/0.99  --res_out_proof                         true
% 4.14/0.99  
% 4.14/0.99  ------ Superposition Options
% 4.14/0.99  
% 4.14/0.99  --superposition_flag                    true
% 4.14/0.99  --sup_passive_queue_type                priority_queues
% 4.14/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.14/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.14/0.99  --demod_completeness_check              fast
% 4.14/0.99  --demod_use_ground                      true
% 4.14/0.99  --sup_to_prop_solver                    passive
% 4.14/0.99  --sup_prop_simpl_new                    true
% 4.14/0.99  --sup_prop_simpl_given                  true
% 4.14/0.99  --sup_fun_splitting                     true
% 4.14/0.99  --sup_smt_interval                      50000
% 4.14/0.99  
% 4.14/0.99  ------ Superposition Simplification Setup
% 4.14/0.99  
% 4.14/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.14/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.14/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.14/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.14/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.14/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.14/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.14/0.99  --sup_immed_triv                        [TrivRules]
% 4.14/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.14/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.14/0.99  --sup_immed_bw_main                     []
% 4.14/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.14/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.14/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.14/0.99  --sup_input_bw                          []
% 4.14/0.99  
% 4.14/0.99  ------ Combination Options
% 4.14/0.99  
% 4.14/0.99  --comb_res_mult                         3
% 4.14/0.99  --comb_sup_mult                         2
% 4.14/0.99  --comb_inst_mult                        10
% 4.14/0.99  
% 4.14/0.99  ------ Debug Options
% 4.14/0.99  
% 4.14/0.99  --dbg_backtrace                         false
% 4.14/0.99  --dbg_dump_prop_clauses                 false
% 4.14/0.99  --dbg_dump_prop_clauses_file            -
% 4.14/0.99  --dbg_out_stat                          false
% 4.14/0.99  ------ Parsing...
% 4.14/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.14/0.99  
% 4.14/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 4.14/0.99  
% 4.14/0.99  ------ Preprocessing... gs_s  sp: 6 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.14/0.99  
% 4.14/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.14/0.99  ------ Proving...
% 4.14/0.99  ------ Problem Properties 
% 4.14/0.99  
% 4.14/0.99  
% 4.14/0.99  clauses                                 35
% 4.14/0.99  conjectures                             3
% 4.14/0.99  EPR                                     4
% 4.14/0.99  Horn                                    23
% 4.14/0.99  unary                                   5
% 4.14/0.99  binary                                  7
% 4.14/0.99  lits                                    93
% 4.14/0.99  lits eq                                 20
% 4.14/0.99  fd_pure                                 0
% 4.14/0.99  fd_pseudo                               0
% 4.14/0.99  fd_cond                                 3
% 4.14/0.99  fd_pseudo_cond                          1
% 4.14/0.99  AC symbols                              0
% 4.14/0.99  
% 4.14/0.99  ------ Schedule dynamic 5 is on 
% 4.14/0.99  
% 4.14/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.14/0.99  
% 4.14/0.99  
% 4.14/0.99  ------ 
% 4.14/0.99  Current options:
% 4.14/0.99  ------ 
% 4.14/0.99  
% 4.14/0.99  ------ Input Options
% 4.14/0.99  
% 4.14/0.99  --out_options                           all
% 4.14/0.99  --tptp_safe_out                         true
% 4.14/0.99  --problem_path                          ""
% 4.14/0.99  --include_path                          ""
% 4.14/0.99  --clausifier                            res/vclausify_rel
% 4.14/0.99  --clausifier_options                    ""
% 4.14/0.99  --stdin                                 false
% 4.14/0.99  --stats_out                             all
% 4.14/0.99  
% 4.14/0.99  ------ General Options
% 4.14/0.99  
% 4.14/0.99  --fof                                   false
% 4.14/0.99  --time_out_real                         305.
% 4.14/0.99  --time_out_virtual                      -1.
% 4.14/0.99  --symbol_type_check                     false
% 4.14/0.99  --clausify_out                          false
% 4.14/0.99  --sig_cnt_out                           false
% 4.14/0.99  --trig_cnt_out                          false
% 4.14/0.99  --trig_cnt_out_tolerance                1.
% 4.14/0.99  --trig_cnt_out_sk_spl                   false
% 4.14/0.99  --abstr_cl_out                          false
% 4.14/0.99  
% 4.14/0.99  ------ Global Options
% 4.14/0.99  
% 4.14/0.99  --schedule                              default
% 4.14/0.99  --add_important_lit                     false
% 4.14/0.99  --prop_solver_per_cl                    1000
% 4.14/0.99  --min_unsat_core                        false
% 4.14/0.99  --soft_assumptions                      false
% 4.14/0.99  --soft_lemma_size                       3
% 4.14/0.99  --prop_impl_unit_size                   0
% 4.14/0.99  --prop_impl_unit                        []
% 4.14/0.99  --share_sel_clauses                     true
% 4.14/0.99  --reset_solvers                         false
% 4.14/0.99  --bc_imp_inh                            [conj_cone]
% 4.14/0.99  --conj_cone_tolerance                   3.
% 4.14/0.99  --extra_neg_conj                        none
% 4.14/0.99  --large_theory_mode                     true
% 4.14/0.99  --prolific_symb_bound                   200
% 4.14/0.99  --lt_threshold                          2000
% 4.14/0.99  --clause_weak_htbl                      true
% 4.14/0.99  --gc_record_bc_elim                     false
% 4.14/0.99  
% 4.14/0.99  ------ Preprocessing Options
% 4.14/0.99  
% 4.14/0.99  --preprocessing_flag                    true
% 4.14/0.99  --time_out_prep_mult                    0.1
% 4.14/0.99  --splitting_mode                        input
% 4.14/0.99  --splitting_grd                         true
% 4.14/0.99  --splitting_cvd                         false
% 4.14/0.99  --splitting_cvd_svl                     false
% 4.14/0.99  --splitting_nvd                         32
% 4.14/0.99  --sub_typing                            true
% 4.14/0.99  --prep_gs_sim                           true
% 4.14/0.99  --prep_unflatten                        true
% 4.14/0.99  --prep_res_sim                          true
% 4.14/0.99  --prep_upred                            true
% 4.14/0.99  --prep_sem_filter                       exhaustive
% 4.14/0.99  --prep_sem_filter_out                   false
% 4.14/0.99  --pred_elim                             true
% 4.14/0.99  --res_sim_input                         true
% 4.14/0.99  --eq_ax_congr_red                       true
% 4.14/0.99  --pure_diseq_elim                       true
% 4.14/0.99  --brand_transform                       false
% 4.14/0.99  --non_eq_to_eq                          false
% 4.14/0.99  --prep_def_merge                        true
% 4.14/0.99  --prep_def_merge_prop_impl              false
% 4.14/0.99  --prep_def_merge_mbd                    true
% 4.14/0.99  --prep_def_merge_tr_red                 false
% 4.14/0.99  --prep_def_merge_tr_cl                  false
% 4.14/0.99  --smt_preprocessing                     true
% 4.14/0.99  --smt_ac_axioms                         fast
% 4.14/0.99  --preprocessed_out                      false
% 4.14/0.99  --preprocessed_stats                    false
% 4.14/0.99  
% 4.14/0.99  ------ Abstraction refinement Options
% 4.14/0.99  
% 4.14/0.99  --abstr_ref                             []
% 4.14/0.99  --abstr_ref_prep                        false
% 4.14/0.99  --abstr_ref_until_sat                   false
% 4.14/0.99  --abstr_ref_sig_restrict                funpre
% 4.14/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.14/0.99  --abstr_ref_under                       []
% 4.14/0.99  
% 4.14/0.99  ------ SAT Options
% 4.14/0.99  
% 4.14/0.99  --sat_mode                              false
% 4.14/0.99  --sat_fm_restart_options                ""
% 4.14/0.99  --sat_gr_def                            false
% 4.14/0.99  --sat_epr_types                         true
% 4.14/0.99  --sat_non_cyclic_types                  false
% 4.14/0.99  --sat_finite_models                     false
% 4.14/0.99  --sat_fm_lemmas                         false
% 4.14/0.99  --sat_fm_prep                           false
% 4.14/0.99  --sat_fm_uc_incr                        true
% 4.14/0.99  --sat_out_model                         small
% 4.14/0.99  --sat_out_clauses                       false
% 4.14/0.99  
% 4.14/0.99  ------ QBF Options
% 4.14/0.99  
% 4.14/0.99  --qbf_mode                              false
% 4.14/0.99  --qbf_elim_univ                         false
% 4.14/0.99  --qbf_dom_inst                          none
% 4.14/0.99  --qbf_dom_pre_inst                      false
% 4.14/0.99  --qbf_sk_in                             false
% 4.14/0.99  --qbf_pred_elim                         true
% 4.14/0.99  --qbf_split                             512
% 4.14/0.99  
% 4.14/0.99  ------ BMC1 Options
% 4.14/0.99  
% 4.14/0.99  --bmc1_incremental                      false
% 4.14/0.99  --bmc1_axioms                           reachable_all
% 4.14/0.99  --bmc1_min_bound                        0
% 4.14/0.99  --bmc1_max_bound                        -1
% 4.14/0.99  --bmc1_max_bound_default                -1
% 4.14/0.99  --bmc1_symbol_reachability              true
% 4.14/0.99  --bmc1_property_lemmas                  false
% 4.14/0.99  --bmc1_k_induction                      false
% 4.14/0.99  --bmc1_non_equiv_states                 false
% 4.14/0.99  --bmc1_deadlock                         false
% 4.14/0.99  --bmc1_ucm                              false
% 4.14/0.99  --bmc1_add_unsat_core                   none
% 4.14/0.99  --bmc1_unsat_core_children              false
% 4.14/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.14/0.99  --bmc1_out_stat                         full
% 4.14/0.99  --bmc1_ground_init                      false
% 4.14/0.99  --bmc1_pre_inst_next_state              false
% 4.14/0.99  --bmc1_pre_inst_state                   false
% 4.14/0.99  --bmc1_pre_inst_reach_state             false
% 4.14/0.99  --bmc1_out_unsat_core                   false
% 4.14/0.99  --bmc1_aig_witness_out                  false
% 4.14/0.99  --bmc1_verbose                          false
% 4.14/0.99  --bmc1_dump_clauses_tptp                false
% 4.14/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.14/0.99  --bmc1_dump_file                        -
% 4.14/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.14/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.14/0.99  --bmc1_ucm_extend_mode                  1
% 4.14/0.99  --bmc1_ucm_init_mode                    2
% 4.14/0.99  --bmc1_ucm_cone_mode                    none
% 4.14/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.14/0.99  --bmc1_ucm_relax_model                  4
% 4.14/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.14/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.14/0.99  --bmc1_ucm_layered_model                none
% 4.14/0.99  --bmc1_ucm_max_lemma_size               10
% 4.14/0.99  
% 4.14/0.99  ------ AIG Options
% 4.14/0.99  
% 4.14/0.99  --aig_mode                              false
% 4.14/0.99  
% 4.14/0.99  ------ Instantiation Options
% 4.14/0.99  
% 4.14/0.99  --instantiation_flag                    true
% 4.14/0.99  --inst_sos_flag                         true
% 4.14/0.99  --inst_sos_phase                        true
% 4.14/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.14/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.14/0.99  --inst_lit_sel_side                     none
% 4.14/0.99  --inst_solver_per_active                1400
% 4.14/0.99  --inst_solver_calls_frac                1.
% 4.14/0.99  --inst_passive_queue_type               priority_queues
% 4.14/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.14/0.99  --inst_passive_queues_freq              [25;2]
% 4.14/0.99  --inst_dismatching                      true
% 4.14/0.99  --inst_eager_unprocessed_to_passive     true
% 4.14/0.99  --inst_prop_sim_given                   true
% 4.14/0.99  --inst_prop_sim_new                     false
% 4.14/0.99  --inst_subs_new                         false
% 4.14/0.99  --inst_eq_res_simp                      false
% 4.14/0.99  --inst_subs_given                       false
% 4.14/0.99  --inst_orphan_elimination               true
% 4.14/0.99  --inst_learning_loop_flag               true
% 4.14/0.99  --inst_learning_start                   3000
% 4.14/0.99  --inst_learning_factor                  2
% 4.14/0.99  --inst_start_prop_sim_after_learn       3
% 4.14/0.99  --inst_sel_renew                        solver
% 4.14/0.99  --inst_lit_activity_flag                true
% 4.14/0.99  --inst_restr_to_given                   false
% 4.14/0.99  --inst_activity_threshold               500
% 4.14/0.99  --inst_out_proof                        true
% 4.14/0.99  
% 4.14/0.99  ------ Resolution Options
% 4.14/0.99  
% 4.14/0.99  --resolution_flag                       false
% 4.14/0.99  --res_lit_sel                           adaptive
% 4.14/0.99  --res_lit_sel_side                      none
% 4.14/0.99  --res_ordering                          kbo
% 4.14/0.99  --res_to_prop_solver                    active
% 4.14/0.99  --res_prop_simpl_new                    false
% 4.14/0.99  --res_prop_simpl_given                  true
% 4.14/0.99  --res_passive_queue_type                priority_queues
% 4.14/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.14/0.99  --res_passive_queues_freq               [15;5]
% 4.14/0.99  --res_forward_subs                      full
% 4.14/0.99  --res_backward_subs                     full
% 4.14/0.99  --res_forward_subs_resolution           true
% 4.14/0.99  --res_backward_subs_resolution          true
% 4.14/0.99  --res_orphan_elimination                true
% 4.14/0.99  --res_time_limit                        2.
% 4.14/0.99  --res_out_proof                         true
% 4.14/0.99  
% 4.14/0.99  ------ Superposition Options
% 4.14/0.99  
% 4.14/0.99  --superposition_flag                    true
% 4.14/0.99  --sup_passive_queue_type                priority_queues
% 4.14/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.14/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.14/0.99  --demod_completeness_check              fast
% 4.14/0.99  --demod_use_ground                      true
% 4.14/0.99  --sup_to_prop_solver                    passive
% 4.14/0.99  --sup_prop_simpl_new                    true
% 4.14/0.99  --sup_prop_simpl_given                  true
% 4.14/0.99  --sup_fun_splitting                     true
% 4.14/0.99  --sup_smt_interval                      50000
% 4.14/0.99  
% 4.14/0.99  ------ Superposition Simplification Setup
% 4.14/0.99  
% 4.14/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.14/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.14/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.14/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.14/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.14/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.14/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.14/0.99  --sup_immed_triv                        [TrivRules]
% 4.14/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.14/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.14/0.99  --sup_immed_bw_main                     []
% 4.14/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.14/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.14/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.14/0.99  --sup_input_bw                          []
% 4.14/0.99  
% 4.14/0.99  ------ Combination Options
% 4.14/0.99  
% 4.14/0.99  --comb_res_mult                         3
% 4.14/0.99  --comb_sup_mult                         2
% 4.14/0.99  --comb_inst_mult                        10
% 4.14/0.99  
% 4.14/0.99  ------ Debug Options
% 4.14/0.99  
% 4.14/0.99  --dbg_backtrace                         false
% 4.14/0.99  --dbg_dump_prop_clauses                 false
% 4.14/0.99  --dbg_dump_prop_clauses_file            -
% 4.14/0.99  --dbg_out_stat                          false
% 4.14/0.99  
% 4.14/0.99  
% 4.14/0.99  
% 4.14/0.99  
% 4.14/0.99  ------ Proving...
% 4.14/0.99  
% 4.14/0.99  
% 4.14/0.99  % SZS status Theorem for theBenchmark.p
% 4.14/0.99  
% 4.14/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 4.14/0.99  
% 4.14/0.99  fof(f12,conjecture,(
% 4.14/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 4.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.14/0.99  
% 4.14/0.99  fof(f13,negated_conjecture,(
% 4.14/0.99    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 4.14/0.99    inference(negated_conjecture,[],[f12])).
% 4.14/0.99  
% 4.14/0.99  fof(f25,plain,(
% 4.14/0.99    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 4.14/0.99    inference(ennf_transformation,[],[f13])).
% 4.14/0.99  
% 4.14/0.99  fof(f26,plain,(
% 4.14/0.99    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 4.14/0.99    inference(flattening,[],[f25])).
% 4.14/0.99  
% 4.14/0.99  fof(f35,plain,(
% 4.14/0.99    ( ! [X2,X0,X1] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (~r1_tarski(k2_relset_1(X1,X2,sK4),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,sK4,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 4.14/0.99    introduced(choice_axiom,[])).
% 4.14/0.99  
% 4.14/0.99  fof(f34,plain,(
% 4.14/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (~r1_tarski(k2_relset_1(X1,sK3,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,sK3,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK3))) & v1_funct_2(X3,X1,sK3) & v1_funct_1(X3)) & ~v1_xboole_0(sK3))) )),
% 4.14/0.99    introduced(choice_axiom,[])).
% 4.14/0.99  
% 4.14/0.99  fof(f33,plain,(
% 4.14/0.99    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK2,X2,X3),sK1) & ! [X4] : (r2_hidden(k3_funct_2(sK2,X2,X3,X4),sK1) | ~m1_subset_1(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X2))) & v1_funct_2(X3,sK2,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK2))),
% 4.14/0.99    introduced(choice_axiom,[])).
% 4.14/0.99  
% 4.14/0.99  fof(f36,plain,(
% 4.14/0.99    ((~r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) & ! [X4] : (r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1) | ~m1_subset_1(X4,sK2)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 4.14/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f26,f35,f34,f33])).
% 4.14/0.99  
% 4.14/0.99  fof(f65,plain,(
% 4.14/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 4.14/0.99    inference(cnf_transformation,[],[f36])).
% 4.14/0.99  
% 4.14/0.99  fof(f9,axiom,(
% 4.14/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 4.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.14/0.99  
% 4.14/0.99  fof(f19,plain,(
% 4.14/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.14/0.99    inference(ennf_transformation,[],[f9])).
% 4.14/0.99  
% 4.14/0.99  fof(f20,plain,(
% 4.14/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.14/0.99    inference(flattening,[],[f19])).
% 4.14/0.99  
% 4.14/0.99  fof(f30,plain,(
% 4.14/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.14/0.99    inference(nnf_transformation,[],[f20])).
% 4.14/0.99  
% 4.14/0.99  fof(f48,plain,(
% 4.14/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.14/0.99    inference(cnf_transformation,[],[f30])).
% 4.14/0.99  
% 4.14/0.99  fof(f7,axiom,(
% 4.14/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 4.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.14/0.99  
% 4.14/0.99  fof(f17,plain,(
% 4.14/0.99    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.14/0.99    inference(ennf_transformation,[],[f7])).
% 4.14/0.99  
% 4.14/0.99  fof(f46,plain,(
% 4.14/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.14/0.99    inference(cnf_transformation,[],[f17])).
% 4.14/0.99  
% 4.14/0.99  fof(f64,plain,(
% 4.14/0.99    v1_funct_2(sK4,sK2,sK3)),
% 4.14/0.99    inference(cnf_transformation,[],[f36])).
% 4.14/0.99  
% 4.14/0.99  fof(f3,axiom,(
% 4.14/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 4.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.14/0.99  
% 4.14/0.99  fof(f14,plain,(
% 4.14/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 4.14/0.99    inference(ennf_transformation,[],[f3])).
% 4.14/0.99  
% 4.14/0.99  fof(f41,plain,(
% 4.14/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 4.14/0.99    inference(cnf_transformation,[],[f14])).
% 4.14/0.99  
% 4.14/0.99  fof(f11,axiom,(
% 4.14/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 4.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.14/0.99  
% 4.14/0.99  fof(f23,plain,(
% 4.14/0.99    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 4.14/0.99    inference(ennf_transformation,[],[f11])).
% 4.14/0.99  
% 4.14/0.99  fof(f24,plain,(
% 4.14/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.14/0.99    inference(flattening,[],[f23])).
% 4.14/0.99  
% 4.14/0.99  fof(f31,plain,(
% 4.14/0.99    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),X0)))),
% 4.14/0.99    introduced(choice_axiom,[])).
% 4.14/0.99  
% 4.14/0.99  fof(f32,plain,(
% 4.14/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.14/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f31])).
% 4.14/0.99  
% 4.14/0.99  fof(f59,plain,(
% 4.14/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK0(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 4.14/0.99    inference(cnf_transformation,[],[f32])).
% 4.14/0.99  
% 4.14/0.99  fof(f76,plain,(
% 4.14/0.99    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 4.14/0.99    inference(equality_resolution,[],[f59])).
% 4.14/0.99  
% 4.14/0.99  fof(f63,plain,(
% 4.14/0.99    v1_funct_1(sK4)),
% 4.14/0.99    inference(cnf_transformation,[],[f36])).
% 4.14/0.99  
% 4.14/0.99  fof(f5,axiom,(
% 4.14/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 4.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.14/0.99  
% 4.14/0.99  fof(f15,plain,(
% 4.14/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.14/0.99    inference(ennf_transformation,[],[f5])).
% 4.14/0.99  
% 4.14/0.99  fof(f44,plain,(
% 4.14/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.14/0.99    inference(cnf_transformation,[],[f15])).
% 4.14/0.99  
% 4.14/0.99  fof(f4,axiom,(
% 4.14/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.14/0.99  
% 4.14/0.99  fof(f29,plain,(
% 4.14/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 4.14/0.99    inference(nnf_transformation,[],[f4])).
% 4.14/0.99  
% 4.14/0.99  fof(f42,plain,(
% 4.14/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 4.14/0.99    inference(cnf_transformation,[],[f29])).
% 4.14/0.99  
% 4.14/0.99  fof(f10,axiom,(
% 4.14/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 4.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.14/0.99  
% 4.14/0.99  fof(f21,plain,(
% 4.14/0.99    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 4.14/0.99    inference(ennf_transformation,[],[f10])).
% 4.14/0.99  
% 4.14/0.99  fof(f22,plain,(
% 4.14/0.99    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 4.14/0.99    inference(flattening,[],[f21])).
% 4.14/0.99  
% 4.14/0.99  fof(f54,plain,(
% 4.14/0.99    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 4.14/0.99    inference(cnf_transformation,[],[f22])).
% 4.14/0.99  
% 4.14/0.99  fof(f61,plain,(
% 4.14/0.99    ~v1_xboole_0(sK2)),
% 4.14/0.99    inference(cnf_transformation,[],[f36])).
% 4.14/0.99  
% 4.14/0.99  fof(f43,plain,(
% 4.14/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 4.14/0.99    inference(cnf_transformation,[],[f29])).
% 4.14/0.99  
% 4.14/0.99  fof(f8,axiom,(
% 4.14/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 4.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.14/0.99  
% 4.14/0.99  fof(f18,plain,(
% 4.14/0.99    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.14/0.99    inference(ennf_transformation,[],[f8])).
% 4.14/0.99  
% 4.14/0.99  fof(f47,plain,(
% 4.14/0.99    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.14/0.99    inference(cnf_transformation,[],[f18])).
% 4.14/0.99  
% 4.14/0.99  fof(f67,plain,(
% 4.14/0.99    ~r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)),
% 4.14/0.99    inference(cnf_transformation,[],[f36])).
% 4.14/0.99  
% 4.14/0.99  fof(f2,axiom,(
% 4.14/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 4.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.14/0.99  
% 4.14/0.99  fof(f40,plain,(
% 4.14/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 4.14/0.99    inference(cnf_transformation,[],[f2])).
% 4.14/0.99  
% 4.14/0.99  fof(f1,axiom,(
% 4.14/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.14/0.99  
% 4.14/0.99  fof(f27,plain,(
% 4.14/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.14/0.99    inference(nnf_transformation,[],[f1])).
% 4.14/0.99  
% 4.14/0.99  fof(f28,plain,(
% 4.14/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.14/0.99    inference(flattening,[],[f27])).
% 4.14/0.99  
% 4.14/0.99  fof(f39,plain,(
% 4.14/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.14/0.99    inference(cnf_transformation,[],[f28])).
% 4.14/0.99  
% 4.14/0.99  fof(f37,plain,(
% 4.14/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 4.14/0.99    inference(cnf_transformation,[],[f28])).
% 4.14/0.99  
% 4.14/0.99  fof(f69,plain,(
% 4.14/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.14/0.99    inference(equality_resolution,[],[f37])).
% 4.14/0.99  
% 4.14/0.99  fof(f6,axiom,(
% 4.14/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 4.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.14/0.99  
% 4.14/0.99  fof(f16,plain,(
% 4.14/0.99    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.14/0.99    inference(ennf_transformation,[],[f6])).
% 4.14/0.99  
% 4.14/0.99  fof(f45,plain,(
% 4.14/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.14/0.99    inference(cnf_transformation,[],[f16])).
% 4.14/0.99  
% 4.14/0.99  fof(f66,plain,(
% 4.14/0.99    ( ! [X4] : (r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1) | ~m1_subset_1(X4,sK2)) )),
% 4.14/0.99    inference(cnf_transformation,[],[f36])).
% 4.14/0.99  
% 4.14/0.99  fof(f58,plain,(
% 4.14/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 4.14/0.99    inference(cnf_transformation,[],[f32])).
% 4.14/0.99  
% 4.14/0.99  fof(f77,plain,(
% 4.14/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | ~r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 4.14/0.99    inference(equality_resolution,[],[f58])).
% 4.14/0.99  
% 4.14/0.99  fof(f60,plain,(
% 4.14/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 4.14/0.99    inference(cnf_transformation,[],[f32])).
% 4.14/0.99  
% 4.14/0.99  fof(f75,plain,(
% 4.14/0.99    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 4.14/0.99    inference(equality_resolution,[],[f60])).
% 4.14/0.99  
% 4.14/0.99  cnf(c_26,negated_conjecture,
% 4.14/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 4.14/0.99      inference(cnf_transformation,[],[f65]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2229,plain,
% 4.14/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 4.14/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_16,plain,
% 4.14/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 4.14/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.14/0.99      | k1_relset_1(X1,X2,X0) = X1
% 4.14/0.99      | k1_xboole_0 = X2 ),
% 4.14/0.99      inference(cnf_transformation,[],[f48]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2231,plain,
% 4.14/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 4.14/0.99      | k1_xboole_0 = X1
% 4.14/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 4.14/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.14/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_4383,plain,
% 4.14/0.99      ( k1_relset_1(sK2,sK3,sK4) = sK2
% 4.14/0.99      | sK3 = k1_xboole_0
% 4.14/0.99      | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
% 4.14/0.99      inference(superposition,[status(thm)],[c_2229,c_2231]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_9,plain,
% 4.14/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.14/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 4.14/0.99      inference(cnf_transformation,[],[f46]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2238,plain,
% 4.14/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 4.14/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.14/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_3258,plain,
% 4.14/0.99      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 4.14/0.99      inference(superposition,[status(thm)],[c_2229,c_2238]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_4387,plain,
% 4.14/0.99      ( k1_relat_1(sK4) = sK2
% 4.14/0.99      | sK3 = k1_xboole_0
% 4.14/0.99      | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
% 4.14/0.99      inference(demodulation,[status(thm)],[c_4383,c_3258]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_27,negated_conjecture,
% 4.14/0.99      ( v1_funct_2(sK4,sK2,sK3) ),
% 4.14/0.99      inference(cnf_transformation,[],[f64]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_34,plain,
% 4.14/0.99      ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
% 4.14/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_4482,plain,
% 4.14/0.99      ( sK3 = k1_xboole_0 | k1_relat_1(sK4) = sK2 ),
% 4.14/0.99      inference(global_propositional_subsumption,
% 4.14/0.99                [status(thm)],
% 4.14/0.99                [c_4387,c_34]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_4483,plain,
% 4.14/0.99      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 4.14/0.99      inference(renaming,[status(thm)],[c_4482]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_4,plain,
% 4.14/0.99      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 4.14/0.99      inference(cnf_transformation,[],[f41]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_19,plain,
% 4.14/0.99      ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 4.14/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 4.14/0.99      | ~ v1_funct_1(X0)
% 4.14/0.99      | ~ v1_relat_1(X0) ),
% 4.14/0.99      inference(cnf_transformation,[],[f76]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_28,negated_conjecture,
% 4.14/0.99      ( v1_funct_1(sK4) ),
% 4.14/0.99      inference(cnf_transformation,[],[f63]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_589,plain,
% 4.14/0.99      ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 4.14/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 4.14/0.99      | ~ v1_relat_1(X0)
% 4.14/0.99      | sK4 != X0 ),
% 4.14/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_590,plain,
% 4.14/0.99      ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
% 4.14/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 4.14/0.99      | ~ v1_relat_1(sK4) ),
% 4.14/0.99      inference(unflattening,[status(thm)],[c_589]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_729,plain,
% 4.14/0.99      ( m1_subset_1(X0,X1)
% 4.14/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X2)))
% 4.14/0.99      | ~ v1_relat_1(sK4)
% 4.14/0.99      | sK0(k1_relat_1(sK4),X2,sK4) != X0
% 4.14/0.99      | k1_relat_1(sK4) != X1 ),
% 4.14/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_590]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_730,plain,
% 4.14/0.99      ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
% 4.14/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 4.14/0.99      | ~ v1_relat_1(sK4) ),
% 4.14/0.99      inference(unflattening,[status(thm)],[c_729]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2224,plain,
% 4.14/0.99      ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 4.14/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 4.14/0.99      | v1_relat_1(sK4) != iProver_top ),
% 4.14/0.99      inference(predicate_to_equality,[status(thm)],[c_730]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_35,plain,
% 4.14/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 4.14/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_731,plain,
% 4.14/0.99      ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 4.14/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 4.14/0.99      | v1_relat_1(sK4) != iProver_top ),
% 4.14/0.99      inference(predicate_to_equality,[status(thm)],[c_730]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_7,plain,
% 4.14/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.14/0.99      | v1_relat_1(X0) ),
% 4.14/0.99      inference(cnf_transformation,[],[f44]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2303,plain,
% 4.14/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.14/0.99      | v1_relat_1(sK4) ),
% 4.14/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2359,plain,
% 4.14/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 4.14/0.99      | v1_relat_1(sK4) ),
% 4.14/0.99      inference(instantiation,[status(thm)],[c_2303]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2360,plain,
% 4.14/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 4.14/0.99      | v1_relat_1(sK4) = iProver_top ),
% 4.14/0.99      inference(predicate_to_equality,[status(thm)],[c_2359]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_3961,plain,
% 4.14/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 4.14/0.99      | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top ),
% 4.14/0.99      inference(global_propositional_subsumption,
% 4.14/0.99                [status(thm)],
% 4.14/0.99                [c_2224,c_35,c_731,c_2360]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_3962,plain,
% 4.14/0.99      ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 4.14/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
% 4.14/0.99      inference(renaming,[status(thm)],[c_3961]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_4488,plain,
% 4.14/0.99      ( sK3 = k1_xboole_0
% 4.14/0.99      | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
% 4.14/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
% 4.14/0.99      inference(superposition,[status(thm)],[c_4483,c_3962]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_6,plain,
% 4.14/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 4.14/0.99      inference(cnf_transformation,[],[f42]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2241,plain,
% 4.14/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.14/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 4.14/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_6287,plain,
% 4.14/0.99      ( sK3 = k1_xboole_0
% 4.14/0.99      | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
% 4.14/0.99      | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),X0)) = iProver_top ),
% 4.14/0.99      inference(superposition,[status(thm)],[c_4488,c_2241]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_17,plain,
% 4.14/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 4.14/0.99      | ~ m1_subset_1(X3,X1)
% 4.14/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.14/0.99      | v1_xboole_0(X1)
% 4.14/0.99      | ~ v1_funct_1(X0)
% 4.14/0.99      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 4.14/0.99      inference(cnf_transformation,[],[f54]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_30,negated_conjecture,
% 4.14/0.99      ( ~ v1_xboole_0(sK2) ),
% 4.14/0.99      inference(cnf_transformation,[],[f61]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_406,plain,
% 4.14/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 4.14/0.99      | ~ m1_subset_1(X3,X1)
% 4.14/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.14/0.99      | ~ v1_funct_1(X0)
% 4.14/0.99      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
% 4.14/0.99      | sK2 != X1 ),
% 4.14/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_30]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_407,plain,
% 4.14/0.99      ( ~ v1_funct_2(X0,sK2,X1)
% 4.14/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
% 4.14/0.99      | ~ m1_subset_1(X2,sK2)
% 4.14/0.99      | ~ v1_funct_1(X0)
% 4.14/0.99      | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2) ),
% 4.14/0.99      inference(unflattening,[status(thm)],[c_406]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_523,plain,
% 4.14/0.99      ( ~ v1_funct_2(X0,sK2,X1)
% 4.14/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
% 4.14/0.99      | ~ m1_subset_1(X2,sK2)
% 4.14/0.99      | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2)
% 4.14/0.99      | sK4 != X0 ),
% 4.14/0.99      inference(resolution_lifted,[status(thm)],[c_407,c_28]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_524,plain,
% 4.14/0.99      ( ~ v1_funct_2(sK4,sK2,X0)
% 4.14/0.99      | ~ m1_subset_1(X1,sK2)
% 4.14/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 4.14/0.99      | k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1) ),
% 4.14/0.99      inference(unflattening,[status(thm)],[c_523]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2227,plain,
% 4.14/0.99      ( k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1)
% 4.14/0.99      | v1_funct_2(sK4,sK2,X0) != iProver_top
% 4.14/0.99      | m1_subset_1(X1,sK2) != iProver_top
% 4.14/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
% 4.14/0.99      inference(predicate_to_equality,[status(thm)],[c_524]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2500,plain,
% 4.14/0.99      ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
% 4.14/0.99      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 4.14/0.99      | m1_subset_1(X0,sK2) != iProver_top ),
% 4.14/0.99      inference(superposition,[status(thm)],[c_2229,c_2227]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2505,plain,
% 4.14/0.99      ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
% 4.14/0.99      | m1_subset_1(X0,sK2) != iProver_top ),
% 4.14/0.99      inference(global_propositional_subsumption,
% 4.14/0.99                [status(thm)],
% 4.14/0.99                [c_2500,c_34]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_11670,plain,
% 4.14/0.99      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 4.14/0.99      | sK3 = k1_xboole_0
% 4.14/0.99      | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),X0)) = iProver_top ),
% 4.14/0.99      inference(superposition,[status(thm)],[c_6287,c_2505]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_5,plain,
% 4.14/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 4.14/0.99      inference(cnf_transformation,[],[f43]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2242,plain,
% 4.14/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 4.14/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 4.14/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_10,plain,
% 4.14/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.14/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 4.14/0.99      inference(cnf_transformation,[],[f47]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2237,plain,
% 4.14/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 4.14/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.14/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_3173,plain,
% 4.14/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 4.14/0.99      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 4.14/0.99      inference(superposition,[status(thm)],[c_2242,c_2237]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_11796,plain,
% 4.14/0.99      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 4.14/0.99      | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
% 4.14/0.99      | sK3 = k1_xboole_0 ),
% 4.14/0.99      inference(superposition,[status(thm)],[c_11670,c_3173]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_24,negated_conjecture,
% 4.14/0.99      ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
% 4.14/0.99      inference(cnf_transformation,[],[f67]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_3,plain,
% 4.14/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 4.14/0.99      inference(cnf_transformation,[],[f40]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_97,plain,
% 4.14/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 4.14/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_0,plain,
% 4.14/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 4.14/0.99      inference(cnf_transformation,[],[f39]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_102,plain,
% 4.14/0.99      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 4.14/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 4.14/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_1494,plain,
% 4.14/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 4.14/0.99      theory(equality) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2298,plain,
% 4.14/0.99      ( ~ r1_tarski(X0,X1)
% 4.14/0.99      | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
% 4.14/0.99      | k2_relset_1(sK2,sK3,sK4) != X0
% 4.14/0.99      | sK1 != X1 ),
% 4.14/0.99      inference(instantiation,[status(thm)],[c_1494]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2351,plain,
% 4.14/0.99      ( ~ r1_tarski(X0,sK1)
% 4.14/0.99      | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
% 4.14/0.99      | k2_relset_1(sK2,sK3,sK4) != X0
% 4.14/0.99      | sK1 != sK1 ),
% 4.14/0.99      inference(instantiation,[status(thm)],[c_2298]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2353,plain,
% 4.14/0.99      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
% 4.14/0.99      | ~ r1_tarski(k1_xboole_0,sK1)
% 4.14/0.99      | k2_relset_1(sK2,sK3,sK4) != k1_xboole_0
% 4.14/0.99      | sK1 != sK1 ),
% 4.14/0.99      inference(instantiation,[status(thm)],[c_2351]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_1492,plain,( X0 = X0 ),theory(equality) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2447,plain,
% 4.14/0.99      ( sK1 = sK1 ),
% 4.14/0.99      inference(instantiation,[status(thm)],[c_1492]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2637,plain,
% 4.14/0.99      ( r1_tarski(k1_xboole_0,sK1) ),
% 4.14/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_1493,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2821,plain,
% 4.14/0.99      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 4.14/0.99      inference(instantiation,[status(thm)],[c_1493]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2822,plain,
% 4.14/0.99      ( sK3 != k1_xboole_0
% 4.14/0.99      | k1_xboole_0 = sK3
% 4.14/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 4.14/0.99      inference(instantiation,[status(thm)],[c_2821]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2964,plain,
% 4.14/0.99      ( ~ r1_tarski(X0,k2_relset_1(sK2,sK3,sK4))
% 4.14/0.99      | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),X0)
% 4.14/0.99      | k2_relset_1(sK2,sK3,sK4) = X0 ),
% 4.14/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2966,plain,
% 4.14/0.99      ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_xboole_0)
% 4.14/0.99      | ~ r1_tarski(k1_xboole_0,k2_relset_1(sK2,sK3,sK4))
% 4.14/0.99      | k2_relset_1(sK2,sK3,sK4) = k1_xboole_0 ),
% 4.14/0.99      inference(instantiation,[status(thm)],[c_2964]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_3136,plain,
% 4.14/0.99      ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k2_relset_1(sK2,sK3,sK4))
% 4.14/0.99      | k2_relset_1(sK2,sK3,sK4) = k2_relset_1(sK2,sK3,sK4) ),
% 4.14/0.99      inference(instantiation,[status(thm)],[c_2964]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2,plain,
% 4.14/0.99      ( r1_tarski(X0,X0) ),
% 4.14/0.99      inference(cnf_transformation,[],[f69]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_4020,plain,
% 4.14/0.99      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k2_relset_1(sK2,sK3,sK4)) ),
% 4.14/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_8,plain,
% 4.14/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.14/0.99      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 4.14/0.99      inference(cnf_transformation,[],[f45]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_3586,plain,
% 4.14/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
% 4.14/0.99      | m1_subset_1(k2_relset_1(X1,sK3,X0),k1_zfmisc_1(sK3)) ),
% 4.14/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_5284,plain,
% 4.14/0.99      ( m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK3))
% 4.14/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 4.14/0.99      inference(instantiation,[status(thm)],[c_3586]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2511,plain,
% 4.14/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3)) | r1_tarski(X0,sK3) ),
% 4.14/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2789,plain,
% 4.14/0.99      ( ~ m1_subset_1(k2_relset_1(X0,sK3,X1),k1_zfmisc_1(sK3))
% 4.14/0.99      | r1_tarski(k2_relset_1(X0,sK3,X1),sK3) ),
% 4.14/0.99      inference(instantiation,[status(thm)],[c_2511]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_5879,plain,
% 4.14/0.99      ( ~ m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK3))
% 4.14/0.99      | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK3) ),
% 4.14/0.99      inference(instantiation,[status(thm)],[c_2789]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_4027,plain,
% 4.14/0.99      ( ~ r1_tarski(X0,X1)
% 4.14/0.99      | r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_xboole_0)
% 4.14/0.99      | k2_relset_1(sK2,sK3,sK4) != X0
% 4.14/0.99      | k1_xboole_0 != X1 ),
% 4.14/0.99      inference(instantiation,[status(thm)],[c_1494]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_4830,plain,
% 4.14/0.99      ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),X0)
% 4.14/0.99      | r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_xboole_0)
% 4.14/0.99      | k2_relset_1(sK2,sK3,sK4) != k2_relset_1(sK2,sK3,sK4)
% 4.14/0.99      | k1_xboole_0 != X0 ),
% 4.14/0.99      inference(instantiation,[status(thm)],[c_4027]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_7381,plain,
% 4.14/0.99      ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK3)
% 4.14/0.99      | r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_xboole_0)
% 4.14/0.99      | k2_relset_1(sK2,sK3,sK4) != k2_relset_1(sK2,sK3,sK4)
% 4.14/0.99      | k1_xboole_0 != sK3 ),
% 4.14/0.99      inference(instantiation,[status(thm)],[c_4830]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_12043,plain,
% 4.14/0.99      ( r1_tarski(k1_xboole_0,k2_relset_1(sK2,sK3,sK4)) ),
% 4.14/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_12055,plain,
% 4.14/0.99      ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
% 4.14/0.99      | k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4)) ),
% 4.14/0.99      inference(global_propositional_subsumption,
% 4.14/0.99                [status(thm)],
% 4.14/0.99                [c_11796,c_26,c_24,c_97,c_102,c_2353,c_2447,c_2637,
% 4.14/0.99                 c_2822,c_2966,c_3136,c_4020,c_5284,c_5879,c_7381,
% 4.14/0.99                 c_12043]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_12056,plain,
% 4.14/0.99      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 4.14/0.99      | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4) ),
% 4.14/0.99      inference(renaming,[status(thm)],[c_12055]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_25,negated_conjecture,
% 4.14/0.99      ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1)
% 4.14/0.99      | ~ m1_subset_1(X0,sK2) ),
% 4.14/0.99      inference(cnf_transformation,[],[f66]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_20,plain,
% 4.14/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 4.14/0.99      | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 4.14/0.99      | ~ v1_funct_1(X0)
% 4.14/0.99      | ~ v1_relat_1(X0) ),
% 4.14/0.99      inference(cnf_transformation,[],[f77]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_574,plain,
% 4.14/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 4.14/0.99      | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 4.14/0.99      | ~ v1_relat_1(X0)
% 4.14/0.99      | sK4 != X0 ),
% 4.14/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_28]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_575,plain,
% 4.14/0.99      ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
% 4.14/0.99      | ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
% 4.14/0.99      | ~ v1_relat_1(sK4) ),
% 4.14/0.99      inference(unflattening,[status(thm)],[c_574]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_777,plain,
% 4.14/0.99      ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
% 4.14/0.99      | ~ m1_subset_1(X1,sK2)
% 4.14/0.99      | ~ v1_relat_1(sK4)
% 4.14/0.99      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)) != k3_funct_2(sK2,sK3,sK4,X1)
% 4.14/0.99      | sK1 != X0 ),
% 4.14/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_575]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_778,plain,
% 4.14/0.99      ( v1_funct_2(sK4,k1_relat_1(sK4),sK1)
% 4.14/0.99      | ~ m1_subset_1(X0,sK2)
% 4.14/0.99      | ~ v1_relat_1(sK4)
% 4.14/0.99      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
% 4.14/0.99      inference(unflattening,[status(thm)],[c_777]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_1488,plain,
% 4.14/0.99      ( ~ m1_subset_1(X0,sK2)
% 4.14/0.99      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
% 4.14/0.99      | ~ sP2_iProver_split ),
% 4.14/0.99      inference(splitting,
% 4.14/0.99                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 4.14/0.99                [c_778]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2220,plain,
% 4.14/0.99      ( k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
% 4.14/0.99      | m1_subset_1(X0,sK2) != iProver_top
% 4.14/0.99      | sP2_iProver_split != iProver_top ),
% 4.14/0.99      inference(predicate_to_equality,[status(thm)],[c_1488]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_12059,plain,
% 4.14/0.99      ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
% 4.14/0.99      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 4.14/0.99      | m1_subset_1(sK0(sK2,X0,sK4),sK2) != iProver_top
% 4.14/0.99      | sP2_iProver_split != iProver_top ),
% 4.14/0.99      inference(superposition,[status(thm)],[c_12056,c_2220]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_6290,plain,
% 4.14/0.99      ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
% 4.14/0.99      | sK3 = k1_xboole_0
% 4.14/0.99      | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top ),
% 4.14/0.99      inference(superposition,[status(thm)],[c_4488,c_2237]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_12071,plain,
% 4.14/0.99      ( k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 4.14/0.99      | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
% 4.14/0.99      | sP2_iProver_split != iProver_top ),
% 4.14/0.99      inference(global_propositional_subsumption,
% 4.14/0.99                [status(thm)],
% 4.14/0.99                [c_12059,c_26,c_24,c_97,c_102,c_2353,c_2447,c_2637,
% 4.14/0.99                 c_2822,c_2966,c_3136,c_4020,c_5284,c_5879,c_6290,c_7381,
% 4.14/0.99                 c_12043]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_12072,plain,
% 4.14/0.99      ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
% 4.14/0.99      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 4.14/0.99      | sP2_iProver_split != iProver_top ),
% 4.14/0.99      inference(renaming,[status(thm)],[c_12071]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_12077,plain,
% 4.14/0.99      ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
% 4.14/0.99      | k1_funct_1(sK4,sK0(sK2,X0,sK4)) != k1_funct_1(sK4,sK0(sK2,sK1,sK4))
% 4.14/0.99      | sK3 = k1_xboole_0
% 4.14/0.99      | sP2_iProver_split != iProver_top ),
% 4.14/0.99      inference(superposition,[status(thm)],[c_4483,c_12072]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_12603,plain,
% 4.14/0.99      ( k1_funct_1(sK4,sK0(sK2,X0,sK4)) != k1_funct_1(sK4,sK0(sK2,sK1,sK4))
% 4.14/0.99      | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
% 4.14/0.99      | sP2_iProver_split != iProver_top ),
% 4.14/0.99      inference(global_propositional_subsumption,
% 4.14/0.99                [status(thm)],
% 4.14/0.99                [c_12077,c_26,c_24,c_97,c_102,c_2353,c_2447,c_2637,
% 4.14/0.99                 c_2822,c_2966,c_3136,c_4020,c_5284,c_5879,c_7381,
% 4.14/0.99                 c_12043]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_12604,plain,
% 4.14/0.99      ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
% 4.14/0.99      | k1_funct_1(sK4,sK0(sK2,X0,sK4)) != k1_funct_1(sK4,sK0(sK2,sK1,sK4))
% 4.14/0.99      | sP2_iProver_split != iProver_top ),
% 4.14/0.99      inference(renaming,[status(thm)],[c_12603]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_12609,plain,
% 4.14/0.99      ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4)
% 4.14/0.99      | sP2_iProver_split != iProver_top ),
% 4.14/0.99      inference(equality_resolution,[status(thm)],[c_12604]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_18,plain,
% 4.14/0.99      ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 4.14/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 4.14/0.99      | ~ v1_funct_1(X0)
% 4.14/0.99      | ~ v1_relat_1(X0) ),
% 4.14/0.99      inference(cnf_transformation,[],[f75]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_604,plain,
% 4.14/0.99      ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 4.14/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 4.14/0.99      | ~ v1_relat_1(X0)
% 4.14/0.99      | sK4 != X0 ),
% 4.14/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_28]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_605,plain,
% 4.14/0.99      ( ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
% 4.14/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 4.14/0.99      | ~ v1_relat_1(sK4) ),
% 4.14/0.99      inference(unflattening,[status(thm)],[c_604]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_759,plain,
% 4.14/0.99      ( ~ m1_subset_1(X0,sK2)
% 4.14/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X1)))
% 4.14/0.99      | ~ v1_relat_1(sK4)
% 4.14/0.99      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),X1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
% 4.14/0.99      | sK1 != X1 ),
% 4.14/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_605]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_760,plain,
% 4.14/0.99      ( ~ m1_subset_1(X0,sK2)
% 4.14/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
% 4.14/0.99      | ~ v1_relat_1(sK4)
% 4.14/0.99      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
% 4.14/0.99      inference(unflattening,[status(thm)],[c_759]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_1490,plain,
% 4.14/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
% 4.14/0.99      | ~ v1_relat_1(sK4)
% 4.14/0.99      | sP2_iProver_split ),
% 4.14/0.99      inference(splitting,
% 4.14/0.99                [splitting(split),new_symbols(definition,[])],
% 4.14/0.99                [c_760]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2221,plain,
% 4.14/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
% 4.14/0.99      | v1_relat_1(sK4) != iProver_top
% 4.14/0.99      | sP2_iProver_split = iProver_top ),
% 4.14/0.99      inference(predicate_to_equality,[status(thm)],[c_1490]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_1536,plain,
% 4.14/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
% 4.14/0.99      | v1_relat_1(sK4) != iProver_top
% 4.14/0.99      | sP2_iProver_split = iProver_top ),
% 4.14/0.99      inference(predicate_to_equality,[status(thm)],[c_1490]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2829,plain,
% 4.14/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
% 4.14/0.99      | sP2_iProver_split = iProver_top ),
% 4.14/0.99      inference(global_propositional_subsumption,
% 4.14/0.99                [status(thm)],
% 4.14/0.99                [c_2221,c_35,c_1536,c_2360]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_3175,plain,
% 4.14/0.99      ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4)
% 4.14/0.99      | sP2_iProver_split = iProver_top ),
% 4.14/0.99      inference(superposition,[status(thm)],[c_2829,c_2237]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_16890,plain,
% 4.14/0.99      ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4) ),
% 4.14/0.99      inference(global_propositional_subsumption,
% 4.14/0.99                [status(thm)],
% 4.14/0.99                [c_12609,c_3175]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2239,plain,
% 4.14/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.14/0.99      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 4.14/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_16901,plain,
% 4.14/0.99      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) = iProver_top
% 4.14/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) != iProver_top ),
% 4.14/0.99      inference(superposition,[status(thm)],[c_16890,c_2239]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_39,plain,
% 4.14/0.99      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) != iProver_top ),
% 4.14/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2969,plain,
% 4.14/0.99      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
% 4.14/0.99      | ~ r1_tarski(k2_relat_1(sK4),sK1)
% 4.14/0.99      | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
% 4.14/0.99      | sK1 != sK1 ),
% 4.14/0.99      inference(instantiation,[status(thm)],[c_2351]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2970,plain,
% 4.14/0.99      ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
% 4.14/0.99      | sK1 != sK1
% 4.14/0.99      | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) = iProver_top
% 4.14/0.99      | r1_tarski(k2_relat_1(sK4),sK1) != iProver_top ),
% 4.14/0.99      inference(predicate_to_equality,[status(thm)],[c_2969]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_3174,plain,
% 4.14/0.99      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 4.14/0.99      inference(superposition,[status(thm)],[c_2229,c_2237]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2527,plain,
% 4.14/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.14/0.99      | r1_tarski(sK4,k2_zfmisc_1(X0,X1)) ),
% 4.14/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_2869,plain,
% 4.14/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 4.14/0.99      | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),X0)) ),
% 4.14/0.99      inference(instantiation,[status(thm)],[c_2527]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_3249,plain,
% 4.14/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
% 4.14/0.99      | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),sK1)) ),
% 4.14/0.99      inference(instantiation,[status(thm)],[c_2869]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_3250,plain,
% 4.14/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) != iProver_top
% 4.14/0.99      | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),sK1)) = iProver_top ),
% 4.14/0.99      inference(predicate_to_equality,[status(thm)],[c_3249]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_3775,plain,
% 4.14/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.14/0.99      | r1_tarski(k2_relset_1(X1,X2,X0),X2) = iProver_top ),
% 4.14/0.99      inference(superposition,[status(thm)],[c_2239,c_2241]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_7617,plain,
% 4.14/0.99      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 4.14/0.99      | r1_tarski(k2_relset_1(X1,X2,X0),X2) = iProver_top ),
% 4.14/0.99      inference(superposition,[status(thm)],[c_2242,c_3775]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_16900,plain,
% 4.14/0.99      ( r1_tarski(k2_relat_1(sK4),sK1) = iProver_top
% 4.14/0.99      | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),sK1)) != iProver_top ),
% 4.14/0.99      inference(superposition,[status(thm)],[c_16890,c_7617]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_17068,plain,
% 4.14/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) != iProver_top ),
% 4.14/0.99      inference(global_propositional_subsumption,
% 4.14/0.99                [status(thm)],
% 4.14/0.99                [c_16901,c_39,c_2447,c_2970,c_3174,c_3250,c_16900]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_17072,plain,
% 4.14/0.99      ( r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),sK1)) != iProver_top ),
% 4.14/0.99      inference(superposition,[status(thm)],[c_2242,c_17068]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_17357,plain,
% 4.14/0.99      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,sK1,sK4)) = k1_funct_1(sK4,sK0(sK2,sK1,sK4))
% 4.14/0.99      | sK3 = k1_xboole_0 ),
% 4.14/0.99      inference(superposition,[status(thm)],[c_11670,c_17072]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_17599,plain,
% 4.14/0.99      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,sK1,sK4)) = k1_funct_1(sK4,sK0(sK2,sK1,sK4)) ),
% 4.14/0.99      inference(global_propositional_subsumption,
% 4.14/0.99                [status(thm)],
% 4.14/0.99                [c_17357,c_26,c_24,c_97,c_102,c_2353,c_2447,c_2637,
% 4.14/0.99                 c_2822,c_2966,c_3136,c_4020,c_5284,c_5879,c_7381,
% 4.14/0.99                 c_12043]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_4509,plain,
% 4.14/0.99      ( k1_funct_1(sK4,sK0(sK2,sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
% 4.14/0.99      | sK3 = k1_xboole_0
% 4.14/0.99      | m1_subset_1(X0,sK2) != iProver_top
% 4.14/0.99      | sP2_iProver_split != iProver_top ),
% 4.14/0.99      inference(superposition,[status(thm)],[c_4483,c_2220]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_17601,plain,
% 4.14/0.99      ( sK3 = k1_xboole_0
% 4.14/0.99      | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
% 4.14/0.99      | sP2_iProver_split != iProver_top ),
% 4.14/0.99      inference(superposition,[status(thm)],[c_17599,c_4509]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_7621,plain,
% 4.14/0.99      ( sK3 = k1_xboole_0
% 4.14/0.99      | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
% 4.14/0.99      | r1_tarski(k2_relset_1(k1_relat_1(sK4),X0,sK4),X0) = iProver_top ),
% 4.14/0.99      inference(superposition,[status(thm)],[c_4488,c_3775]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_17025,plain,
% 4.14/0.99      ( m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
% 4.14/0.99      | r1_tarski(k2_relset_1(k1_relat_1(sK4),X0,sK4),X0) = iProver_top ),
% 4.14/0.99      inference(global_propositional_subsumption,
% 4.14/0.99                [status(thm)],
% 4.14/0.99                [c_7621,c_26,c_24,c_97,c_102,c_2353,c_2447,c_2637,c_2822,
% 4.14/0.99                 c_2966,c_3136,c_4020,c_5284,c_5879,c_7381,c_12043]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_17031,plain,
% 4.14/0.99      ( m1_subset_1(sK0(sK2,sK1,sK4),sK2) = iProver_top
% 4.14/0.99      | r1_tarski(k2_relat_1(sK4),sK1) = iProver_top ),
% 4.14/0.99      inference(superposition,[status(thm)],[c_16890,c_17025]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_7622,plain,
% 4.14/0.99      ( r1_tarski(k2_relset_1(k1_relat_1(sK4),sK1,sK4),sK1) = iProver_top
% 4.14/0.99      | sP2_iProver_split = iProver_top ),
% 4.14/0.99      inference(superposition,[status(thm)],[c_2829,c_3775]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(c_16894,plain,
% 4.14/0.99      ( r1_tarski(k2_relat_1(sK4),sK1) = iProver_top
% 4.14/0.99      | sP2_iProver_split = iProver_top ),
% 4.14/0.99      inference(demodulation,[status(thm)],[c_16890,c_7622]) ).
% 4.14/0.99  
% 4.14/0.99  cnf(contradiction,plain,
% 4.14/0.99      ( $false ),
% 4.14/0.99      inference(minisat,
% 4.14/0.99                [status(thm)],
% 4.14/0.99                [c_17601,c_17031,c_16894,c_12043,c_7381,c_5879,c_5284,
% 4.14/0.99                 c_4020,c_3174,c_3136,c_2970,c_2966,c_2822,c_2637,c_2447,
% 4.14/0.99                 c_2353,c_102,c_97,c_39,c_24,c_26]) ).
% 4.14/0.99  
% 4.14/0.99  
% 4.14/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 4.14/0.99  
% 4.14/0.99  ------                               Statistics
% 4.14/0.99  
% 4.14/0.99  ------ General
% 4.14/0.99  
% 4.14/0.99  abstr_ref_over_cycles:                  0
% 4.14/0.99  abstr_ref_under_cycles:                 0
% 4.14/0.99  gc_basic_clause_elim:                   0
% 4.14/0.99  forced_gc_time:                         0
% 4.14/0.99  parsing_time:                           0.008
% 4.14/0.99  unif_index_cands_time:                  0.
% 4.14/0.99  unif_index_add_time:                    0.
% 4.14/0.99  orderings_time:                         0.
% 4.14/0.99  out_proof_time:                         0.012
% 4.14/0.99  total_time:                             0.492
% 4.14/0.99  num_of_symbols:                         55
% 4.14/0.99  num_of_terms:                           13622
% 4.14/0.99  
% 4.14/0.99  ------ Preprocessing
% 4.14/0.99  
% 4.14/0.99  num_of_splits:                          6
% 4.14/0.99  num_of_split_atoms:                     3
% 4.14/0.99  num_of_reused_defs:                     3
% 4.14/0.99  num_eq_ax_congr_red:                    17
% 4.14/0.99  num_of_sem_filtered_clauses:            1
% 4.14/0.99  num_of_subtypes:                        0
% 4.14/0.99  monotx_restored_types:                  0
% 4.14/0.99  sat_num_of_epr_types:                   0
% 4.14/0.99  sat_num_of_non_cyclic_types:            0
% 4.14/0.99  sat_guarded_non_collapsed_types:        0
% 4.14/0.99  num_pure_diseq_elim:                    0
% 4.14/0.99  simp_replaced_by:                       0
% 4.14/0.99  res_preprocessed:                       150
% 4.14/0.99  prep_upred:                             0
% 4.14/0.99  prep_unflattend:                        40
% 4.14/0.99  smt_new_axioms:                         0
% 4.14/0.99  pred_elim_cands:                        4
% 4.14/0.99  pred_elim:                              3
% 4.14/0.99  pred_elim_cl:                           -1
% 4.14/0.99  pred_elim_cycles:                       7
% 4.14/0.99  merged_defs:                            8
% 4.14/0.99  merged_defs_ncl:                        0
% 4.14/0.99  bin_hyper_res:                          8
% 4.14/0.99  prep_cycles:                            4
% 4.14/0.99  pred_elim_time:                         0.02
% 4.14/0.99  splitting_time:                         0.
% 4.14/0.99  sem_filter_time:                        0.
% 4.14/0.99  monotx_time:                            0.
% 4.14/0.99  subtype_inf_time:                       0.
% 4.14/0.99  
% 4.14/0.99  ------ Problem properties
% 4.14/0.99  
% 4.14/0.99  clauses:                                35
% 4.14/0.99  conjectures:                            3
% 4.14/0.99  epr:                                    4
% 4.14/0.99  horn:                                   23
% 4.14/0.99  ground:                                 9
% 4.14/0.99  unary:                                  5
% 4.14/0.99  binary:                                 7
% 4.14/0.99  lits:                                   93
% 4.14/0.99  lits_eq:                                20
% 4.14/0.99  fd_pure:                                0
% 4.14/0.99  fd_pseudo:                              0
% 4.14/0.99  fd_cond:                                3
% 4.14/0.99  fd_pseudo_cond:                         1
% 4.14/0.99  ac_symbols:                             0
% 4.14/0.99  
% 4.14/0.99  ------ Propositional Solver
% 4.14/0.99  
% 4.14/0.99  prop_solver_calls:                      33
% 4.14/0.99  prop_fast_solver_calls:                 2131
% 4.14/0.99  smt_solver_calls:                       0
% 4.14/0.99  smt_fast_solver_calls:                  0
% 4.14/0.99  prop_num_of_clauses:                    6915
% 4.14/0.99  prop_preprocess_simplified:             14387
% 4.14/0.99  prop_fo_subsumed:                       108
% 4.14/0.99  prop_solver_time:                       0.
% 4.14/0.99  smt_solver_time:                        0.
% 4.14/0.99  smt_fast_solver_time:                   0.
% 4.14/0.99  prop_fast_solver_time:                  0.
% 4.14/0.99  prop_unsat_core_time:                   0.
% 4.14/0.99  
% 4.14/0.99  ------ QBF
% 4.14/0.99  
% 4.14/0.99  qbf_q_res:                              0
% 4.14/0.99  qbf_num_tautologies:                    0
% 4.14/0.99  qbf_prep_cycles:                        0
% 4.14/0.99  
% 4.14/0.99  ------ BMC1
% 4.14/0.99  
% 4.14/0.99  bmc1_current_bound:                     -1
% 4.14/0.99  bmc1_last_solved_bound:                 -1
% 4.14/0.99  bmc1_unsat_core_size:                   -1
% 4.14/0.99  bmc1_unsat_core_parents_size:           -1
% 4.14/0.99  bmc1_merge_next_fun:                    0
% 4.14/0.99  bmc1_unsat_core_clauses_time:           0.
% 4.14/0.99  
% 4.14/0.99  ------ Instantiation
% 4.14/0.99  
% 4.14/0.99  inst_num_of_clauses:                    1939
% 4.14/0.99  inst_num_in_passive:                    246
% 4.14/0.99  inst_num_in_active:                     1055
% 4.14/0.99  inst_num_in_unprocessed:                638
% 4.14/0.99  inst_num_of_loops:                      1220
% 4.14/0.99  inst_num_of_learning_restarts:          0
% 4.14/0.99  inst_num_moves_active_passive:          159
% 4.14/0.99  inst_lit_activity:                      0
% 4.14/0.99  inst_lit_activity_moves:                0
% 4.14/0.99  inst_num_tautologies:                   0
% 4.14/0.99  inst_num_prop_implied:                  0
% 4.14/0.99  inst_num_existing_simplified:           0
% 4.14/0.99  inst_num_eq_res_simplified:             0
% 4.14/0.99  inst_num_child_elim:                    0
% 4.14/0.99  inst_num_of_dismatching_blockings:      945
% 4.14/0.99  inst_num_of_non_proper_insts:           3139
% 4.14/0.99  inst_num_of_duplicates:                 0
% 4.14/0.99  inst_inst_num_from_inst_to_res:         0
% 4.14/0.99  inst_dismatching_checking_time:         0.
% 4.14/0.99  
% 4.14/0.99  ------ Resolution
% 4.14/0.99  
% 4.14/0.99  res_num_of_clauses:                     0
% 4.14/0.99  res_num_in_passive:                     0
% 4.14/0.99  res_num_in_active:                      0
% 4.14/0.99  res_num_of_loops:                       154
% 4.14/0.99  res_forward_subset_subsumed:            261
% 4.14/0.99  res_backward_subset_subsumed:           2
% 4.14/0.99  res_forward_subsumed:                   0
% 4.14/0.99  res_backward_subsumed:                  0
% 4.14/0.99  res_forward_subsumption_resolution:     0
% 4.14/0.99  res_backward_subsumption_resolution:    0
% 4.14/0.99  res_clause_to_clause_subsumption:       1089
% 4.14/0.99  res_orphan_elimination:                 0
% 4.14/0.99  res_tautology_del:                      238
% 4.14/0.99  res_num_eq_res_simplified:              0
% 4.14/0.99  res_num_sel_changes:                    0
% 4.14/0.99  res_moves_from_active_to_pass:          0
% 4.14/0.99  
% 4.14/0.99  ------ Superposition
% 4.14/0.99  
% 4.14/0.99  sup_time_total:                         0.
% 4.14/0.99  sup_time_generating:                    0.
% 4.14/0.99  sup_time_sim_full:                      0.
% 4.14/0.99  sup_time_sim_immed:                     0.
% 4.14/0.99  
% 4.14/0.99  sup_num_of_clauses:                     354
% 4.14/0.99  sup_num_in_active:                      198
% 4.14/0.99  sup_num_in_passive:                     156
% 4.14/0.99  sup_num_of_loops:                       242
% 4.14/0.99  sup_fw_superposition:                   266
% 4.14/0.99  sup_bw_superposition:                   303
% 4.14/0.99  sup_immediate_simplified:               102
% 4.14/0.99  sup_given_eliminated:                   2
% 4.14/0.99  comparisons_done:                       0
% 4.14/0.99  comparisons_avoided:                    368
% 4.14/0.99  
% 4.14/0.99  ------ Simplifications
% 4.14/0.99  
% 4.14/0.99  
% 4.14/0.99  sim_fw_subset_subsumed:                 34
% 4.14/0.99  sim_bw_subset_subsumed:                 20
% 4.14/0.99  sim_fw_subsumed:                        28
% 4.14/0.99  sim_bw_subsumed:                        31
% 4.14/0.99  sim_fw_subsumption_res:                 0
% 4.14/0.99  sim_bw_subsumption_res:                 0
% 4.14/0.99  sim_tautology_del:                      1
% 4.14/0.99  sim_eq_tautology_del:                   8
% 4.14/0.99  sim_eq_res_simp:                        0
% 4.14/0.99  sim_fw_demodulated:                     35
% 4.14/0.99  sim_bw_demodulated:                     13
% 4.14/0.99  sim_light_normalised:                   17
% 4.14/0.99  sim_joinable_taut:                      0
% 4.14/0.99  sim_joinable_simp:                      0
% 4.14/0.99  sim_ac_normalised:                      0
% 4.14/0.99  sim_smt_subsumption:                    0
% 4.14/0.99  
%------------------------------------------------------------------------------
