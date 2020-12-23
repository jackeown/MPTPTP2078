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
% DateTime   : Thu Dec  3 12:10:12 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  277 (6070 expanded)
%              Number of clauses        :  192 (2097 expanded)
%              Number of leaves         :   23 (1482 expanded)
%              Depth                    :   33
%              Number of atoms          :  904 (31705 expanded)
%              Number of equality atoms :  358 (3014 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f41])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f93,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f54])).

fof(f16,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,
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

fof(f51,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1)
        | ~ m1_subset_1(X4,sK2) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f40,f50,f49,f48])).

fof(f90,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f51])).

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

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f89,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
        & r2_hidden(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
        & r2_hidden(sK0(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f46])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK0(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f101,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f84])).

fof(f88,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f94,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f53])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f79,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f29])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f87,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f92,plain,(
    ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f103,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f82])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f100,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f85])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f86,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f91,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f102,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | ~ r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f83])).

cnf(c_0,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2588,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2590,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4727,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2588,c_2590])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2598,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3742,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2588,c_2598])).

cnf(c_4733,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4727,c_3742])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_44,plain,
    ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4738,plain,
    ( sK3 = k1_xboole_0
    | k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4733,c_44])).

cnf(c_4739,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4738])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_29,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_850,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_38])).

cnf(c_851,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_850])).

cnf(c_1132,plain,
    ( m1_subset_1(X0,X1)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X2)))
    | ~ v1_relat_1(sK4)
    | sK0(k1_relat_1(sK4),X2,sK4) != X0
    | k1_relat_1(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_851])).

cnf(c_1133,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_1132])).

cnf(c_2576,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1133])).

cnf(c_45,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_1134,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1133])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2674,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2761,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2674])).

cnf(c_2762,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2761])).

cnf(c_4928,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2576,c_45,c_1134,c_2762])).

cnf(c_4929,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_4928])).

cnf(c_4934,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4739,c_4929])).

cnf(c_8218,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK2,k1_xboole_0,sK4),sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_4934])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_133,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_134,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_7,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_420,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_9,c_7])).

cnf(c_430,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_420,c_8])).

cnf(c_2896,plain,
    ( r1_tarski(k2_relat_1(sK4),X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ),
    inference(instantiation,[status(thm)],[c_430])).

cnf(c_3062,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_2896])).

cnf(c_3063,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3062])).

cnf(c_1977,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3304,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_1977])).

cnf(c_3305,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3304])).

cnf(c_1981,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2939,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_relat_1(X2),X3)
    | X1 != X3
    | X0 != k2_relat_1(X2) ),
    inference(instantiation,[status(thm)],[c_1981])).

cnf(c_3213,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_relat_1(sK4),sK3)
    | X0 != k2_relat_1(sK4)
    | X1 != sK3 ),
    inference(instantiation,[status(thm)],[c_2939])).

cnf(c_4348,plain,
    ( r1_tarski(k2_relat_1(sK4),X0)
    | ~ r1_tarski(k2_relat_1(sK4),sK3)
    | X0 != sK3
    | k2_relat_1(sK4) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3213])).

cnf(c_4349,plain,
    ( X0 != sK3
    | k2_relat_1(sK4) != k2_relat_1(sK4)
    | r1_tarski(k2_relat_1(sK4),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4348])).

cnf(c_4351,plain,
    ( k2_relat_1(sK4) != k2_relat_1(sK4)
    | k1_xboole_0 != sK3
    | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
    | r1_tarski(k2_relat_1(sK4),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4349])).

cnf(c_1976,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4988,plain,
    ( k2_relat_1(sK4) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1976])).

cnf(c_25,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_890,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_38])).

cnf(c_891,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_890])).

cnf(c_2579,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_891])).

cnf(c_892,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_891])).

cnf(c_2783,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2579,c_45,c_892,c_2762])).

cnf(c_10,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_5,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_399,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_10,c_5])).

cnf(c_403,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_399,c_10,c_8,c_5])).

cnf(c_404,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(renaming,[status(thm)],[c_403])).

cnf(c_2586,plain,
    ( r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_404])).

cnf(c_5610,plain,
    ( r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2783,c_2586])).

cnf(c_13,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ r1_tarski(k1_relat_1(X0),X2)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2596,plain,
    ( r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5147,plain,
    ( r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_2596])).

cnf(c_5895,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5610,c_5147])).

cnf(c_6170,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5895,c_45,c_2762])).

cnf(c_6171,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6170])).

cnf(c_8528,plain,
    ( m1_subset_1(sK0(sK2,k1_xboole_0,sK4),sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8218,c_45,c_133,c_134,c_3063,c_3305,c_4351,c_4988,c_6171])).

cnf(c_4758,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK4)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4739,c_2783])).

cnf(c_3065,plain,
    ( r1_tarski(k2_relat_1(sK4),X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) ),
    inference(instantiation,[status(thm)],[c_2896])).

cnf(c_3162,plain,
    ( r1_tarski(k2_relat_1(sK4),k2_relat_1(sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) ),
    inference(instantiation,[status(thm)],[c_3065])).

cnf(c_3163,plain,
    ( r1_tarski(k2_relat_1(sK4),k2_relat_1(sK4)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3162])).

cnf(c_3239,plain,
    ( r1_tarski(k1_relat_1(sK4),sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_404])).

cnf(c_3240,plain,
    ( r1_tarski(k1_relat_1(sK4),sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3239])).

cnf(c_2764,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),X0)
    | ~ r1_tarski(k1_relat_1(sK4),X1)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3260,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),k2_relat_1(sK4))
    | ~ r1_tarski(k1_relat_1(sK4),X0)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2764])).

cnf(c_3796,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),k2_relat_1(sK4))
    | ~ r1_tarski(k1_relat_1(sK4),sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK4))))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3260])).

cnf(c_3797,plain,
    ( r1_tarski(k2_relat_1(sK4),k2_relat_1(sK4)) != iProver_top
    | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK4)))) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3796])).

cnf(c_4842,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4758,c_45,c_892,c_2762,c_3163,c_3240,c_3797])).

cnf(c_4846,plain,
    ( k1_relset_1(sK2,k2_relat_1(sK4),sK4) = sK2
    | k2_relat_1(sK4) = k1_xboole_0
    | v1_funct_2(sK4,sK2,k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4842,c_2590])).

cnf(c_4847,plain,
    ( k1_relset_1(sK2,k2_relat_1(sK4),sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_4842,c_2598])).

cnf(c_4852,plain,
    ( k2_relat_1(sK4) = k1_xboole_0
    | k1_relat_1(sK4) = sK2
    | v1_funct_2(sK4,sK2,k2_relat_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4846,c_4847])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_39,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_509,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_39])).

cnf(c_510,plain,
    ( ~ v1_funct_2(X0,X1,sK3)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_509])).

cnf(c_769,plain,
    ( ~ v1_funct_2(X0,X1,sK3)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_510,c_38])).

cnf(c_770,plain,
    ( ~ v1_funct_2(sK4,X0,sK3)
    | v1_partfun1(sK4,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) ),
    inference(unflattening,[status(thm)],[c_769])).

cnf(c_2700,plain,
    ( ~ v1_funct_2(sK4,sK2,sK3)
    | v1_partfun1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_770])).

cnf(c_14,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_900,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_38])).

cnf(c_901,plain,
    ( v1_funct_2(sK4,X0,X1)
    | ~ v1_partfun1(sK4,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(unflattening,[status(thm)],[c_900])).

cnf(c_2736,plain,
    ( v1_funct_2(sK4,sK2,X0)
    | ~ v1_partfun1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) ),
    inference(instantiation,[status(thm)],[c_901])).

cnf(c_4308,plain,
    ( v1_funct_2(sK4,sK2,k2_relat_1(sK4))
    | ~ v1_partfun1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK4)))) ),
    inference(instantiation,[status(thm)],[c_2736])).

cnf(c_4857,plain,
    ( ~ v1_funct_2(sK4,sK2,k2_relat_1(sK4))
    | k2_relat_1(sK4) = k1_xboole_0
    | k1_relat_1(sK4) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4852])).

cnf(c_9704,plain,
    ( k1_relat_1(sK4) = sK2
    | k2_relat_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4852,c_37,c_36,c_891,c_2700,c_2761,c_3162,c_3239,c_3796,c_4308,c_4857])).

cnf(c_9705,plain,
    ( k2_relat_1(sK4) = k1_xboole_0
    | k1_relat_1(sK4) = sK2 ),
    inference(renaming,[status(thm)],[c_9704])).

cnf(c_9726,plain,
    ( k1_relat_1(sK4) = sK2
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9705,c_2783])).

cnf(c_9727,plain,
    ( k1_relat_1(sK4) = sK2
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9726,c_0])).

cnf(c_2585,plain,
    ( r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_430])).

cnf(c_4999,plain,
    ( r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_2585])).

cnf(c_9881,plain,
    ( k1_relat_1(sK4) = sK2
    | r1_tarski(k2_relat_1(sK4),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9727,c_4999])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2597,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3271,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2588,c_2597])).

cnf(c_34,negated_conjecture,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2589,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3329,plain,
    ( r1_tarski(k2_relat_1(sK4),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3271,c_2589])).

cnf(c_10038,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(superposition,[status(thm)],[c_9881,c_3329])).

cnf(c_31,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_820,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_38])).

cnf(c_821,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
    | r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_820])).

cnf(c_28,plain,
    ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_865,plain,
    ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_38])).

cnf(c_866,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_865])).

cnf(c_1234,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X1)))
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),X1,sK4)) != sK0(k1_relat_1(sK4),X0,sK4)
    | k1_relat_1(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_821,c_866])).

cnf(c_1235,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_relat_1(sK4))))
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),k1_relat_1(sK4),sK4)) != sK0(k1_relat_1(sK4),X0,sK4) ),
    inference(unflattening,[status(thm)],[c_1234])).

cnf(c_1968,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_relat_1(sK4))))
    | ~ v1_relat_1(sK4)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1235])).

cnf(c_2565,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_relat_1(sK4)))) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1968])).

cnf(c_2012,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_relat_1(sK4)))) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1968])).

cnf(c_4226,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_relat_1(sK4)))) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2565,c_45,c_2012,c_2762])).

cnf(c_4996,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_relat_1(sK4)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_4226,c_2585])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_40,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_488,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_40])).

cnf(c_489,plain,
    ( ~ v1_funct_2(X0,sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | ~ m1_subset_1(X2,sK2)
    | ~ v1_funct_1(X0)
    | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_784,plain,
    ( ~ v1_funct_2(X0,sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | ~ m1_subset_1(X2,sK2)
    | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_489,c_38])).

cnf(c_785,plain,
    ( ~ v1_funct_2(sK4,sK2,X0)
    | ~ m1_subset_1(X1,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1) ),
    inference(unflattening,[status(thm)],[c_784])).

cnf(c_2582,plain,
    ( k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1)
    | v1_funct_2(sK4,sK2,X0) != iProver_top
    | m1_subset_1(X1,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_785])).

cnf(c_786,plain,
    ( k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1)
    | v1_funct_2(sK4,sK2,X0) != iProver_top
    | m1_subset_1(X1,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_785])).

cnf(c_2701,plain,
    ( v1_funct_2(sK4,sK2,sK3) != iProver_top
    | v1_partfun1(sK4,sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2700])).

cnf(c_2737,plain,
    ( v1_funct_2(sK4,sK2,X0) = iProver_top
    | v1_partfun1(sK4,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2736])).

cnf(c_3129,plain,
    ( k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1)
    | m1_subset_1(X1,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2582,c_44,c_45,c_786,c_2701,c_2737])).

cnf(c_5156,plain,
    ( k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1)
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top
    | m1_subset_1(X1,sK2) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2596,c_3129])).

cnf(c_5360,plain,
    ( m1_subset_1(X1,sK2) != iProver_top
    | k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1)
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5156,c_45,c_2762,c_3240])).

cnf(c_5361,plain,
    ( k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1)
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | m1_subset_1(X1,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5360])).

cnf(c_6823,plain,
    ( k3_funct_2(sK2,k1_relat_1(sK4),sK4,X0) = k1_funct_1(sK4,X0)
    | m1_subset_1(X0,sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_4996,c_5361])).

cnf(c_10053,plain,
    ( k3_funct_2(sK2,sK2,sK4,X0) = k1_funct_1(sK4,X0)
    | m1_subset_1(X0,sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_10038,c_6823])).

cnf(c_13035,plain,
    ( k3_funct_2(sK2,sK2,sK4,sK0(sK2,k1_xboole_0,sK4)) = k1_funct_1(sK4,sK0(sK2,k1_xboole_0,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_8528,c_10053])).

cnf(c_49,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2664,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
    | k2_relset_1(sK2,sK3,sK4) != X0
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_1981])).

cnf(c_2746,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(X0)
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_2664])).

cnf(c_2864,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
    | ~ r1_tarski(k2_relat_1(X0),sK1)
    | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(X0)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2746])).

cnf(c_3022,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
    | ~ r1_tarski(k2_relat_1(sK4),sK1)
    | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2864])).

cnf(c_3023,plain,
    ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
    | sK1 != sK1
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) = iProver_top
    | r1_tarski(k2_relat_1(sK4),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3022])).

cnf(c_3189,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1976])).

cnf(c_8225,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK4),X0) = iProver_top
    | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4934,c_2585])).

cnf(c_10081,plain,
    ( m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10038,c_4929])).

cnf(c_3135,plain,
    ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2588,c_3129])).

cnf(c_12017,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_10081,c_3135])).

cnf(c_12028,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | r1_tarski(k2_relat_1(sK4),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12017,c_2585])).

cnf(c_13281,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,sK1,sK4)) = k1_funct_1(sK4,sK0(sK2,sK1,sK4)) ),
    inference(superposition,[status(thm)],[c_12028,c_3329])).

cnf(c_35,negated_conjecture,
    ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1)
    | ~ m1_subset_1(X0,sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_30,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_835,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_38])).

cnf(c_836,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
    | ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_835])).

cnf(c_1180,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
    | ~ m1_subset_1(X1,sK2)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)) != k3_funct_2(sK2,sK3,sK4,X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_836])).

cnf(c_1181,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),sK1)
    | ~ m1_subset_1(X0,sK2)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
    inference(unflattening,[status(thm)],[c_1180])).

cnf(c_1972,plain,
    ( ~ m1_subset_1(X0,sK2)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_1181])).

cnf(c_2572,plain,
    ( k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
    | m1_subset_1(X0,sK2) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1972])).

cnf(c_10093,plain,
    ( k1_funct_1(sK4,sK0(sK2,sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
    | m1_subset_1(X0,sK2) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_10038,c_2572])).

cnf(c_1162,plain,
    ( ~ m1_subset_1(X0,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X1)))
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),X1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_866])).

cnf(c_1163,plain,
    ( ~ m1_subset_1(X0,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
    inference(unflattening,[status(thm)],[c_1162])).

cnf(c_1974,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
    | ~ v1_relat_1(sK4)
    | sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1163])).

cnf(c_2024,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1974])).

cnf(c_3165,plain,
    ( r1_tarski(k2_relat_1(sK4),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) ),
    inference(instantiation,[status(thm)],[c_3065])).

cnf(c_3166,plain,
    ( r1_tarski(k2_relat_1(sK4),sK1) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3165])).

cnf(c_10278,plain,
    ( m1_subset_1(X0,sK2) != iProver_top
    | k1_funct_1(sK4,sK0(sK2,sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10093,c_45,c_49,c_2024,c_2762,c_3023,c_3166,c_3189,c_3271])).

cnf(c_10279,plain,
    ( k1_funct_1(sK4,sK0(sK2,sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_10278])).

cnf(c_13289,plain,
    ( m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_13281,c_10279])).

cnf(c_14083,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK4),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_8225,c_13289])).

cnf(c_14279,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13035,c_45,c_49,c_133,c_134,c_2762,c_3023,c_3063,c_3189,c_3271,c_3305,c_4351,c_4988,c_5895,c_14083])).

cnf(c_5614,plain,
    ( r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_2586])).

cnf(c_14287,plain,
    ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_14279,c_5614])).

cnf(c_14293,plain,
    ( r1_tarski(sK2,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14287,c_10038])).

cnf(c_14308,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_14293])).

cnf(c_4993,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2588,c_2585])).

cnf(c_5148,plain,
    ( r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_2596])).

cnf(c_5760,plain,
    ( r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4993,c_5148])).

cnf(c_6013,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5760,c_45,c_2762])).

cnf(c_6014,plain,
    ( r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6013])).

cnf(c_6017,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4739,c_6014])).

cnf(c_7354,plain,
    ( r1_tarski(sK2,k1_xboole_0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6017,c_45,c_133,c_134,c_2762,c_3063,c_3305,c_4351,c_4988,c_5895])).

cnf(c_7363,plain,
    ( r1_tarski(k2_relat_1(sK4),X0) = iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7354,c_4999])).

cnf(c_7648,plain,
    ( r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7363,c_3329])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14308,c_7648])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 13:19:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.70/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.00  
% 3.70/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.70/1.00  
% 3.70/1.00  ------  iProver source info
% 3.70/1.00  
% 3.70/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.70/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.70/1.00  git: non_committed_changes: false
% 3.70/1.00  git: last_make_outside_of_git: false
% 3.70/1.00  
% 3.70/1.00  ------ 
% 3.70/1.00  
% 3.70/1.00  ------ Input Options
% 3.70/1.00  
% 3.70/1.00  --out_options                           all
% 3.70/1.00  --tptp_safe_out                         true
% 3.70/1.00  --problem_path                          ""
% 3.70/1.00  --include_path                          ""
% 3.70/1.00  --clausifier                            res/vclausify_rel
% 3.70/1.00  --clausifier_options                    ""
% 3.70/1.00  --stdin                                 false
% 3.70/1.00  --stats_out                             all
% 3.70/1.00  
% 3.70/1.00  ------ General Options
% 3.70/1.00  
% 3.70/1.00  --fof                                   false
% 3.70/1.00  --time_out_real                         305.
% 3.70/1.00  --time_out_virtual                      -1.
% 3.70/1.00  --symbol_type_check                     false
% 3.70/1.00  --clausify_out                          false
% 3.70/1.00  --sig_cnt_out                           false
% 3.70/1.00  --trig_cnt_out                          false
% 3.70/1.00  --trig_cnt_out_tolerance                1.
% 3.70/1.00  --trig_cnt_out_sk_spl                   false
% 3.70/1.00  --abstr_cl_out                          false
% 3.70/1.00  
% 3.70/1.00  ------ Global Options
% 3.70/1.00  
% 3.70/1.00  --schedule                              default
% 3.70/1.00  --add_important_lit                     false
% 3.70/1.00  --prop_solver_per_cl                    1000
% 3.70/1.00  --min_unsat_core                        false
% 3.70/1.00  --soft_assumptions                      false
% 3.70/1.00  --soft_lemma_size                       3
% 3.70/1.00  --prop_impl_unit_size                   0
% 3.70/1.00  --prop_impl_unit                        []
% 3.70/1.00  --share_sel_clauses                     true
% 3.70/1.00  --reset_solvers                         false
% 3.70/1.00  --bc_imp_inh                            [conj_cone]
% 3.70/1.00  --conj_cone_tolerance                   3.
% 3.70/1.00  --extra_neg_conj                        none
% 3.70/1.00  --large_theory_mode                     true
% 3.70/1.00  --prolific_symb_bound                   200
% 3.70/1.00  --lt_threshold                          2000
% 3.70/1.00  --clause_weak_htbl                      true
% 3.70/1.00  --gc_record_bc_elim                     false
% 3.70/1.00  
% 3.70/1.00  ------ Preprocessing Options
% 3.70/1.00  
% 3.70/1.00  --preprocessing_flag                    true
% 3.70/1.00  --time_out_prep_mult                    0.1
% 3.70/1.00  --splitting_mode                        input
% 3.70/1.00  --splitting_grd                         true
% 3.70/1.00  --splitting_cvd                         false
% 3.70/1.00  --splitting_cvd_svl                     false
% 3.70/1.00  --splitting_nvd                         32
% 3.70/1.00  --sub_typing                            true
% 3.70/1.00  --prep_gs_sim                           true
% 3.70/1.00  --prep_unflatten                        true
% 3.70/1.00  --prep_res_sim                          true
% 3.70/1.00  --prep_upred                            true
% 3.70/1.00  --prep_sem_filter                       exhaustive
% 3.70/1.00  --prep_sem_filter_out                   false
% 3.70/1.00  --pred_elim                             true
% 3.70/1.00  --res_sim_input                         true
% 3.70/1.00  --eq_ax_congr_red                       true
% 3.70/1.00  --pure_diseq_elim                       true
% 3.70/1.00  --brand_transform                       false
% 3.70/1.00  --non_eq_to_eq                          false
% 3.70/1.00  --prep_def_merge                        true
% 3.70/1.00  --prep_def_merge_prop_impl              false
% 3.70/1.00  --prep_def_merge_mbd                    true
% 3.70/1.00  --prep_def_merge_tr_red                 false
% 3.70/1.00  --prep_def_merge_tr_cl                  false
% 3.70/1.00  --smt_preprocessing                     true
% 3.70/1.00  --smt_ac_axioms                         fast
% 3.70/1.00  --preprocessed_out                      false
% 3.70/1.00  --preprocessed_stats                    false
% 3.70/1.00  
% 3.70/1.00  ------ Abstraction refinement Options
% 3.70/1.00  
% 3.70/1.00  --abstr_ref                             []
% 3.70/1.00  --abstr_ref_prep                        false
% 3.70/1.00  --abstr_ref_until_sat                   false
% 3.70/1.00  --abstr_ref_sig_restrict                funpre
% 3.70/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.70/1.00  --abstr_ref_under                       []
% 3.70/1.00  
% 3.70/1.00  ------ SAT Options
% 3.70/1.00  
% 3.70/1.00  --sat_mode                              false
% 3.70/1.00  --sat_fm_restart_options                ""
% 3.70/1.00  --sat_gr_def                            false
% 3.70/1.00  --sat_epr_types                         true
% 3.70/1.00  --sat_non_cyclic_types                  false
% 3.70/1.00  --sat_finite_models                     false
% 3.70/1.00  --sat_fm_lemmas                         false
% 3.70/1.00  --sat_fm_prep                           false
% 3.70/1.00  --sat_fm_uc_incr                        true
% 3.70/1.00  --sat_out_model                         small
% 3.70/1.00  --sat_out_clauses                       false
% 3.70/1.00  
% 3.70/1.00  ------ QBF Options
% 3.70/1.00  
% 3.70/1.00  --qbf_mode                              false
% 3.70/1.00  --qbf_elim_univ                         false
% 3.70/1.00  --qbf_dom_inst                          none
% 3.70/1.00  --qbf_dom_pre_inst                      false
% 3.70/1.00  --qbf_sk_in                             false
% 3.70/1.00  --qbf_pred_elim                         true
% 3.70/1.00  --qbf_split                             512
% 3.70/1.00  
% 3.70/1.00  ------ BMC1 Options
% 3.70/1.00  
% 3.70/1.00  --bmc1_incremental                      false
% 3.70/1.00  --bmc1_axioms                           reachable_all
% 3.70/1.00  --bmc1_min_bound                        0
% 3.70/1.00  --bmc1_max_bound                        -1
% 3.70/1.00  --bmc1_max_bound_default                -1
% 3.70/1.00  --bmc1_symbol_reachability              true
% 3.70/1.00  --bmc1_property_lemmas                  false
% 3.70/1.00  --bmc1_k_induction                      false
% 3.70/1.00  --bmc1_non_equiv_states                 false
% 3.70/1.00  --bmc1_deadlock                         false
% 3.70/1.00  --bmc1_ucm                              false
% 3.70/1.00  --bmc1_add_unsat_core                   none
% 3.70/1.00  --bmc1_unsat_core_children              false
% 3.70/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.70/1.00  --bmc1_out_stat                         full
% 3.70/1.00  --bmc1_ground_init                      false
% 3.70/1.00  --bmc1_pre_inst_next_state              false
% 3.70/1.00  --bmc1_pre_inst_state                   false
% 3.70/1.00  --bmc1_pre_inst_reach_state             false
% 3.70/1.00  --bmc1_out_unsat_core                   false
% 3.70/1.00  --bmc1_aig_witness_out                  false
% 3.70/1.00  --bmc1_verbose                          false
% 3.70/1.00  --bmc1_dump_clauses_tptp                false
% 3.70/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.70/1.00  --bmc1_dump_file                        -
% 3.70/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.70/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.70/1.00  --bmc1_ucm_extend_mode                  1
% 3.70/1.00  --bmc1_ucm_init_mode                    2
% 3.70/1.00  --bmc1_ucm_cone_mode                    none
% 3.70/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.70/1.00  --bmc1_ucm_relax_model                  4
% 3.70/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.70/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.70/1.00  --bmc1_ucm_layered_model                none
% 3.70/1.00  --bmc1_ucm_max_lemma_size               10
% 3.70/1.00  
% 3.70/1.00  ------ AIG Options
% 3.70/1.00  
% 3.70/1.00  --aig_mode                              false
% 3.70/1.00  
% 3.70/1.00  ------ Instantiation Options
% 3.70/1.00  
% 3.70/1.00  --instantiation_flag                    true
% 3.70/1.00  --inst_sos_flag                         true
% 3.70/1.00  --inst_sos_phase                        true
% 3.70/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.70/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.70/1.00  --inst_lit_sel_side                     num_symb
% 3.70/1.00  --inst_solver_per_active                1400
% 3.70/1.00  --inst_solver_calls_frac                1.
% 3.70/1.00  --inst_passive_queue_type               priority_queues
% 3.70/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.70/1.00  --inst_passive_queues_freq              [25;2]
% 3.70/1.00  --inst_dismatching                      true
% 3.70/1.00  --inst_eager_unprocessed_to_passive     true
% 3.70/1.00  --inst_prop_sim_given                   true
% 3.70/1.00  --inst_prop_sim_new                     false
% 3.70/1.00  --inst_subs_new                         false
% 3.70/1.00  --inst_eq_res_simp                      false
% 3.70/1.00  --inst_subs_given                       false
% 3.70/1.00  --inst_orphan_elimination               true
% 3.70/1.00  --inst_learning_loop_flag               true
% 3.70/1.00  --inst_learning_start                   3000
% 3.70/1.00  --inst_learning_factor                  2
% 3.70/1.00  --inst_start_prop_sim_after_learn       3
% 3.70/1.00  --inst_sel_renew                        solver
% 3.70/1.00  --inst_lit_activity_flag                true
% 3.70/1.00  --inst_restr_to_given                   false
% 3.70/1.00  --inst_activity_threshold               500
% 3.70/1.00  --inst_out_proof                        true
% 3.70/1.00  
% 3.70/1.00  ------ Resolution Options
% 3.70/1.00  
% 3.70/1.00  --resolution_flag                       true
% 3.70/1.00  --res_lit_sel                           adaptive
% 3.70/1.00  --res_lit_sel_side                      none
% 3.70/1.00  --res_ordering                          kbo
% 3.70/1.00  --res_to_prop_solver                    active
% 3.70/1.00  --res_prop_simpl_new                    false
% 3.70/1.00  --res_prop_simpl_given                  true
% 3.70/1.00  --res_passive_queue_type                priority_queues
% 3.70/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.70/1.00  --res_passive_queues_freq               [15;5]
% 3.70/1.00  --res_forward_subs                      full
% 3.70/1.00  --res_backward_subs                     full
% 3.70/1.00  --res_forward_subs_resolution           true
% 3.70/1.00  --res_backward_subs_resolution          true
% 3.70/1.00  --res_orphan_elimination                true
% 3.70/1.00  --res_time_limit                        2.
% 3.70/1.00  --res_out_proof                         true
% 3.70/1.00  
% 3.70/1.00  ------ Superposition Options
% 3.70/1.00  
% 3.70/1.00  --superposition_flag                    true
% 3.70/1.00  --sup_passive_queue_type                priority_queues
% 3.70/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.70/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.70/1.00  --demod_completeness_check              fast
% 3.70/1.00  --demod_use_ground                      true
% 3.70/1.00  --sup_to_prop_solver                    passive
% 3.70/1.00  --sup_prop_simpl_new                    true
% 3.70/1.00  --sup_prop_simpl_given                  true
% 3.70/1.00  --sup_fun_splitting                     true
% 3.70/1.00  --sup_smt_interval                      50000
% 3.70/1.00  
% 3.70/1.00  ------ Superposition Simplification Setup
% 3.70/1.00  
% 3.70/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.70/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.70/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.70/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.70/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.70/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.70/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.70/1.00  --sup_immed_triv                        [TrivRules]
% 3.70/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/1.00  --sup_immed_bw_main                     []
% 3.70/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.70/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.70/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/1.00  --sup_input_bw                          []
% 3.70/1.00  
% 3.70/1.00  ------ Combination Options
% 3.70/1.00  
% 3.70/1.00  --comb_res_mult                         3
% 3.70/1.00  --comb_sup_mult                         2
% 3.70/1.00  --comb_inst_mult                        10
% 3.70/1.00  
% 3.70/1.00  ------ Debug Options
% 3.70/1.00  
% 3.70/1.00  --dbg_backtrace                         false
% 3.70/1.00  --dbg_dump_prop_clauses                 false
% 3.70/1.00  --dbg_dump_prop_clauses_file            -
% 3.70/1.00  --dbg_out_stat                          false
% 3.70/1.00  ------ Parsing...
% 3.70/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.70/1.00  
% 3.70/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.70/1.00  
% 3.70/1.00  ------ Preprocessing... gs_s  sp: 6 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.70/1.00  
% 3.70/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/1.00  ------ Proving...
% 3.70/1.00  ------ Problem Properties 
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  clauses                                 40
% 3.70/1.00  conjectures                             3
% 3.70/1.00  EPR                                     1
% 3.70/1.00  Horn                                    27
% 3.70/1.00  unary                                   5
% 3.70/1.00  binary                                  8
% 3.70/1.00  lits                                    108
% 3.70/1.00  lits eq                                 24
% 3.70/1.00  fd_pure                                 0
% 3.70/1.00  fd_pseudo                               0
% 3.70/1.00  fd_cond                                 4
% 3.70/1.00  fd_pseudo_cond                          0
% 3.70/1.00  AC symbols                              0
% 3.70/1.00  
% 3.70/1.00  ------ Schedule dynamic 5 is on 
% 3.70/1.00  
% 3.70/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  ------ 
% 3.70/1.00  Current options:
% 3.70/1.00  ------ 
% 3.70/1.00  
% 3.70/1.00  ------ Input Options
% 3.70/1.00  
% 3.70/1.00  --out_options                           all
% 3.70/1.00  --tptp_safe_out                         true
% 3.70/1.00  --problem_path                          ""
% 3.70/1.00  --include_path                          ""
% 3.70/1.00  --clausifier                            res/vclausify_rel
% 3.70/1.00  --clausifier_options                    ""
% 3.70/1.00  --stdin                                 false
% 3.70/1.00  --stats_out                             all
% 3.70/1.00  
% 3.70/1.00  ------ General Options
% 3.70/1.00  
% 3.70/1.00  --fof                                   false
% 3.70/1.00  --time_out_real                         305.
% 3.70/1.00  --time_out_virtual                      -1.
% 3.70/1.00  --symbol_type_check                     false
% 3.70/1.00  --clausify_out                          false
% 3.70/1.00  --sig_cnt_out                           false
% 3.70/1.00  --trig_cnt_out                          false
% 3.70/1.00  --trig_cnt_out_tolerance                1.
% 3.70/1.00  --trig_cnt_out_sk_spl                   false
% 3.70/1.00  --abstr_cl_out                          false
% 3.70/1.00  
% 3.70/1.00  ------ Global Options
% 3.70/1.00  
% 3.70/1.00  --schedule                              default
% 3.70/1.00  --add_important_lit                     false
% 3.70/1.00  --prop_solver_per_cl                    1000
% 3.70/1.00  --min_unsat_core                        false
% 3.70/1.00  --soft_assumptions                      false
% 3.70/1.00  --soft_lemma_size                       3
% 3.70/1.00  --prop_impl_unit_size                   0
% 3.70/1.00  --prop_impl_unit                        []
% 3.70/1.00  --share_sel_clauses                     true
% 3.70/1.00  --reset_solvers                         false
% 3.70/1.00  --bc_imp_inh                            [conj_cone]
% 3.70/1.00  --conj_cone_tolerance                   3.
% 3.70/1.00  --extra_neg_conj                        none
% 3.70/1.00  --large_theory_mode                     true
% 3.70/1.00  --prolific_symb_bound                   200
% 3.70/1.00  --lt_threshold                          2000
% 3.70/1.00  --clause_weak_htbl                      true
% 3.70/1.00  --gc_record_bc_elim                     false
% 3.70/1.00  
% 3.70/1.00  ------ Preprocessing Options
% 3.70/1.00  
% 3.70/1.00  --preprocessing_flag                    true
% 3.70/1.00  --time_out_prep_mult                    0.1
% 3.70/1.00  --splitting_mode                        input
% 3.70/1.00  --splitting_grd                         true
% 3.70/1.00  --splitting_cvd                         false
% 3.70/1.00  --splitting_cvd_svl                     false
% 3.70/1.00  --splitting_nvd                         32
% 3.70/1.00  --sub_typing                            true
% 3.70/1.00  --prep_gs_sim                           true
% 3.70/1.00  --prep_unflatten                        true
% 3.70/1.00  --prep_res_sim                          true
% 3.70/1.00  --prep_upred                            true
% 3.70/1.00  --prep_sem_filter                       exhaustive
% 3.70/1.00  --prep_sem_filter_out                   false
% 3.70/1.00  --pred_elim                             true
% 3.70/1.00  --res_sim_input                         true
% 3.70/1.00  --eq_ax_congr_red                       true
% 3.70/1.00  --pure_diseq_elim                       true
% 3.70/1.00  --brand_transform                       false
% 3.70/1.00  --non_eq_to_eq                          false
% 3.70/1.00  --prep_def_merge                        true
% 3.70/1.00  --prep_def_merge_prop_impl              false
% 3.70/1.00  --prep_def_merge_mbd                    true
% 3.70/1.00  --prep_def_merge_tr_red                 false
% 3.70/1.00  --prep_def_merge_tr_cl                  false
% 3.70/1.00  --smt_preprocessing                     true
% 3.70/1.00  --smt_ac_axioms                         fast
% 3.70/1.00  --preprocessed_out                      false
% 3.70/1.00  --preprocessed_stats                    false
% 3.70/1.00  
% 3.70/1.00  ------ Abstraction refinement Options
% 3.70/1.00  
% 3.70/1.00  --abstr_ref                             []
% 3.70/1.00  --abstr_ref_prep                        false
% 3.70/1.00  --abstr_ref_until_sat                   false
% 3.70/1.00  --abstr_ref_sig_restrict                funpre
% 3.70/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.70/1.00  --abstr_ref_under                       []
% 3.70/1.00  
% 3.70/1.00  ------ SAT Options
% 3.70/1.00  
% 3.70/1.00  --sat_mode                              false
% 3.70/1.00  --sat_fm_restart_options                ""
% 3.70/1.00  --sat_gr_def                            false
% 3.70/1.00  --sat_epr_types                         true
% 3.70/1.00  --sat_non_cyclic_types                  false
% 3.70/1.00  --sat_finite_models                     false
% 3.70/1.00  --sat_fm_lemmas                         false
% 3.70/1.00  --sat_fm_prep                           false
% 3.70/1.00  --sat_fm_uc_incr                        true
% 3.70/1.00  --sat_out_model                         small
% 3.70/1.00  --sat_out_clauses                       false
% 3.70/1.00  
% 3.70/1.00  ------ QBF Options
% 3.70/1.00  
% 3.70/1.00  --qbf_mode                              false
% 3.70/1.00  --qbf_elim_univ                         false
% 3.70/1.00  --qbf_dom_inst                          none
% 3.70/1.00  --qbf_dom_pre_inst                      false
% 3.70/1.00  --qbf_sk_in                             false
% 3.70/1.00  --qbf_pred_elim                         true
% 3.70/1.00  --qbf_split                             512
% 3.70/1.00  
% 3.70/1.00  ------ BMC1 Options
% 3.70/1.00  
% 3.70/1.00  --bmc1_incremental                      false
% 3.70/1.00  --bmc1_axioms                           reachable_all
% 3.70/1.00  --bmc1_min_bound                        0
% 3.70/1.00  --bmc1_max_bound                        -1
% 3.70/1.00  --bmc1_max_bound_default                -1
% 3.70/1.00  --bmc1_symbol_reachability              true
% 3.70/1.00  --bmc1_property_lemmas                  false
% 3.70/1.00  --bmc1_k_induction                      false
% 3.70/1.00  --bmc1_non_equiv_states                 false
% 3.70/1.00  --bmc1_deadlock                         false
% 3.70/1.00  --bmc1_ucm                              false
% 3.70/1.00  --bmc1_add_unsat_core                   none
% 3.70/1.00  --bmc1_unsat_core_children              false
% 3.70/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.70/1.00  --bmc1_out_stat                         full
% 3.70/1.00  --bmc1_ground_init                      false
% 3.70/1.00  --bmc1_pre_inst_next_state              false
% 3.70/1.00  --bmc1_pre_inst_state                   false
% 3.70/1.00  --bmc1_pre_inst_reach_state             false
% 3.70/1.00  --bmc1_out_unsat_core                   false
% 3.70/1.00  --bmc1_aig_witness_out                  false
% 3.70/1.00  --bmc1_verbose                          false
% 3.70/1.00  --bmc1_dump_clauses_tptp                false
% 3.70/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.70/1.00  --bmc1_dump_file                        -
% 3.70/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.70/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.70/1.00  --bmc1_ucm_extend_mode                  1
% 3.70/1.00  --bmc1_ucm_init_mode                    2
% 3.70/1.00  --bmc1_ucm_cone_mode                    none
% 3.70/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.70/1.00  --bmc1_ucm_relax_model                  4
% 3.70/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.70/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.70/1.00  --bmc1_ucm_layered_model                none
% 3.70/1.00  --bmc1_ucm_max_lemma_size               10
% 3.70/1.00  
% 3.70/1.00  ------ AIG Options
% 3.70/1.00  
% 3.70/1.00  --aig_mode                              false
% 3.70/1.00  
% 3.70/1.00  ------ Instantiation Options
% 3.70/1.00  
% 3.70/1.00  --instantiation_flag                    true
% 3.70/1.00  --inst_sos_flag                         true
% 3.70/1.00  --inst_sos_phase                        true
% 3.70/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.70/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.70/1.00  --inst_lit_sel_side                     none
% 3.70/1.00  --inst_solver_per_active                1400
% 3.70/1.00  --inst_solver_calls_frac                1.
% 3.70/1.00  --inst_passive_queue_type               priority_queues
% 3.70/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.70/1.00  --inst_passive_queues_freq              [25;2]
% 3.70/1.00  --inst_dismatching                      true
% 3.70/1.00  --inst_eager_unprocessed_to_passive     true
% 3.70/1.00  --inst_prop_sim_given                   true
% 3.70/1.00  --inst_prop_sim_new                     false
% 3.70/1.00  --inst_subs_new                         false
% 3.70/1.00  --inst_eq_res_simp                      false
% 3.70/1.00  --inst_subs_given                       false
% 3.70/1.00  --inst_orphan_elimination               true
% 3.70/1.00  --inst_learning_loop_flag               true
% 3.70/1.00  --inst_learning_start                   3000
% 3.70/1.00  --inst_learning_factor                  2
% 3.70/1.00  --inst_start_prop_sim_after_learn       3
% 3.70/1.00  --inst_sel_renew                        solver
% 3.70/1.00  --inst_lit_activity_flag                true
% 3.70/1.00  --inst_restr_to_given                   false
% 3.70/1.00  --inst_activity_threshold               500
% 3.70/1.00  --inst_out_proof                        true
% 3.70/1.00  
% 3.70/1.00  ------ Resolution Options
% 3.70/1.00  
% 3.70/1.00  --resolution_flag                       false
% 3.70/1.00  --res_lit_sel                           adaptive
% 3.70/1.00  --res_lit_sel_side                      none
% 3.70/1.00  --res_ordering                          kbo
% 3.70/1.00  --res_to_prop_solver                    active
% 3.70/1.00  --res_prop_simpl_new                    false
% 3.70/1.00  --res_prop_simpl_given                  true
% 3.70/1.00  --res_passive_queue_type                priority_queues
% 3.70/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.70/1.00  --res_passive_queues_freq               [15;5]
% 3.70/1.00  --res_forward_subs                      full
% 3.70/1.00  --res_backward_subs                     full
% 3.70/1.00  --res_forward_subs_resolution           true
% 3.70/1.00  --res_backward_subs_resolution          true
% 3.70/1.00  --res_orphan_elimination                true
% 3.70/1.00  --res_time_limit                        2.
% 3.70/1.00  --res_out_proof                         true
% 3.70/1.00  
% 3.70/1.00  ------ Superposition Options
% 3.70/1.00  
% 3.70/1.00  --superposition_flag                    true
% 3.70/1.00  --sup_passive_queue_type                priority_queues
% 3.70/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.70/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.70/1.00  --demod_completeness_check              fast
% 3.70/1.00  --demod_use_ground                      true
% 3.70/1.00  --sup_to_prop_solver                    passive
% 3.70/1.00  --sup_prop_simpl_new                    true
% 3.70/1.00  --sup_prop_simpl_given                  true
% 3.70/1.00  --sup_fun_splitting                     true
% 3.70/1.00  --sup_smt_interval                      50000
% 3.70/1.00  
% 3.70/1.00  ------ Superposition Simplification Setup
% 3.70/1.00  
% 3.70/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.70/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.70/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.70/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.70/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.70/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.70/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.70/1.00  --sup_immed_triv                        [TrivRules]
% 3.70/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/1.00  --sup_immed_bw_main                     []
% 3.70/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.70/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.70/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/1.00  --sup_input_bw                          []
% 3.70/1.00  
% 3.70/1.00  ------ Combination Options
% 3.70/1.00  
% 3.70/1.00  --comb_res_mult                         3
% 3.70/1.00  --comb_sup_mult                         2
% 3.70/1.00  --comb_inst_mult                        10
% 3.70/1.00  
% 3.70/1.00  ------ Debug Options
% 3.70/1.00  
% 3.70/1.00  --dbg_backtrace                         false
% 3.70/1.00  --dbg_dump_prop_clauses                 false
% 3.70/1.00  --dbg_dump_prop_clauses_file            -
% 3.70/1.00  --dbg_out_stat                          false
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  ------ Proving...
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  % SZS status Theorem for theBenchmark.p
% 3.70/1.00  
% 3.70/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.70/1.00  
% 3.70/1.00  fof(f1,axiom,(
% 3.70/1.00    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f41,plain,(
% 3.70/1.00    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.70/1.00    inference(nnf_transformation,[],[f1])).
% 3.70/1.00  
% 3.70/1.00  fof(f42,plain,(
% 3.70/1.00    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.70/1.00    inference(flattening,[],[f41])).
% 3.70/1.00  
% 3.70/1.00  fof(f54,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 3.70/1.00    inference(cnf_transformation,[],[f42])).
% 3.70/1.00  
% 3.70/1.00  fof(f93,plain,(
% 3.70/1.00    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.70/1.00    inference(equality_resolution,[],[f54])).
% 3.70/1.00  
% 3.70/1.00  fof(f16,conjecture,(
% 3.70/1.00    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f17,negated_conjecture,(
% 3.70/1.00    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 3.70/1.00    inference(negated_conjecture,[],[f16])).
% 3.70/1.00  
% 3.70/1.00  fof(f39,plain,(
% 3.70/1.00    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 3.70/1.00    inference(ennf_transformation,[],[f17])).
% 3.70/1.00  
% 3.70/1.00  fof(f40,plain,(
% 3.70/1.00    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 3.70/1.00    inference(flattening,[],[f39])).
% 3.70/1.00  
% 3.70/1.00  fof(f50,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (~r1_tarski(k2_relset_1(X1,X2,sK4),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,sK4,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 3.70/1.00    introduced(choice_axiom,[])).
% 3.70/1.00  
% 3.70/1.00  fof(f49,plain,(
% 3.70/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (~r1_tarski(k2_relset_1(X1,sK3,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,sK3,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK3))) & v1_funct_2(X3,X1,sK3) & v1_funct_1(X3)) & ~v1_xboole_0(sK3))) )),
% 3.70/1.00    introduced(choice_axiom,[])).
% 3.70/1.00  
% 3.70/1.00  fof(f48,plain,(
% 3.70/1.00    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK2,X2,X3),sK1) & ! [X4] : (r2_hidden(k3_funct_2(sK2,X2,X3,X4),sK1) | ~m1_subset_1(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X2))) & v1_funct_2(X3,sK2,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK2))),
% 3.70/1.00    introduced(choice_axiom,[])).
% 3.70/1.00  
% 3.70/1.00  fof(f51,plain,(
% 3.70/1.00    ((~r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) & ! [X4] : (r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1) | ~m1_subset_1(X4,sK2)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 3.70/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f40,f50,f49,f48])).
% 3.70/1.00  
% 3.70/1.00  fof(f90,plain,(
% 3.70/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.70/1.00    inference(cnf_transformation,[],[f51])).
% 3.70/1.00  
% 3.70/1.00  fof(f12,axiom,(
% 3.70/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f31,plain,(
% 3.70/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.70/1.00    inference(ennf_transformation,[],[f12])).
% 3.70/1.00  
% 3.70/1.00  fof(f32,plain,(
% 3.70/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.70/1.00    inference(flattening,[],[f31])).
% 3.70/1.00  
% 3.70/1.00  fof(f45,plain,(
% 3.70/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.70/1.00    inference(nnf_transformation,[],[f32])).
% 3.70/1.00  
% 3.70/1.00  fof(f70,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.70/1.00    inference(cnf_transformation,[],[f45])).
% 3.70/1.00  
% 3.70/1.00  fof(f7,axiom,(
% 3.70/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f23,plain,(
% 3.70/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.70/1.00    inference(ennf_transformation,[],[f7])).
% 3.70/1.00  
% 3.70/1.00  fof(f63,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.70/1.00    inference(cnf_transformation,[],[f23])).
% 3.70/1.00  
% 3.70/1.00  fof(f89,plain,(
% 3.70/1.00    v1_funct_2(sK4,sK2,sK3)),
% 3.70/1.00    inference(cnf_transformation,[],[f51])).
% 3.70/1.00  
% 3.70/1.00  fof(f2,axiom,(
% 3.70/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f18,plain,(
% 3.70/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.70/1.00    inference(ennf_transformation,[],[f2])).
% 3.70/1.00  
% 3.70/1.00  fof(f55,plain,(
% 3.70/1.00    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f18])).
% 3.70/1.00  
% 3.70/1.00  fof(f15,axiom,(
% 3.70/1.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f37,plain,(
% 3.70/1.00    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.70/1.00    inference(ennf_transformation,[],[f15])).
% 3.70/1.00  
% 3.70/1.00  fof(f38,plain,(
% 3.70/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.70/1.00    inference(flattening,[],[f37])).
% 3.70/1.00  
% 3.70/1.00  fof(f46,plain,(
% 3.70/1.00    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),X0)))),
% 3.70/1.00    introduced(choice_axiom,[])).
% 3.70/1.00  
% 3.70/1.00  fof(f47,plain,(
% 3.70/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.70/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f46])).
% 3.70/1.00  
% 3.70/1.00  fof(f84,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK0(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f47])).
% 3.70/1.00  
% 3.70/1.00  fof(f101,plain,(
% 3.70/1.00    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.70/1.00    inference(equality_resolution,[],[f84])).
% 3.70/1.00  
% 3.70/1.00  fof(f88,plain,(
% 3.70/1.00    v1_funct_1(sK4)),
% 3.70/1.00    inference(cnf_transformation,[],[f51])).
% 3.70/1.00  
% 3.70/1.00  fof(f5,axiom,(
% 3.70/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f21,plain,(
% 3.70/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.70/1.00    inference(ennf_transformation,[],[f5])).
% 3.70/1.00  
% 3.70/1.00  fof(f60,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.70/1.00    inference(cnf_transformation,[],[f21])).
% 3.70/1.00  
% 3.70/1.00  fof(f52,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 3.70/1.00    inference(cnf_transformation,[],[f42])).
% 3.70/1.00  
% 3.70/1.00  fof(f53,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 3.70/1.00    inference(cnf_transformation,[],[f42])).
% 3.70/1.00  
% 3.70/1.00  fof(f94,plain,(
% 3.70/1.00    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 3.70/1.00    inference(equality_resolution,[],[f53])).
% 3.70/1.00  
% 3.70/1.00  fof(f6,axiom,(
% 3.70/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f22,plain,(
% 3.70/1.00    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.70/1.00    inference(ennf_transformation,[],[f6])).
% 3.70/1.00  
% 3.70/1.00  fof(f62,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.70/1.00    inference(cnf_transformation,[],[f22])).
% 3.70/1.00  
% 3.70/1.00  fof(f4,axiom,(
% 3.70/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f20,plain,(
% 3.70/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.70/1.00    inference(ennf_transformation,[],[f4])).
% 3.70/1.00  
% 3.70/1.00  fof(f44,plain,(
% 3.70/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.70/1.00    inference(nnf_transformation,[],[f20])).
% 3.70/1.00  
% 3.70/1.00  fof(f58,plain,(
% 3.70/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f44])).
% 3.70/1.00  
% 3.70/1.00  fof(f14,axiom,(
% 3.70/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f35,plain,(
% 3.70/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.70/1.00    inference(ennf_transformation,[],[f14])).
% 3.70/1.00  
% 3.70/1.00  fof(f36,plain,(
% 3.70/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.70/1.00    inference(flattening,[],[f35])).
% 3.70/1.00  
% 3.70/1.00  fof(f79,plain,(
% 3.70/1.00    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f36])).
% 3.70/1.00  
% 3.70/1.00  fof(f61,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.70/1.00    inference(cnf_transformation,[],[f22])).
% 3.70/1.00  
% 3.70/1.00  fof(f3,axiom,(
% 3.70/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f19,plain,(
% 3.70/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.70/1.00    inference(ennf_transformation,[],[f3])).
% 3.70/1.00  
% 3.70/1.00  fof(f43,plain,(
% 3.70/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.70/1.00    inference(nnf_transformation,[],[f19])).
% 3.70/1.00  
% 3.70/1.00  fof(f56,plain,(
% 3.70/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f43])).
% 3.70/1.00  
% 3.70/1.00  fof(f9,axiom,(
% 3.70/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f25,plain,(
% 3.70/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 3.70/1.00    inference(ennf_transformation,[],[f9])).
% 3.70/1.00  
% 3.70/1.00  fof(f26,plain,(
% 3.70/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.70/1.00    inference(flattening,[],[f25])).
% 3.70/1.00  
% 3.70/1.00  fof(f65,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f26])).
% 3.70/1.00  
% 3.70/1.00  fof(f11,axiom,(
% 3.70/1.00    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f29,plain,(
% 3.70/1.00    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.70/1.00    inference(ennf_transformation,[],[f11])).
% 3.70/1.00  
% 3.70/1.00  fof(f30,plain,(
% 3.70/1.00    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.70/1.00    inference(flattening,[],[f29])).
% 3.70/1.00  
% 3.70/1.00  fof(f69,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f30])).
% 3.70/1.00  
% 3.70/1.00  fof(f87,plain,(
% 3.70/1.00    ~v1_xboole_0(sK3)),
% 3.70/1.00    inference(cnf_transformation,[],[f51])).
% 3.70/1.00  
% 3.70/1.00  fof(f10,axiom,(
% 3.70/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f27,plain,(
% 3.70/1.00    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.70/1.00    inference(ennf_transformation,[],[f10])).
% 3.70/1.00  
% 3.70/1.00  fof(f28,plain,(
% 3.70/1.00    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.70/1.00    inference(flattening,[],[f27])).
% 3.70/1.00  
% 3.70/1.00  fof(f67,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.70/1.00    inference(cnf_transformation,[],[f28])).
% 3.70/1.00  
% 3.70/1.00  fof(f8,axiom,(
% 3.70/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f24,plain,(
% 3.70/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.70/1.00    inference(ennf_transformation,[],[f8])).
% 3.70/1.00  
% 3.70/1.00  fof(f64,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.70/1.00    inference(cnf_transformation,[],[f24])).
% 3.70/1.00  
% 3.70/1.00  fof(f92,plain,(
% 3.70/1.00    ~r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)),
% 3.70/1.00    inference(cnf_transformation,[],[f51])).
% 3.70/1.00  
% 3.70/1.00  fof(f82,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | r2_hidden(sK0(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f47])).
% 3.70/1.00  
% 3.70/1.00  fof(f103,plain,(
% 3.70/1.00    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.70/1.00    inference(equality_resolution,[],[f82])).
% 3.70/1.00  
% 3.70/1.00  fof(f85,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f47])).
% 3.70/1.00  
% 3.70/1.00  fof(f100,plain,(
% 3.70/1.00    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.70/1.00    inference(equality_resolution,[],[f85])).
% 3.70/1.00  
% 3.70/1.00  fof(f13,axiom,(
% 3.70/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f33,plain,(
% 3.70/1.00    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 3.70/1.00    inference(ennf_transformation,[],[f13])).
% 3.70/1.00  
% 3.70/1.00  fof(f34,plain,(
% 3.70/1.00    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 3.70/1.00    inference(flattening,[],[f33])).
% 3.70/1.00  
% 3.70/1.00  fof(f76,plain,(
% 3.70/1.00    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f34])).
% 3.70/1.00  
% 3.70/1.00  fof(f86,plain,(
% 3.70/1.00    ~v1_xboole_0(sK2)),
% 3.70/1.00    inference(cnf_transformation,[],[f51])).
% 3.70/1.00  
% 3.70/1.00  fof(f91,plain,(
% 3.70/1.00    ( ! [X4] : (r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1) | ~m1_subset_1(X4,sK2)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f51])).
% 3.70/1.00  
% 3.70/1.00  fof(f83,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f47])).
% 3.70/1.00  
% 3.70/1.00  fof(f102,plain,(
% 3.70/1.00    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | ~r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.70/1.00    inference(equality_resolution,[],[f83])).
% 3.70/1.00  
% 3.70/1.00  cnf(c_0,plain,
% 3.70/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.70/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_36,negated_conjecture,
% 3.70/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.70/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2588,plain,
% 3.70/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_23,plain,
% 3.70/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.70/1.00      | k1_xboole_0 = X2 ),
% 3.70/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2590,plain,
% 3.70/1.00      ( k1_relset_1(X0,X1,X2) = X0
% 3.70/1.00      | k1_xboole_0 = X1
% 3.70/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.70/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_4727,plain,
% 3.70/1.00      ( k1_relset_1(sK2,sK3,sK4) = sK2
% 3.70/1.00      | sK3 = k1_xboole_0
% 3.70/1.00      | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_2588,c_2590]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_11,plain,
% 3.70/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.70/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2598,plain,
% 3.70/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.70/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3742,plain,
% 3.70/1.00      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_2588,c_2598]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_4733,plain,
% 3.70/1.00      ( k1_relat_1(sK4) = sK2
% 3.70/1.00      | sK3 = k1_xboole_0
% 3.70/1.00      | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
% 3.70/1.00      inference(demodulation,[status(thm)],[c_4727,c_3742]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_37,negated_conjecture,
% 3.70/1.00      ( v1_funct_2(sK4,sK2,sK3) ),
% 3.70/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_44,plain,
% 3.70/1.00      ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_4738,plain,
% 3.70/1.00      ( sK3 = k1_xboole_0 | k1_relat_1(sK4) = sK2 ),
% 3.70/1.00      inference(global_propositional_subsumption,
% 3.70/1.00                [status(thm)],
% 3.70/1.00                [c_4733,c_44]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_4739,plain,
% 3.70/1.00      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 3.70/1.00      inference(renaming,[status(thm)],[c_4738]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3,plain,
% 3.70/1.00      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 3.70/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_29,plain,
% 3.70/1.00      ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 3.70/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.70/1.00      | ~ v1_funct_1(X0)
% 3.70/1.00      | ~ v1_relat_1(X0) ),
% 3.70/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_38,negated_conjecture,
% 3.70/1.00      ( v1_funct_1(sK4) ),
% 3.70/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_850,plain,
% 3.70/1.00      ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 3.70/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.70/1.00      | ~ v1_relat_1(X0)
% 3.70/1.00      | sK4 != X0 ),
% 3.70/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_38]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_851,plain,
% 3.70/1.00      ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 3.70/1.00      | ~ v1_relat_1(sK4) ),
% 3.70/1.00      inference(unflattening,[status(thm)],[c_850]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1132,plain,
% 3.70/1.00      ( m1_subset_1(X0,X1)
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X2)))
% 3.70/1.00      | ~ v1_relat_1(sK4)
% 3.70/1.00      | sK0(k1_relat_1(sK4),X2,sK4) != X0
% 3.70/1.00      | k1_relat_1(sK4) != X1 ),
% 3.70/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_851]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1133,plain,
% 3.70/1.00      ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 3.70/1.00      | ~ v1_relat_1(sK4) ),
% 3.70/1.00      inference(unflattening,[status(thm)],[c_1132]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2576,plain,
% 3.70/1.00      ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 3.70/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_1133]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_45,plain,
% 3.70/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1134,plain,
% 3.70/1.00      ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 3.70/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_1133]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_8,plain,
% 3.70/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/1.00      | v1_relat_1(X0) ),
% 3.70/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2674,plain,
% 3.70/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.70/1.00      | v1_relat_1(sK4) ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2761,plain,
% 3.70/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.70/1.00      | v1_relat_1(sK4) ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_2674]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2762,plain,
% 3.70/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.70/1.00      | v1_relat_1(sK4) = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_2761]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_4928,plain,
% 3.70/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 3.70/1.00      | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top ),
% 3.70/1.00      inference(global_propositional_subsumption,
% 3.70/1.00                [status(thm)],
% 3.70/1.00                [c_2576,c_45,c_1134,c_2762]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_4929,plain,
% 3.70/1.00      ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
% 3.70/1.00      inference(renaming,[status(thm)],[c_4928]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_4934,plain,
% 3.70/1.00      ( sK3 = k1_xboole_0
% 3.70/1.00      | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_4739,c_4929]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_8218,plain,
% 3.70/1.00      ( sK3 = k1_xboole_0
% 3.70/1.00      | m1_subset_1(sK0(sK2,k1_xboole_0,sK4),sK2) = iProver_top
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_0,c_4934]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2,plain,
% 3.70/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.70/1.00      | k1_xboole_0 = X1
% 3.70/1.00      | k1_xboole_0 = X0 ),
% 3.70/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_133,plain,
% 3.70/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.70/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1,plain,
% 3.70/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.70/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_134,plain,
% 3.70/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_9,plain,
% 3.70/1.00      ( v5_relat_1(X0,X1)
% 3.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.70/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_7,plain,
% 3.70/1.00      ( ~ v5_relat_1(X0,X1)
% 3.70/1.00      | r1_tarski(k2_relat_1(X0),X1)
% 3.70/1.00      | ~ v1_relat_1(X0) ),
% 3.70/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_420,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(X0),X1)
% 3.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.70/1.00      | ~ v1_relat_1(X0) ),
% 3.70/1.00      inference(resolution,[status(thm)],[c_9,c_7]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_430,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(X0),X1)
% 3.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.70/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_420,c_8]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2896,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(sK4),X0)
% 3.70/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_430]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3062,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(sK4),sK3)
% 3.70/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_2896]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3063,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_3062]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1977,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3304,plain,
% 3.70/1.00      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_1977]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3305,plain,
% 3.70/1.00      ( sK3 != k1_xboole_0
% 3.70/1.00      | k1_xboole_0 = sK3
% 3.70/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_3304]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1981,plain,
% 3.70/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.70/1.00      theory(equality) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2939,plain,
% 3.70/1.00      ( r1_tarski(X0,X1)
% 3.70/1.00      | ~ r1_tarski(k2_relat_1(X2),X3)
% 3.70/1.00      | X1 != X3
% 3.70/1.00      | X0 != k2_relat_1(X2) ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_1981]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3213,plain,
% 3.70/1.00      ( r1_tarski(X0,X1)
% 3.70/1.00      | ~ r1_tarski(k2_relat_1(sK4),sK3)
% 3.70/1.00      | X0 != k2_relat_1(sK4)
% 3.70/1.00      | X1 != sK3 ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_2939]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_4348,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(sK4),X0)
% 3.70/1.00      | ~ r1_tarski(k2_relat_1(sK4),sK3)
% 3.70/1.00      | X0 != sK3
% 3.70/1.00      | k2_relat_1(sK4) != k2_relat_1(sK4) ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_3213]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_4349,plain,
% 3.70/1.00      ( X0 != sK3
% 3.70/1.00      | k2_relat_1(sK4) != k2_relat_1(sK4)
% 3.70/1.00      | r1_tarski(k2_relat_1(sK4),X0) = iProver_top
% 3.70/1.00      | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_4348]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_4351,plain,
% 3.70/1.00      ( k2_relat_1(sK4) != k2_relat_1(sK4)
% 3.70/1.00      | k1_xboole_0 != sK3
% 3.70/1.00      | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
% 3.70/1.00      | r1_tarski(k2_relat_1(sK4),k1_xboole_0) = iProver_top ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_4349]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1976,plain,( X0 = X0 ),theory(equality) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_4988,plain,
% 3.70/1.00      ( k2_relat_1(sK4) = k2_relat_1(sK4) ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_1976]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_25,plain,
% 3.70/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.70/1.00      | ~ v1_funct_1(X0)
% 3.70/1.00      | ~ v1_relat_1(X0) ),
% 3.70/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_890,plain,
% 3.70/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.70/1.00      | ~ v1_relat_1(X0)
% 3.70/1.00      | sK4 != X0 ),
% 3.70/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_38]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_891,plain,
% 3.70/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))))
% 3.70/1.00      | ~ v1_relat_1(sK4) ),
% 3.70/1.00      inference(unflattening,[status(thm)],[c_890]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2579,plain,
% 3.70/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) = iProver_top
% 3.70/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_891]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_892,plain,
% 3.70/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) = iProver_top
% 3.70/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_891]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2783,plain,
% 3.70/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) = iProver_top ),
% 3.70/1.00      inference(global_propositional_subsumption,
% 3.70/1.00                [status(thm)],
% 3.70/1.00                [c_2579,c_45,c_892,c_2762]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_10,plain,
% 3.70/1.00      ( v4_relat_1(X0,X1)
% 3.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.70/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_5,plain,
% 3.70/1.00      ( r1_tarski(k1_relat_1(X0),X1)
% 3.70/1.00      | ~ v4_relat_1(X0,X1)
% 3.70/1.00      | ~ v1_relat_1(X0) ),
% 3.70/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_399,plain,
% 3.70/1.00      ( r1_tarski(k1_relat_1(X0),X1)
% 3.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/1.00      | ~ v1_relat_1(X0) ),
% 3.70/1.00      inference(resolution,[status(thm)],[c_10,c_5]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_403,plain,
% 3.70/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/1.00      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.70/1.00      inference(global_propositional_subsumption,
% 3.70/1.00                [status(thm)],
% 3.70/1.00                [c_399,c_10,c_8,c_5]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_404,plain,
% 3.70/1.00      ( r1_tarski(k1_relat_1(X0),X1)
% 3.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.70/1.00      inference(renaming,[status(thm)],[c_403]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2586,plain,
% 3.70/1.00      ( r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.70/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_404]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_5610,plain,
% 3.70/1.00      ( r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) = iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_2783,c_2586]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_13,plain,
% 3.70/1.00      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.70/1.00      | ~ r1_tarski(k1_relat_1(X0),X2)
% 3.70/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.70/1.00      | ~ v1_relat_1(X0) ),
% 3.70/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2596,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.70/1.00      | r1_tarski(k1_relat_1(X0),X2) != iProver_top
% 3.70/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
% 3.70/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_5147,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 3.70/1.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.70/1.00      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.70/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_0,c_2596]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_5895,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.70/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_5610,c_5147]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_6170,plain,
% 3.70/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.70/1.00      | r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top ),
% 3.70/1.00      inference(global_propositional_subsumption,
% 3.70/1.00                [status(thm)],
% 3.70/1.00                [c_5895,c_45,c_2762]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_6171,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.70/1.00      inference(renaming,[status(thm)],[c_6170]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_8528,plain,
% 3.70/1.00      ( m1_subset_1(sK0(sK2,k1_xboole_0,sK4),sK2) = iProver_top
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.70/1.00      inference(global_propositional_subsumption,
% 3.70/1.00                [status(thm)],
% 3.70/1.00                [c_8218,c_45,c_133,c_134,c_3063,c_3305,c_4351,c_4988,
% 3.70/1.00                 c_6171]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_4758,plain,
% 3.70/1.00      ( sK3 = k1_xboole_0
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK4)))) = iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_4739,c_2783]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3065,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(sK4),X0)
% 3.70/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_2896]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3162,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(sK4),k2_relat_1(sK4))
% 3.70/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_3065]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3163,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(sK4),k2_relat_1(sK4)) = iProver_top
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_3162]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3239,plain,
% 3.70/1.00      ( r1_tarski(k1_relat_1(sK4),sK2)
% 3.70/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_404]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3240,plain,
% 3.70/1.00      ( r1_tarski(k1_relat_1(sK4),sK2) = iProver_top
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_3239]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2764,plain,
% 3.70/1.00      ( ~ r1_tarski(k2_relat_1(sK4),X0)
% 3.70/1.00      | ~ r1_tarski(k1_relat_1(sK4),X1)
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.70/1.00      | ~ v1_relat_1(sK4) ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3260,plain,
% 3.70/1.00      ( ~ r1_tarski(k2_relat_1(sK4),k2_relat_1(sK4))
% 3.70/1.00      | ~ r1_tarski(k1_relat_1(sK4),X0)
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
% 3.70/1.00      | ~ v1_relat_1(sK4) ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_2764]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3796,plain,
% 3.70/1.00      ( ~ r1_tarski(k2_relat_1(sK4),k2_relat_1(sK4))
% 3.70/1.00      | ~ r1_tarski(k1_relat_1(sK4),sK2)
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK4))))
% 3.70/1.00      | ~ v1_relat_1(sK4) ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_3260]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3797,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(sK4),k2_relat_1(sK4)) != iProver_top
% 3.70/1.00      | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK4)))) = iProver_top
% 3.70/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_3796]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_4842,plain,
% 3.70/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK4)))) = iProver_top ),
% 3.70/1.00      inference(global_propositional_subsumption,
% 3.70/1.00                [status(thm)],
% 3.70/1.00                [c_4758,c_45,c_892,c_2762,c_3163,c_3240,c_3797]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_4846,plain,
% 3.70/1.00      ( k1_relset_1(sK2,k2_relat_1(sK4),sK4) = sK2
% 3.70/1.00      | k2_relat_1(sK4) = k1_xboole_0
% 3.70/1.00      | v1_funct_2(sK4,sK2,k2_relat_1(sK4)) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_4842,c_2590]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_4847,plain,
% 3.70/1.00      ( k1_relset_1(sK2,k2_relat_1(sK4),sK4) = k1_relat_1(sK4) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_4842,c_2598]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_4852,plain,
% 3.70/1.00      ( k2_relat_1(sK4) = k1_xboole_0
% 3.70/1.00      | k1_relat_1(sK4) = sK2
% 3.70/1.00      | v1_funct_2(sK4,sK2,k2_relat_1(sK4)) != iProver_top ),
% 3.70/1.00      inference(demodulation,[status(thm)],[c_4846,c_4847]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_16,plain,
% 3.70/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.70/1.00      | v1_partfun1(X0,X1)
% 3.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/1.00      | v1_xboole_0(X2)
% 3.70/1.00      | ~ v1_funct_1(X0) ),
% 3.70/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_39,negated_conjecture,
% 3.70/1.00      ( ~ v1_xboole_0(sK3) ),
% 3.70/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_509,plain,
% 3.70/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.70/1.00      | v1_partfun1(X0,X1)
% 3.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/1.00      | ~ v1_funct_1(X0)
% 3.70/1.00      | sK3 != X2 ),
% 3.70/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_39]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_510,plain,
% 3.70/1.00      ( ~ v1_funct_2(X0,X1,sK3)
% 3.70/1.00      | v1_partfun1(X0,X1)
% 3.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
% 3.70/1.00      | ~ v1_funct_1(X0) ),
% 3.70/1.00      inference(unflattening,[status(thm)],[c_509]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_769,plain,
% 3.70/1.00      ( ~ v1_funct_2(X0,X1,sK3)
% 3.70/1.00      | v1_partfun1(X0,X1)
% 3.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
% 3.70/1.00      | sK4 != X0 ),
% 3.70/1.00      inference(resolution_lifted,[status(thm)],[c_510,c_38]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_770,plain,
% 3.70/1.00      ( ~ v1_funct_2(sK4,X0,sK3)
% 3.70/1.00      | v1_partfun1(sK4,X0)
% 3.70/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) ),
% 3.70/1.00      inference(unflattening,[status(thm)],[c_769]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2700,plain,
% 3.70/1.00      ( ~ v1_funct_2(sK4,sK2,sK3)
% 3.70/1.00      | v1_partfun1(sK4,sK2)
% 3.70/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_770]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_14,plain,
% 3.70/1.00      ( v1_funct_2(X0,X1,X2)
% 3.70/1.00      | ~ v1_partfun1(X0,X1)
% 3.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/1.00      | ~ v1_funct_1(X0) ),
% 3.70/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_900,plain,
% 3.70/1.00      ( v1_funct_2(X0,X1,X2)
% 3.70/1.00      | ~ v1_partfun1(X0,X1)
% 3.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/1.00      | sK4 != X0 ),
% 3.70/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_38]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_901,plain,
% 3.70/1.00      ( v1_funct_2(sK4,X0,X1)
% 3.70/1.00      | ~ v1_partfun1(sK4,X0)
% 3.70/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.70/1.00      inference(unflattening,[status(thm)],[c_900]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2736,plain,
% 3.70/1.00      ( v1_funct_2(sK4,sK2,X0)
% 3.70/1.00      | ~ v1_partfun1(sK4,sK2)
% 3.70/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_901]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_4308,plain,
% 3.70/1.00      ( v1_funct_2(sK4,sK2,k2_relat_1(sK4))
% 3.70/1.00      | ~ v1_partfun1(sK4,sK2)
% 3.70/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK4)))) ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_2736]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_4857,plain,
% 3.70/1.00      ( ~ v1_funct_2(sK4,sK2,k2_relat_1(sK4))
% 3.70/1.00      | k2_relat_1(sK4) = k1_xboole_0
% 3.70/1.00      | k1_relat_1(sK4) = sK2 ),
% 3.70/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4852]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_9704,plain,
% 3.70/1.00      ( k1_relat_1(sK4) = sK2 | k2_relat_1(sK4) = k1_xboole_0 ),
% 3.70/1.00      inference(global_propositional_subsumption,
% 3.70/1.00                [status(thm)],
% 3.70/1.00                [c_4852,c_37,c_36,c_891,c_2700,c_2761,c_3162,c_3239,
% 3.70/1.00                 c_3796,c_4308,c_4857]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_9705,plain,
% 3.70/1.00      ( k2_relat_1(sK4) = k1_xboole_0 | k1_relat_1(sK4) = sK2 ),
% 3.70/1.00      inference(renaming,[status(thm)],[c_9704]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_9726,plain,
% 3.70/1.00      ( k1_relat_1(sK4) = sK2
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0))) = iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_9705,c_2783]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_9727,plain,
% 3.70/1.00      ( k1_relat_1(sK4) = sK2
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.70/1.00      inference(demodulation,[status(thm)],[c_9726,c_0]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2585,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 3.70/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_430]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_4999,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 3.70/1.00      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_1,c_2585]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_9881,plain,
% 3.70/1.00      ( k1_relat_1(sK4) = sK2
% 3.70/1.00      | r1_tarski(k2_relat_1(sK4),X0) = iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_9727,c_4999]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_12,plain,
% 3.70/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.70/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2597,plain,
% 3.70/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.70/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3271,plain,
% 3.70/1.00      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_2588,c_2597]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_34,negated_conjecture,
% 3.70/1.00      ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
% 3.70/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2589,plain,
% 3.70/1.00      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3329,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(sK4),sK1) != iProver_top ),
% 3.70/1.00      inference(demodulation,[status(thm)],[c_3271,c_2589]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_10038,plain,
% 3.70/1.00      ( k1_relat_1(sK4) = sK2 ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_9881,c_3329]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_31,plain,
% 3.70/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.70/1.00      | r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 3.70/1.00      | ~ v1_funct_1(X0)
% 3.70/1.00      | ~ v1_relat_1(X0) ),
% 3.70/1.00      inference(cnf_transformation,[],[f103]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_820,plain,
% 3.70/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.70/1.00      | r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 3.70/1.00      | ~ v1_relat_1(X0)
% 3.70/1.00      | sK4 != X0 ),
% 3.70/1.00      inference(resolution_lifted,[status(thm)],[c_31,c_38]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_821,plain,
% 3.70/1.00      ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
% 3.70/1.00      | r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
% 3.70/1.00      | ~ v1_relat_1(sK4) ),
% 3.70/1.00      inference(unflattening,[status(thm)],[c_820]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_28,plain,
% 3.70/1.00      ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 3.70/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.70/1.00      | ~ v1_funct_1(X0)
% 3.70/1.00      | ~ v1_relat_1(X0) ),
% 3.70/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_865,plain,
% 3.70/1.00      ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 3.70/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.70/1.00      | ~ v1_relat_1(X0)
% 3.70/1.00      | sK4 != X0 ),
% 3.70/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_38]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_866,plain,
% 3.70/1.00      ( ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 3.70/1.00      | ~ v1_relat_1(sK4) ),
% 3.70/1.00      inference(unflattening,[status(thm)],[c_865]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1234,plain,
% 3.70/1.00      ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X1)))
% 3.70/1.00      | ~ v1_relat_1(sK4)
% 3.70/1.00      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),X1,sK4)) != sK0(k1_relat_1(sK4),X0,sK4)
% 3.70/1.00      | k1_relat_1(sK4) != X1 ),
% 3.70/1.00      inference(resolution_lifted,[status(thm)],[c_821,c_866]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1235,plain,
% 3.70/1.00      ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_relat_1(sK4))))
% 3.70/1.00      | ~ v1_relat_1(sK4)
% 3.70/1.00      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),k1_relat_1(sK4),sK4)) != sK0(k1_relat_1(sK4),X0,sK4) ),
% 3.70/1.00      inference(unflattening,[status(thm)],[c_1234]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1968,plain,
% 3.70/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_relat_1(sK4))))
% 3.70/1.00      | ~ v1_relat_1(sK4)
% 3.70/1.00      | sP0_iProver_split ),
% 3.70/1.00      inference(splitting,
% 3.70/1.00                [splitting(split),new_symbols(definition,[])],
% 3.70/1.00                [c_1235]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2565,plain,
% 3.70/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_relat_1(sK4)))) = iProver_top
% 3.70/1.00      | v1_relat_1(sK4) != iProver_top
% 3.70/1.00      | sP0_iProver_split = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_1968]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2012,plain,
% 3.70/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_relat_1(sK4)))) = iProver_top
% 3.70/1.00      | v1_relat_1(sK4) != iProver_top
% 3.70/1.00      | sP0_iProver_split = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_1968]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_4226,plain,
% 3.70/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_relat_1(sK4)))) = iProver_top
% 3.70/1.00      | sP0_iProver_split = iProver_top ),
% 3.70/1.00      inference(global_propositional_subsumption,
% 3.70/1.00                [status(thm)],
% 3.70/1.00                [c_2565,c_45,c_2012,c_2762]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_4996,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(sK4),k1_relat_1(sK4)) = iProver_top
% 3.70/1.00      | sP0_iProver_split = iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_4226,c_2585]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_24,plain,
% 3.70/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.70/1.00      | ~ m1_subset_1(X3,X1)
% 3.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/1.00      | v1_xboole_0(X1)
% 3.70/1.00      | ~ v1_funct_1(X0)
% 3.70/1.00      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.70/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_40,negated_conjecture,
% 3.70/1.00      ( ~ v1_xboole_0(sK2) ),
% 3.70/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_488,plain,
% 3.70/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.70/1.00      | ~ m1_subset_1(X3,X1)
% 3.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/1.00      | ~ v1_funct_1(X0)
% 3.70/1.00      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
% 3.70/1.00      | sK2 != X1 ),
% 3.70/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_40]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_489,plain,
% 3.70/1.00      ( ~ v1_funct_2(X0,sK2,X1)
% 3.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
% 3.70/1.00      | ~ m1_subset_1(X2,sK2)
% 3.70/1.00      | ~ v1_funct_1(X0)
% 3.70/1.00      | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2) ),
% 3.70/1.00      inference(unflattening,[status(thm)],[c_488]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_784,plain,
% 3.70/1.00      ( ~ v1_funct_2(X0,sK2,X1)
% 3.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
% 3.70/1.00      | ~ m1_subset_1(X2,sK2)
% 3.70/1.00      | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2)
% 3.70/1.00      | sK4 != X0 ),
% 3.70/1.00      inference(resolution_lifted,[status(thm)],[c_489,c_38]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_785,plain,
% 3.70/1.00      ( ~ v1_funct_2(sK4,sK2,X0)
% 3.70/1.00      | ~ m1_subset_1(X1,sK2)
% 3.70/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 3.70/1.00      | k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1) ),
% 3.70/1.00      inference(unflattening,[status(thm)],[c_784]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2582,plain,
% 3.70/1.00      ( k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1)
% 3.70/1.00      | v1_funct_2(sK4,sK2,X0) != iProver_top
% 3.70/1.00      | m1_subset_1(X1,sK2) != iProver_top
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_785]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_786,plain,
% 3.70/1.00      ( k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1)
% 3.70/1.00      | v1_funct_2(sK4,sK2,X0) != iProver_top
% 3.70/1.00      | m1_subset_1(X1,sK2) != iProver_top
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_785]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2701,plain,
% 3.70/1.00      ( v1_funct_2(sK4,sK2,sK3) != iProver_top
% 3.70/1.00      | v1_partfun1(sK4,sK2) = iProver_top
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_2700]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2737,plain,
% 3.70/1.00      ( v1_funct_2(sK4,sK2,X0) = iProver_top
% 3.70/1.00      | v1_partfun1(sK4,sK2) != iProver_top
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_2736]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3129,plain,
% 3.70/1.00      ( k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1)
% 3.70/1.00      | m1_subset_1(X1,sK2) != iProver_top
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
% 3.70/1.00      inference(global_propositional_subsumption,
% 3.70/1.00                [status(thm)],
% 3.70/1.00                [c_2582,c_44,c_45,c_786,c_2701,c_2737]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_5156,plain,
% 3.70/1.00      ( k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1)
% 3.70/1.00      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 3.70/1.00      | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top
% 3.70/1.00      | m1_subset_1(X1,sK2) != iProver_top
% 3.70/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_2596,c_3129]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_5360,plain,
% 3.70/1.00      ( m1_subset_1(X1,sK2) != iProver_top
% 3.70/1.00      | k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1)
% 3.70/1.00      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
% 3.70/1.00      inference(global_propositional_subsumption,
% 3.70/1.00                [status(thm)],
% 3.70/1.00                [c_5156,c_45,c_2762,c_3240]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_5361,plain,
% 3.70/1.00      ( k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1)
% 3.70/1.00      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 3.70/1.00      | m1_subset_1(X1,sK2) != iProver_top ),
% 3.70/1.00      inference(renaming,[status(thm)],[c_5360]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_6823,plain,
% 3.70/1.00      ( k3_funct_2(sK2,k1_relat_1(sK4),sK4,X0) = k1_funct_1(sK4,X0)
% 3.70/1.00      | m1_subset_1(X0,sK2) != iProver_top
% 3.70/1.00      | sP0_iProver_split = iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_4996,c_5361]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_10053,plain,
% 3.70/1.00      ( k3_funct_2(sK2,sK2,sK4,X0) = k1_funct_1(sK4,X0)
% 3.70/1.00      | m1_subset_1(X0,sK2) != iProver_top
% 3.70/1.00      | sP0_iProver_split = iProver_top ),
% 3.70/1.00      inference(demodulation,[status(thm)],[c_10038,c_6823]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_13035,plain,
% 3.70/1.00      ( k3_funct_2(sK2,sK2,sK4,sK0(sK2,k1_xboole_0,sK4)) = k1_funct_1(sK4,sK0(sK2,k1_xboole_0,sK4))
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.70/1.00      | sP0_iProver_split = iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_8528,c_10053]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_49,plain,
% 3.70/1.00      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2664,plain,
% 3.70/1.00      ( ~ r1_tarski(X0,X1)
% 3.70/1.00      | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
% 3.70/1.00      | k2_relset_1(sK2,sK3,sK4) != X0
% 3.70/1.00      | sK1 != X1 ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_1981]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2746,plain,
% 3.70/1.00      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
% 3.70/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.70/1.00      | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(X0)
% 3.70/1.00      | sK1 != X1 ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_2664]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2864,plain,
% 3.70/1.00      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
% 3.70/1.00      | ~ r1_tarski(k2_relat_1(X0),sK1)
% 3.70/1.00      | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(X0)
% 3.70/1.00      | sK1 != sK1 ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_2746]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3022,plain,
% 3.70/1.00      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
% 3.70/1.00      | ~ r1_tarski(k2_relat_1(sK4),sK1)
% 3.70/1.00      | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
% 3.70/1.00      | sK1 != sK1 ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_2864]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3023,plain,
% 3.70/1.00      ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
% 3.70/1.00      | sK1 != sK1
% 3.70/1.00      | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) = iProver_top
% 3.70/1.00      | r1_tarski(k2_relat_1(sK4),sK1) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_3022]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3189,plain,
% 3.70/1.00      ( sK1 = sK1 ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_1976]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_8225,plain,
% 3.70/1.00      ( sK3 = k1_xboole_0
% 3.70/1.00      | r1_tarski(k2_relat_1(sK4),X0) = iProver_top
% 3.70/1.00      | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_4934,c_2585]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_10081,plain,
% 3.70/1.00      ( m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
% 3.70/1.00      inference(demodulation,[status(thm)],[c_10038,c_4929]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3135,plain,
% 3.70/1.00      ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
% 3.70/1.00      | m1_subset_1(X0,sK2) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_2588,c_3129]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_12017,plain,
% 3.70/1.00      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_10081,c_3135]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_12028,plain,
% 3.70/1.00      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 3.70/1.00      | r1_tarski(k2_relat_1(sK4),X0) = iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_12017,c_2585]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_13281,plain,
% 3.70/1.00      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,sK1,sK4)) = k1_funct_1(sK4,sK0(sK2,sK1,sK4)) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_12028,c_3329]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_35,negated_conjecture,
% 3.70/1.00      ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1)
% 3.70/1.00      | ~ m1_subset_1(X0,sK2) ),
% 3.70/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_30,plain,
% 3.70/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.70/1.00      | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 3.70/1.00      | ~ v1_funct_1(X0)
% 3.70/1.00      | ~ v1_relat_1(X0) ),
% 3.70/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_835,plain,
% 3.70/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.70/1.00      | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 3.70/1.00      | ~ v1_relat_1(X0)
% 3.70/1.00      | sK4 != X0 ),
% 3.70/1.00      inference(resolution_lifted,[status(thm)],[c_30,c_38]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_836,plain,
% 3.70/1.00      ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
% 3.70/1.00      | ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
% 3.70/1.00      | ~ v1_relat_1(sK4) ),
% 3.70/1.00      inference(unflattening,[status(thm)],[c_835]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1180,plain,
% 3.70/1.00      ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
% 3.70/1.00      | ~ m1_subset_1(X1,sK2)
% 3.70/1.00      | ~ v1_relat_1(sK4)
% 3.70/1.00      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)) != k3_funct_2(sK2,sK3,sK4,X1)
% 3.70/1.00      | sK1 != X0 ),
% 3.70/1.00      inference(resolution_lifted,[status(thm)],[c_35,c_836]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1181,plain,
% 3.70/1.00      ( v1_funct_2(sK4,k1_relat_1(sK4),sK1)
% 3.70/1.00      | ~ m1_subset_1(X0,sK2)
% 3.70/1.00      | ~ v1_relat_1(sK4)
% 3.70/1.00      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
% 3.70/1.00      inference(unflattening,[status(thm)],[c_1180]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1972,plain,
% 3.70/1.00      ( ~ m1_subset_1(X0,sK2)
% 3.70/1.00      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
% 3.70/1.00      | ~ sP2_iProver_split ),
% 3.70/1.00      inference(splitting,
% 3.70/1.00                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 3.70/1.00                [c_1181]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2572,plain,
% 3.70/1.00      ( k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
% 3.70/1.00      | m1_subset_1(X0,sK2) != iProver_top
% 3.70/1.00      | sP2_iProver_split != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_1972]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_10093,plain,
% 3.70/1.00      ( k1_funct_1(sK4,sK0(sK2,sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
% 3.70/1.00      | m1_subset_1(X0,sK2) != iProver_top
% 3.70/1.00      | sP2_iProver_split != iProver_top ),
% 3.70/1.00      inference(demodulation,[status(thm)],[c_10038,c_2572]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1162,plain,
% 3.70/1.00      ( ~ m1_subset_1(X0,sK2)
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X1)))
% 3.70/1.00      | ~ v1_relat_1(sK4)
% 3.70/1.00      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),X1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
% 3.70/1.00      | sK1 != X1 ),
% 3.70/1.00      inference(resolution_lifted,[status(thm)],[c_35,c_866]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1163,plain,
% 3.70/1.00      ( ~ m1_subset_1(X0,sK2)
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
% 3.70/1.00      | ~ v1_relat_1(sK4)
% 3.70/1.00      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
% 3.70/1.00      inference(unflattening,[status(thm)],[c_1162]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1974,plain,
% 3.70/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
% 3.70/1.00      | ~ v1_relat_1(sK4)
% 3.70/1.00      | sP2_iProver_split ),
% 3.70/1.00      inference(splitting,
% 3.70/1.00                [splitting(split),new_symbols(definition,[])],
% 3.70/1.00                [c_1163]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2024,plain,
% 3.70/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
% 3.70/1.00      | v1_relat_1(sK4) != iProver_top
% 3.70/1.00      | sP2_iProver_split = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_1974]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3165,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(sK4),sK1)
% 3.70/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_3065]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3166,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(sK4),sK1) = iProver_top
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_3165]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_10278,plain,
% 3.70/1.00      ( m1_subset_1(X0,sK2) != iProver_top
% 3.70/1.00      | k1_funct_1(sK4,sK0(sK2,sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
% 3.70/1.00      inference(global_propositional_subsumption,
% 3.70/1.00                [status(thm)],
% 3.70/1.00                [c_10093,c_45,c_49,c_2024,c_2762,c_3023,c_3166,c_3189,
% 3.70/1.00                 c_3271]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_10279,plain,
% 3.70/1.00      ( k1_funct_1(sK4,sK0(sK2,sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
% 3.70/1.00      | m1_subset_1(X0,sK2) != iProver_top ),
% 3.70/1.00      inference(renaming,[status(thm)],[c_10278]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_13289,plain,
% 3.70/1.00      ( m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_13281,c_10279]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_14083,plain,
% 3.70/1.00      ( sK3 = k1_xboole_0
% 3.70/1.00      | r1_tarski(k2_relat_1(sK4),sK1) = iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_8225,c_13289]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_14279,plain,
% 3.70/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.70/1.00      inference(global_propositional_subsumption,
% 3.70/1.00                [status(thm)],
% 3.70/1.00                [c_13035,c_45,c_49,c_133,c_134,c_2762,c_3023,c_3063,
% 3.70/1.00                 c_3189,c_3271,c_3305,c_4351,c_4988,c_5895,c_14083]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_5614,plain,
% 3.70/1.00      ( r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.70/1.00      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_0,c_2586]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_14287,plain,
% 3.70/1.00      ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_14279,c_5614]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_14293,plain,
% 3.70/1.00      ( r1_tarski(sK2,X0) = iProver_top ),
% 3.70/1.00      inference(light_normalisation,[status(thm)],[c_14287,c_10038]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_14308,plain,
% 3.70/1.00      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_14293]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_4993,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_2588,c_2585]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_5148,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.70/1.00      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 3.70/1.00      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.70/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_1,c_2596]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_5760,plain,
% 3.70/1.00      ( r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.70/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_4993,c_5148]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_6013,plain,
% 3.70/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.70/1.00      | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top ),
% 3.70/1.00      inference(global_propositional_subsumption,
% 3.70/1.00                [status(thm)],
% 3.70/1.00                [c_5760,c_45,c_2762]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_6014,plain,
% 3.70/1.00      ( r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.70/1.00      inference(renaming,[status(thm)],[c_6013]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_6017,plain,
% 3.70/1.00      ( sK3 = k1_xboole_0
% 3.70/1.00      | r1_tarski(sK2,k1_xboole_0) != iProver_top
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_4739,c_6014]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_7354,plain,
% 3.70/1.00      ( r1_tarski(sK2,k1_xboole_0) != iProver_top
% 3.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.70/1.00      inference(global_propositional_subsumption,
% 3.70/1.00                [status(thm)],
% 3.70/1.00                [c_6017,c_45,c_133,c_134,c_2762,c_3063,c_3305,c_4351,
% 3.70/1.00                 c_4988,c_5895]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_7363,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(sK4),X0) = iProver_top
% 3.70/1.00      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_7354,c_4999]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_7648,plain,
% 3.70/1.00      ( r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_7363,c_3329]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(contradiction,plain,
% 3.70/1.00      ( $false ),
% 3.70/1.00      inference(minisat,[status(thm)],[c_14308,c_7648]) ).
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.70/1.00  
% 3.70/1.00  ------                               Statistics
% 3.70/1.00  
% 3.70/1.00  ------ General
% 3.70/1.00  
% 3.70/1.00  abstr_ref_over_cycles:                  0
% 3.70/1.00  abstr_ref_under_cycles:                 0
% 3.70/1.00  gc_basic_clause_elim:                   0
% 3.70/1.00  forced_gc_time:                         0
% 3.70/1.00  parsing_time:                           0.021
% 3.70/1.00  unif_index_cands_time:                  0.
% 3.70/1.00  unif_index_add_time:                    0.
% 3.70/1.00  orderings_time:                         0.
% 3.70/1.00  out_proof_time:                         0.015
% 3.70/1.00  total_time:                             0.453
% 3.70/1.00  num_of_symbols:                         58
% 3.70/1.00  num_of_terms:                           9560
% 3.70/1.00  
% 3.70/1.00  ------ Preprocessing
% 3.70/1.00  
% 3.70/1.00  num_of_splits:                          6
% 3.70/1.00  num_of_split_atoms:                     3
% 3.70/1.00  num_of_reused_defs:                     3
% 3.70/1.00  num_eq_ax_congr_red:                    23
% 3.70/1.00  num_of_sem_filtered_clauses:            1
% 3.70/1.00  num_of_subtypes:                        0
% 3.70/1.00  monotx_restored_types:                  0
% 3.70/1.00  sat_num_of_epr_types:                   0
% 3.70/1.00  sat_num_of_non_cyclic_types:            0
% 3.70/1.00  sat_guarded_non_collapsed_types:        0
% 3.70/1.00  num_pure_diseq_elim:                    0
% 3.70/1.00  simp_replaced_by:                       0
% 3.70/1.00  res_preprocessed:                       177
% 3.70/1.00  prep_upred:                             0
% 3.70/1.00  prep_unflattend:                        53
% 3.70/1.00  smt_new_axioms:                         0
% 3.70/1.00  pred_elim_cands:                        5
% 3.70/1.00  pred_elim:                              5
% 3.70/1.00  pred_elim_cl:                           2
% 3.70/1.00  pred_elim_cycles:                       13
% 3.70/1.00  merged_defs:                            0
% 3.70/1.00  merged_defs_ncl:                        0
% 3.70/1.00  bin_hyper_res:                          0
% 3.70/1.00  prep_cycles:                            4
% 3.70/1.00  pred_elim_time:                         0.038
% 3.70/1.00  splitting_time:                         0.
% 3.70/1.00  sem_filter_time:                        0.
% 3.70/1.00  monotx_time:                            0.
% 3.70/1.00  subtype_inf_time:                       0.
% 3.70/1.00  
% 3.70/1.00  ------ Problem properties
% 3.70/1.00  
% 3.70/1.00  clauses:                                40
% 3.70/1.00  conjectures:                            3
% 3.70/1.00  epr:                                    1
% 3.70/1.00  horn:                                   27
% 3.70/1.00  ground:                                 11
% 3.70/1.00  unary:                                  5
% 3.70/1.00  binary:                                 8
% 3.70/1.00  lits:                                   108
% 3.70/1.00  lits_eq:                                24
% 3.70/1.00  fd_pure:                                0
% 3.70/1.00  fd_pseudo:                              0
% 3.70/1.00  fd_cond:                                4
% 3.70/1.00  fd_pseudo_cond:                         0
% 3.70/1.00  ac_symbols:                             0
% 3.70/1.00  
% 3.70/1.00  ------ Propositional Solver
% 3.70/1.00  
% 3.70/1.00  prop_solver_calls:                      32
% 3.70/1.00  prop_fast_solver_calls:                 2126
% 3.70/1.00  smt_solver_calls:                       0
% 3.70/1.00  smt_fast_solver_calls:                  0
% 3.70/1.00  prop_num_of_clauses:                    5448
% 3.70/1.00  prop_preprocess_simplified:             13291
% 3.70/1.00  prop_fo_subsumed:                       115
% 3.70/1.00  prop_solver_time:                       0.
% 3.70/1.00  smt_solver_time:                        0.
% 3.70/1.00  smt_fast_solver_time:                   0.
% 3.70/1.00  prop_fast_solver_time:                  0.
% 3.70/1.00  prop_unsat_core_time:                   0.
% 3.70/1.00  
% 3.70/1.00  ------ QBF
% 3.70/1.00  
% 3.70/1.00  qbf_q_res:                              0
% 3.70/1.00  qbf_num_tautologies:                    0
% 3.70/1.00  qbf_prep_cycles:                        0
% 3.70/1.00  
% 3.70/1.00  ------ BMC1
% 3.70/1.00  
% 3.70/1.00  bmc1_current_bound:                     -1
% 3.70/1.00  bmc1_last_solved_bound:                 -1
% 3.70/1.00  bmc1_unsat_core_size:                   -1
% 3.70/1.00  bmc1_unsat_core_parents_size:           -1
% 3.70/1.00  bmc1_merge_next_fun:                    0
% 3.70/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.70/1.00  
% 3.70/1.00  ------ Instantiation
% 3.70/1.00  
% 3.70/1.00  inst_num_of_clauses:                    1814
% 3.70/1.00  inst_num_in_passive:                    759
% 3.70/1.00  inst_num_in_active:                     864
% 3.70/1.00  inst_num_in_unprocessed:                191
% 3.70/1.00  inst_num_of_loops:                      1080
% 3.70/1.00  inst_num_of_learning_restarts:          0
% 3.70/1.00  inst_num_moves_active_passive:          210
% 3.70/1.00  inst_lit_activity:                      0
% 3.70/1.00  inst_lit_activity_moves:                0
% 3.70/1.00  inst_num_tautologies:                   0
% 3.70/1.00  inst_num_prop_implied:                  0
% 3.70/1.00  inst_num_existing_simplified:           0
% 3.70/1.00  inst_num_eq_res_simplified:             0
% 3.70/1.00  inst_num_child_elim:                    0
% 3.70/1.00  inst_num_of_dismatching_blockings:      546
% 3.70/1.00  inst_num_of_non_proper_insts:           1834
% 3.70/1.00  inst_num_of_duplicates:                 0
% 3.70/1.00  inst_inst_num_from_inst_to_res:         0
% 3.70/1.00  inst_dismatching_checking_time:         0.
% 3.70/1.00  
% 3.70/1.00  ------ Resolution
% 3.70/1.00  
% 3.70/1.00  res_num_of_clauses:                     0
% 3.70/1.00  res_num_in_passive:                     0
% 3.70/1.00  res_num_in_active:                      0
% 3.70/1.00  res_num_of_loops:                       181
% 3.70/1.00  res_forward_subset_subsumed:            88
% 3.70/1.00  res_backward_subset_subsumed:           0
% 3.70/1.00  res_forward_subsumed:                   0
% 3.70/1.00  res_backward_subsumed:                  0
% 3.70/1.00  res_forward_subsumption_resolution:     1
% 3.70/1.00  res_backward_subsumption_resolution:    0
% 3.70/1.00  res_clause_to_clause_subsumption:       815
% 3.70/1.00  res_orphan_elimination:                 0
% 3.70/1.00  res_tautology_del:                      170
% 3.70/1.00  res_num_eq_res_simplified:              0
% 3.70/1.00  res_num_sel_changes:                    0
% 3.70/1.00  res_moves_from_active_to_pass:          0
% 3.70/1.00  
% 3.70/1.00  ------ Superposition
% 3.70/1.00  
% 3.70/1.00  sup_time_total:                         0.
% 3.70/1.00  sup_time_generating:                    0.
% 3.70/1.00  sup_time_sim_full:                      0.
% 3.70/1.00  sup_time_sim_immed:                     0.
% 3.70/1.00  
% 3.70/1.00  sup_num_of_clauses:                     212
% 3.70/1.00  sup_num_in_active:                      120
% 3.70/1.00  sup_num_in_passive:                     92
% 3.70/1.00  sup_num_of_loops:                       214
% 3.70/1.00  sup_fw_superposition:                   153
% 3.70/1.00  sup_bw_superposition:                   375
% 3.70/1.00  sup_immediate_simplified:               149
% 3.70/1.00  sup_given_eliminated:                   1
% 3.70/1.00  comparisons_done:                       0
% 3.70/1.00  comparisons_avoided:                    106
% 3.70/1.00  
% 3.70/1.00  ------ Simplifications
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  sim_fw_subset_subsumed:                 90
% 3.70/1.00  sim_bw_subset_subsumed:                 57
% 3.70/1.00  sim_fw_subsumed:                        32
% 3.70/1.00  sim_bw_subsumed:                        27
% 3.70/1.00  sim_fw_subsumption_res:                 0
% 3.70/1.00  sim_bw_subsumption_res:                 0
% 3.70/1.00  sim_tautology_del:                      11
% 3.70/1.00  sim_eq_tautology_del:                   3
% 3.70/1.00  sim_eq_res_simp:                        0
% 3.70/1.00  sim_fw_demodulated:                     5
% 3.70/1.00  sim_bw_demodulated:                     55
% 3.70/1.00  sim_light_normalised:                   41
% 3.70/1.00  sim_joinable_taut:                      0
% 3.70/1.00  sim_joinable_simp:                      0
% 3.70/1.00  sim_ac_normalised:                      0
% 3.70/1.00  sim_smt_subsumption:                    0
% 3.70/1.00  
%------------------------------------------------------------------------------
