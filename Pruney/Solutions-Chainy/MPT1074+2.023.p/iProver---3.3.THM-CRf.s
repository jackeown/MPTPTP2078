%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:16 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :  168 (4967 expanded)
%              Number of clauses        :  109 (1538 expanded)
%              Number of leaves         :   16 (1384 expanded)
%              Depth                    :   31
%              Number of atoms          :  541 (30584 expanded)
%              Number of equality atoms :  207 (3122 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   2 average)
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

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f34,plain,(
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

fof(f33,plain,(
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

fof(f32,plain,
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

fof(f35,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1)
        | ~ m1_subset_1(X4,sK2) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f28,f34,f33,f32])).

fof(f61,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f21,plain,(
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
    inference(flattening,[],[f21])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f60,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f58,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

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

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
        & r2_hidden(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
        & r2_hidden(sK0(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f30])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK0(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f70,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f55])).

fof(f59,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f71,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | ~ r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f54])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f56])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f63,plain,(
    ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1364,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1365,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2978,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1364,c_1365])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1372,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1759,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1364,c_1372])).

cnf(c_3005,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2978,c_1759])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_31,plain,
    ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_26,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_310,plain,
    ( sK3 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_26])).

cnf(c_3164,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3005,c_31,c_310])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_16,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_440,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_441,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_508,plain,
    ( m1_subset_1(X0,X1)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X2)))
    | ~ v1_relat_1(sK4)
    | sK0(k1_relat_1(sK4),X2,sK4) != X0
    | k1_relat_1(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_441])).

cnf(c_509,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_508])).

cnf(c_1358,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_509])).

cnf(c_32,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_510,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_509])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1599,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1696,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1599])).

cnf(c_1697,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1696])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1724,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1725,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1724])).

cnf(c_2683,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1358,c_32,c_510,c_1697,c_1725])).

cnf(c_2684,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_2683])).

cnf(c_3167,plain,
    ( m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3164,c_2684])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_27,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_339,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_27])).

cnf(c_340,plain,
    ( ~ v1_funct_2(X0,sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | ~ m1_subset_1(X2,sK2)
    | ~ v1_funct_1(X0)
    | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_374,plain,
    ( ~ v1_funct_2(X0,sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | ~ m1_subset_1(X2,sK2)
    | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_340,c_25])).

cnf(c_375,plain,
    ( ~ v1_funct_2(sK4,sK2,X0)
    | ~ m1_subset_1(X1,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1) ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_1361,plain,
    ( k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1)
    | v1_funct_2(sK4,sK2,X0) != iProver_top
    | m1_subset_1(X1,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_2067,plain,
    ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1364,c_1361])).

cnf(c_2072,plain,
    ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2067,c_31])).

cnf(c_4534,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3167,c_2072])).

cnf(c_4574,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | k1_relset_1(sK2,X0,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_4534,c_1372])).

cnf(c_4617,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | k1_relset_1(sK2,X0,sK4) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_4574,c_3164])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1)
    | ~ m1_subset_1(X0,sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_17,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_425,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_426,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
    | ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_425])).

cnf(c_556,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
    | ~ m1_subset_1(X1,sK2)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)) != k3_funct_2(sK2,sK3,sK4,X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_426])).

cnf(c_557,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),sK1)
    | ~ m1_subset_1(X0,sK2)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
    inference(unflattening,[status(thm)],[c_556])).

cnf(c_861,plain,
    ( ~ m1_subset_1(X0,sK2)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_557])).

cnf(c_1354,plain,
    ( k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
    | m1_subset_1(X0,sK2) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_861])).

cnf(c_3180,plain,
    ( k1_funct_1(sK4,sK0(sK2,sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
    | m1_subset_1(X0,sK2) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_3164,c_1354])).

cnf(c_4698,plain,
    ( k1_relset_1(sK2,X0,sK4) = sK2
    | k1_funct_1(sK4,sK0(sK2,X0,sK4)) != k1_funct_1(sK4,sK0(sK2,sK1,sK4))
    | m1_subset_1(sK0(sK2,X0,sK4),sK2) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_4617,c_3180])).

cnf(c_5060,plain,
    ( k1_relset_1(sK2,sK1,sK4) = sK2
    | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4698])).

cnf(c_15,plain,
    ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_455,plain,
    ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_25])).

cnf(c_456,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_538,plain,
    ( ~ m1_subset_1(X0,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X1)))
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),X1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_456])).

cnf(c_539,plain,
    ( ~ m1_subset_1(X0,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_863,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
    | ~ v1_relat_1(sK4)
    | sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_539])).

cnf(c_1355,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_863])).

cnf(c_907,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_863])).

cnf(c_2153,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1355,c_32,c_907,c_1697,c_1725])).

cnf(c_2160,plain,
    ( k1_relset_1(k1_relat_1(sK4),sK1,sK4) = k1_relat_1(sK4)
    | sP2_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_2153,c_1372])).

cnf(c_3173,plain,
    ( k1_relset_1(sK2,sK1,sK4) = sK2
    | sP2_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_3164,c_2160])).

cnf(c_8171,plain,
    ( m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
    | k1_relset_1(sK2,sK1,sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5060,c_3173])).

cnf(c_8172,plain,
    ( k1_relset_1(sK2,sK1,sK4) = sK2
    | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_8171])).

cnf(c_8177,plain,
    ( k1_relset_1(sK2,sK1,sK4) = sK2
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3167,c_8172])).

cnf(c_11385,plain,
    ( k1_relset_1(sK2,sK1,sK4) = k1_relat_1(sK4)
    | k1_relset_1(sK2,sK1,sK4) = sK2 ),
    inference(superposition,[status(thm)],[c_8177,c_1372])).

cnf(c_11409,plain,
    ( k1_relset_1(sK2,sK1,sK4) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_11385,c_3164])).

cnf(c_11,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1367,plain,
    ( k1_relset_1(X0,X1,X2) != X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12270,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK1) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_11409,c_1367])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1371,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1755,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1364,c_1371])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_301,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k2_relset_1(sK2,sK3,sK4) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_21])).

cnf(c_302,plain,
    ( ~ m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_1362,plain,
    ( m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_302])).

cnf(c_1887,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1755,c_1362])).

cnf(c_4575,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | k2_relset_1(sK2,X0,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_4534,c_1371])).

cnf(c_4730,plain,
    ( k2_relset_1(sK2,X0,sK4) = k2_relat_1(sK4)
    | k1_funct_1(sK4,sK0(sK2,X0,sK4)) != k1_funct_1(sK4,sK0(sK2,sK1,sK4))
    | m1_subset_1(sK0(sK2,X0,sK4),sK2) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_4575,c_3180])).

cnf(c_5067,plain,
    ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4)
    | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4730])).

cnf(c_2161,plain,
    ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4)
    | sP2_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_2153,c_1371])).

cnf(c_3172,plain,
    ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4)
    | sP2_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_3164,c_2161])).

cnf(c_8930,plain,
    ( m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
    | k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5067,c_3172])).

cnf(c_8931,plain,
    ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4)
    | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_8930])).

cnf(c_8936,plain,
    ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3167,c_8931])).

cnf(c_12438,plain,
    ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8936,c_1371])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1373,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_12441,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12438,c_1373])).

cnf(c_12588,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12270,c_1887,c_12441])).

cnf(c_12600,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,sK1,sK4)) = k1_funct_1(sK4,sK0(sK2,sK1,sK4)) ),
    inference(superposition,[status(thm)],[c_4534,c_12588])).

cnf(c_496,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,sK2)
    | k3_funct_2(sK2,sK3,sK4,X2) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_22])).

cnf(c_497,plain,
    ( ~ m1_subset_1(X0,sK2)
    | m1_subset_1(k3_funct_2(sK2,sK3,sK4,X0),sK1) ),
    inference(unflattening,[status(thm)],[c_496])).

cnf(c_1359,plain,
    ( m1_subset_1(X0,sK2) != iProver_top
    | m1_subset_1(k3_funct_2(sK2,sK3,sK4,X0),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_497])).

cnf(c_12639,plain,
    ( m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
    | m1_subset_1(k1_funct_1(sK4,sK0(sK2,sK1,sK4)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_12600,c_1359])).

cnf(c_3176,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_3164,c_2153])).

cnf(c_12638,plain,
    ( m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_12600,c_3180])).

cnf(c_12726,plain,
    ( m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12639,c_1887,c_3176,c_12441,c_12638])).

cnf(c_12731,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3167,c_12726])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12731,c_12441,c_1887])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:12:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.32/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/0.99  
% 3.32/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.32/0.99  
% 3.32/0.99  ------  iProver source info
% 3.32/0.99  
% 3.32/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.32/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.32/0.99  git: non_committed_changes: false
% 3.32/0.99  git: last_make_outside_of_git: false
% 3.32/0.99  
% 3.32/0.99  ------ 
% 3.32/0.99  
% 3.32/0.99  ------ Input Options
% 3.32/0.99  
% 3.32/0.99  --out_options                           all
% 3.32/0.99  --tptp_safe_out                         true
% 3.32/0.99  --problem_path                          ""
% 3.32/0.99  --include_path                          ""
% 3.32/0.99  --clausifier                            res/vclausify_rel
% 3.32/0.99  --clausifier_options                    --mode clausify
% 3.32/0.99  --stdin                                 false
% 3.32/0.99  --stats_out                             all
% 3.32/0.99  
% 3.32/0.99  ------ General Options
% 3.32/0.99  
% 3.32/0.99  --fof                                   false
% 3.32/0.99  --time_out_real                         305.
% 3.32/0.99  --time_out_virtual                      -1.
% 3.32/0.99  --symbol_type_check                     false
% 3.32/0.99  --clausify_out                          false
% 3.32/0.99  --sig_cnt_out                           false
% 3.32/0.99  --trig_cnt_out                          false
% 3.32/0.99  --trig_cnt_out_tolerance                1.
% 3.32/0.99  --trig_cnt_out_sk_spl                   false
% 3.32/0.99  --abstr_cl_out                          false
% 3.32/0.99  
% 3.32/0.99  ------ Global Options
% 3.32/0.99  
% 3.32/0.99  --schedule                              default
% 3.32/0.99  --add_important_lit                     false
% 3.32/0.99  --prop_solver_per_cl                    1000
% 3.32/0.99  --min_unsat_core                        false
% 3.32/0.99  --soft_assumptions                      false
% 3.32/0.99  --soft_lemma_size                       3
% 3.32/0.99  --prop_impl_unit_size                   0
% 3.32/0.99  --prop_impl_unit                        []
% 3.32/0.99  --share_sel_clauses                     true
% 3.32/0.99  --reset_solvers                         false
% 3.32/0.99  --bc_imp_inh                            [conj_cone]
% 3.32/0.99  --conj_cone_tolerance                   3.
% 3.32/0.99  --extra_neg_conj                        none
% 3.32/0.99  --large_theory_mode                     true
% 3.32/0.99  --prolific_symb_bound                   200
% 3.32/0.99  --lt_threshold                          2000
% 3.32/0.99  --clause_weak_htbl                      true
% 3.32/0.99  --gc_record_bc_elim                     false
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing Options
% 3.32/0.99  
% 3.32/0.99  --preprocessing_flag                    true
% 3.32/0.99  --time_out_prep_mult                    0.1
% 3.32/0.99  --splitting_mode                        input
% 3.32/0.99  --splitting_grd                         true
% 3.32/0.99  --splitting_cvd                         false
% 3.32/0.99  --splitting_cvd_svl                     false
% 3.32/0.99  --splitting_nvd                         32
% 3.32/0.99  --sub_typing                            true
% 3.32/0.99  --prep_gs_sim                           true
% 3.32/0.99  --prep_unflatten                        true
% 3.32/0.99  --prep_res_sim                          true
% 3.32/0.99  --prep_upred                            true
% 3.32/0.99  --prep_sem_filter                       exhaustive
% 3.32/0.99  --prep_sem_filter_out                   false
% 3.32/0.99  --pred_elim                             true
% 3.32/0.99  --res_sim_input                         true
% 3.32/0.99  --eq_ax_congr_red                       true
% 3.32/0.99  --pure_diseq_elim                       true
% 3.32/0.99  --brand_transform                       false
% 3.32/0.99  --non_eq_to_eq                          false
% 3.32/0.99  --prep_def_merge                        true
% 3.32/0.99  --prep_def_merge_prop_impl              false
% 3.32/0.99  --prep_def_merge_mbd                    true
% 3.32/0.99  --prep_def_merge_tr_red                 false
% 3.32/0.99  --prep_def_merge_tr_cl                  false
% 3.32/0.99  --smt_preprocessing                     true
% 3.32/0.99  --smt_ac_axioms                         fast
% 3.32/0.99  --preprocessed_out                      false
% 3.32/0.99  --preprocessed_stats                    false
% 3.32/0.99  
% 3.32/0.99  ------ Abstraction refinement Options
% 3.32/0.99  
% 3.32/0.99  --abstr_ref                             []
% 3.32/0.99  --abstr_ref_prep                        false
% 3.32/0.99  --abstr_ref_until_sat                   false
% 3.32/0.99  --abstr_ref_sig_restrict                funpre
% 3.32/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.32/0.99  --abstr_ref_under                       []
% 3.32/0.99  
% 3.32/0.99  ------ SAT Options
% 3.32/0.99  
% 3.32/0.99  --sat_mode                              false
% 3.32/0.99  --sat_fm_restart_options                ""
% 3.32/0.99  --sat_gr_def                            false
% 3.32/0.99  --sat_epr_types                         true
% 3.32/0.99  --sat_non_cyclic_types                  false
% 3.32/0.99  --sat_finite_models                     false
% 3.32/0.99  --sat_fm_lemmas                         false
% 3.32/0.99  --sat_fm_prep                           false
% 3.32/0.99  --sat_fm_uc_incr                        true
% 3.32/0.99  --sat_out_model                         small
% 3.32/0.99  --sat_out_clauses                       false
% 3.32/0.99  
% 3.32/0.99  ------ QBF Options
% 3.32/0.99  
% 3.32/0.99  --qbf_mode                              false
% 3.32/0.99  --qbf_elim_univ                         false
% 3.32/0.99  --qbf_dom_inst                          none
% 3.32/0.99  --qbf_dom_pre_inst                      false
% 3.32/0.99  --qbf_sk_in                             false
% 3.32/0.99  --qbf_pred_elim                         true
% 3.32/0.99  --qbf_split                             512
% 3.32/0.99  
% 3.32/0.99  ------ BMC1 Options
% 3.32/0.99  
% 3.32/0.99  --bmc1_incremental                      false
% 3.32/0.99  --bmc1_axioms                           reachable_all
% 3.32/0.99  --bmc1_min_bound                        0
% 3.32/0.99  --bmc1_max_bound                        -1
% 3.32/0.99  --bmc1_max_bound_default                -1
% 3.32/0.99  --bmc1_symbol_reachability              true
% 3.32/0.99  --bmc1_property_lemmas                  false
% 3.32/0.99  --bmc1_k_induction                      false
% 3.32/0.99  --bmc1_non_equiv_states                 false
% 3.32/0.99  --bmc1_deadlock                         false
% 3.32/0.99  --bmc1_ucm                              false
% 3.32/0.99  --bmc1_add_unsat_core                   none
% 3.32/0.99  --bmc1_unsat_core_children              false
% 3.32/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.32/0.99  --bmc1_out_stat                         full
% 3.32/0.99  --bmc1_ground_init                      false
% 3.32/0.99  --bmc1_pre_inst_next_state              false
% 3.32/0.99  --bmc1_pre_inst_state                   false
% 3.32/0.99  --bmc1_pre_inst_reach_state             false
% 3.32/0.99  --bmc1_out_unsat_core                   false
% 3.32/0.99  --bmc1_aig_witness_out                  false
% 3.32/0.99  --bmc1_verbose                          false
% 3.32/0.99  --bmc1_dump_clauses_tptp                false
% 3.32/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.32/0.99  --bmc1_dump_file                        -
% 3.32/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.32/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.32/0.99  --bmc1_ucm_extend_mode                  1
% 3.32/0.99  --bmc1_ucm_init_mode                    2
% 3.32/0.99  --bmc1_ucm_cone_mode                    none
% 3.32/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.32/0.99  --bmc1_ucm_relax_model                  4
% 3.32/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.32/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.32/0.99  --bmc1_ucm_layered_model                none
% 3.32/0.99  --bmc1_ucm_max_lemma_size               10
% 3.32/0.99  
% 3.32/0.99  ------ AIG Options
% 3.32/0.99  
% 3.32/0.99  --aig_mode                              false
% 3.32/0.99  
% 3.32/0.99  ------ Instantiation Options
% 3.32/0.99  
% 3.32/0.99  --instantiation_flag                    true
% 3.32/0.99  --inst_sos_flag                         false
% 3.32/0.99  --inst_sos_phase                        true
% 3.32/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.32/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.32/0.99  --inst_lit_sel_side                     num_symb
% 3.32/0.99  --inst_solver_per_active                1400
% 3.32/0.99  --inst_solver_calls_frac                1.
% 3.32/0.99  --inst_passive_queue_type               priority_queues
% 3.32/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.32/0.99  --inst_passive_queues_freq              [25;2]
% 3.32/0.99  --inst_dismatching                      true
% 3.32/0.99  --inst_eager_unprocessed_to_passive     true
% 3.32/0.99  --inst_prop_sim_given                   true
% 3.32/0.99  --inst_prop_sim_new                     false
% 3.32/0.99  --inst_subs_new                         false
% 3.32/0.99  --inst_eq_res_simp                      false
% 3.32/0.99  --inst_subs_given                       false
% 3.32/0.99  --inst_orphan_elimination               true
% 3.32/0.99  --inst_learning_loop_flag               true
% 3.32/0.99  --inst_learning_start                   3000
% 3.32/0.99  --inst_learning_factor                  2
% 3.32/0.99  --inst_start_prop_sim_after_learn       3
% 3.32/0.99  --inst_sel_renew                        solver
% 3.32/0.99  --inst_lit_activity_flag                true
% 3.32/0.99  --inst_restr_to_given                   false
% 3.32/0.99  --inst_activity_threshold               500
% 3.32/0.99  --inst_out_proof                        true
% 3.32/0.99  
% 3.32/0.99  ------ Resolution Options
% 3.32/0.99  
% 3.32/0.99  --resolution_flag                       true
% 3.32/0.99  --res_lit_sel                           adaptive
% 3.32/0.99  --res_lit_sel_side                      none
% 3.32/0.99  --res_ordering                          kbo
% 3.32/0.99  --res_to_prop_solver                    active
% 3.32/0.99  --res_prop_simpl_new                    false
% 3.32/0.99  --res_prop_simpl_given                  true
% 3.32/0.99  --res_passive_queue_type                priority_queues
% 3.32/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.32/0.99  --res_passive_queues_freq               [15;5]
% 3.32/0.99  --res_forward_subs                      full
% 3.32/0.99  --res_backward_subs                     full
% 3.32/0.99  --res_forward_subs_resolution           true
% 3.32/0.99  --res_backward_subs_resolution          true
% 3.32/0.99  --res_orphan_elimination                true
% 3.32/0.99  --res_time_limit                        2.
% 3.32/0.99  --res_out_proof                         true
% 3.32/0.99  
% 3.32/0.99  ------ Superposition Options
% 3.32/0.99  
% 3.32/0.99  --superposition_flag                    true
% 3.32/0.99  --sup_passive_queue_type                priority_queues
% 3.32/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.32/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.32/0.99  --demod_completeness_check              fast
% 3.32/0.99  --demod_use_ground                      true
% 3.32/0.99  --sup_to_prop_solver                    passive
% 3.32/0.99  --sup_prop_simpl_new                    true
% 3.32/0.99  --sup_prop_simpl_given                  true
% 3.32/0.99  --sup_fun_splitting                     false
% 3.32/0.99  --sup_smt_interval                      50000
% 3.32/0.99  
% 3.32/0.99  ------ Superposition Simplification Setup
% 3.32/0.99  
% 3.32/0.99  --sup_indices_passive                   []
% 3.32/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.32/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.99  --sup_full_bw                           [BwDemod]
% 3.32/0.99  --sup_immed_triv                        [TrivRules]
% 3.32/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.99  --sup_immed_bw_main                     []
% 3.32/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.32/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/0.99  
% 3.32/0.99  ------ Combination Options
% 3.32/0.99  
% 3.32/0.99  --comb_res_mult                         3
% 3.32/0.99  --comb_sup_mult                         2
% 3.32/0.99  --comb_inst_mult                        10
% 3.32/0.99  
% 3.32/0.99  ------ Debug Options
% 3.32/0.99  
% 3.32/0.99  --dbg_backtrace                         false
% 3.32/0.99  --dbg_dump_prop_clauses                 false
% 3.32/0.99  --dbg_dump_prop_clauses_file            -
% 3.32/0.99  --dbg_out_stat                          false
% 3.32/0.99  ------ Parsing...
% 3.32/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing... gs_s  sp: 6 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.32/0.99  ------ Proving...
% 3.32/0.99  ------ Problem Properties 
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  clauses                                 33
% 3.32/0.99  conjectures                             2
% 3.32/0.99  EPR                                     3
% 3.32/0.99  Horn                                    21
% 3.32/0.99  unary                                   6
% 3.32/0.99  binary                                  4
% 3.32/0.99  lits                                    88
% 3.32/0.99  lits eq                                 21
% 3.32/0.99  fd_pure                                 0
% 3.32/0.99  fd_pseudo                               0
% 3.32/0.99  fd_cond                                 3
% 3.32/0.99  fd_pseudo_cond                          0
% 3.32/0.99  AC symbols                              0
% 3.32/0.99  
% 3.32/0.99  ------ Schedule dynamic 5 is on 
% 3.32/0.99  
% 3.32/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  ------ 
% 3.32/0.99  Current options:
% 3.32/0.99  ------ 
% 3.32/0.99  
% 3.32/0.99  ------ Input Options
% 3.32/0.99  
% 3.32/0.99  --out_options                           all
% 3.32/0.99  --tptp_safe_out                         true
% 3.32/0.99  --problem_path                          ""
% 3.32/0.99  --include_path                          ""
% 3.32/0.99  --clausifier                            res/vclausify_rel
% 3.32/0.99  --clausifier_options                    --mode clausify
% 3.32/0.99  --stdin                                 false
% 3.32/0.99  --stats_out                             all
% 3.32/0.99  
% 3.32/0.99  ------ General Options
% 3.32/0.99  
% 3.32/0.99  --fof                                   false
% 3.32/0.99  --time_out_real                         305.
% 3.32/0.99  --time_out_virtual                      -1.
% 3.32/0.99  --symbol_type_check                     false
% 3.32/0.99  --clausify_out                          false
% 3.32/0.99  --sig_cnt_out                           false
% 3.32/0.99  --trig_cnt_out                          false
% 3.32/0.99  --trig_cnt_out_tolerance                1.
% 3.32/0.99  --trig_cnt_out_sk_spl                   false
% 3.32/0.99  --abstr_cl_out                          false
% 3.32/0.99  
% 3.32/0.99  ------ Global Options
% 3.32/0.99  
% 3.32/0.99  --schedule                              default
% 3.32/0.99  --add_important_lit                     false
% 3.32/0.99  --prop_solver_per_cl                    1000
% 3.32/0.99  --min_unsat_core                        false
% 3.32/0.99  --soft_assumptions                      false
% 3.32/0.99  --soft_lemma_size                       3
% 3.32/0.99  --prop_impl_unit_size                   0
% 3.32/0.99  --prop_impl_unit                        []
% 3.32/0.99  --share_sel_clauses                     true
% 3.32/0.99  --reset_solvers                         false
% 3.32/0.99  --bc_imp_inh                            [conj_cone]
% 3.32/0.99  --conj_cone_tolerance                   3.
% 3.32/0.99  --extra_neg_conj                        none
% 3.32/0.99  --large_theory_mode                     true
% 3.32/0.99  --prolific_symb_bound                   200
% 3.32/0.99  --lt_threshold                          2000
% 3.32/0.99  --clause_weak_htbl                      true
% 3.32/0.99  --gc_record_bc_elim                     false
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing Options
% 3.32/0.99  
% 3.32/0.99  --preprocessing_flag                    true
% 3.32/0.99  --time_out_prep_mult                    0.1
% 3.32/0.99  --splitting_mode                        input
% 3.32/0.99  --splitting_grd                         true
% 3.32/0.99  --splitting_cvd                         false
% 3.32/0.99  --splitting_cvd_svl                     false
% 3.32/0.99  --splitting_nvd                         32
% 3.32/0.99  --sub_typing                            true
% 3.32/0.99  --prep_gs_sim                           true
% 3.32/0.99  --prep_unflatten                        true
% 3.32/0.99  --prep_res_sim                          true
% 3.32/0.99  --prep_upred                            true
% 3.32/0.99  --prep_sem_filter                       exhaustive
% 3.32/0.99  --prep_sem_filter_out                   false
% 3.32/0.99  --pred_elim                             true
% 3.32/0.99  --res_sim_input                         true
% 3.32/0.99  --eq_ax_congr_red                       true
% 3.32/0.99  --pure_diseq_elim                       true
% 3.32/0.99  --brand_transform                       false
% 3.32/0.99  --non_eq_to_eq                          false
% 3.32/0.99  --prep_def_merge                        true
% 3.32/0.99  --prep_def_merge_prop_impl              false
% 3.32/0.99  --prep_def_merge_mbd                    true
% 3.32/0.99  --prep_def_merge_tr_red                 false
% 3.32/0.99  --prep_def_merge_tr_cl                  false
% 3.32/0.99  --smt_preprocessing                     true
% 3.32/0.99  --smt_ac_axioms                         fast
% 3.32/0.99  --preprocessed_out                      false
% 3.32/0.99  --preprocessed_stats                    false
% 3.32/0.99  
% 3.32/0.99  ------ Abstraction refinement Options
% 3.32/0.99  
% 3.32/0.99  --abstr_ref                             []
% 3.32/0.99  --abstr_ref_prep                        false
% 3.32/0.99  --abstr_ref_until_sat                   false
% 3.32/0.99  --abstr_ref_sig_restrict                funpre
% 3.32/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.32/0.99  --abstr_ref_under                       []
% 3.32/0.99  
% 3.32/0.99  ------ SAT Options
% 3.32/0.99  
% 3.32/0.99  --sat_mode                              false
% 3.32/0.99  --sat_fm_restart_options                ""
% 3.32/0.99  --sat_gr_def                            false
% 3.32/0.99  --sat_epr_types                         true
% 3.32/0.99  --sat_non_cyclic_types                  false
% 3.32/0.99  --sat_finite_models                     false
% 3.32/0.99  --sat_fm_lemmas                         false
% 3.32/0.99  --sat_fm_prep                           false
% 3.32/0.99  --sat_fm_uc_incr                        true
% 3.32/0.99  --sat_out_model                         small
% 3.32/0.99  --sat_out_clauses                       false
% 3.32/0.99  
% 3.32/0.99  ------ QBF Options
% 3.32/0.99  
% 3.32/0.99  --qbf_mode                              false
% 3.32/0.99  --qbf_elim_univ                         false
% 3.32/0.99  --qbf_dom_inst                          none
% 3.32/0.99  --qbf_dom_pre_inst                      false
% 3.32/0.99  --qbf_sk_in                             false
% 3.32/0.99  --qbf_pred_elim                         true
% 3.32/0.99  --qbf_split                             512
% 3.32/0.99  
% 3.32/0.99  ------ BMC1 Options
% 3.32/0.99  
% 3.32/0.99  --bmc1_incremental                      false
% 3.32/0.99  --bmc1_axioms                           reachable_all
% 3.32/0.99  --bmc1_min_bound                        0
% 3.32/0.99  --bmc1_max_bound                        -1
% 3.32/0.99  --bmc1_max_bound_default                -1
% 3.32/0.99  --bmc1_symbol_reachability              true
% 3.32/0.99  --bmc1_property_lemmas                  false
% 3.32/0.99  --bmc1_k_induction                      false
% 3.32/0.99  --bmc1_non_equiv_states                 false
% 3.32/0.99  --bmc1_deadlock                         false
% 3.32/0.99  --bmc1_ucm                              false
% 3.32/0.99  --bmc1_add_unsat_core                   none
% 3.32/0.99  --bmc1_unsat_core_children              false
% 3.32/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.32/0.99  --bmc1_out_stat                         full
% 3.32/0.99  --bmc1_ground_init                      false
% 3.32/0.99  --bmc1_pre_inst_next_state              false
% 3.32/0.99  --bmc1_pre_inst_state                   false
% 3.32/0.99  --bmc1_pre_inst_reach_state             false
% 3.32/0.99  --bmc1_out_unsat_core                   false
% 3.32/0.99  --bmc1_aig_witness_out                  false
% 3.32/0.99  --bmc1_verbose                          false
% 3.32/0.99  --bmc1_dump_clauses_tptp                false
% 3.32/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.32/0.99  --bmc1_dump_file                        -
% 3.32/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.32/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.32/0.99  --bmc1_ucm_extend_mode                  1
% 3.32/0.99  --bmc1_ucm_init_mode                    2
% 3.32/0.99  --bmc1_ucm_cone_mode                    none
% 3.32/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.32/0.99  --bmc1_ucm_relax_model                  4
% 3.32/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.32/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.32/0.99  --bmc1_ucm_layered_model                none
% 3.32/0.99  --bmc1_ucm_max_lemma_size               10
% 3.32/0.99  
% 3.32/0.99  ------ AIG Options
% 3.32/0.99  
% 3.32/0.99  --aig_mode                              false
% 3.32/0.99  
% 3.32/0.99  ------ Instantiation Options
% 3.32/0.99  
% 3.32/0.99  --instantiation_flag                    true
% 3.32/0.99  --inst_sos_flag                         false
% 3.32/0.99  --inst_sos_phase                        true
% 3.32/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.32/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.32/0.99  --inst_lit_sel_side                     none
% 3.32/0.99  --inst_solver_per_active                1400
% 3.32/0.99  --inst_solver_calls_frac                1.
% 3.32/0.99  --inst_passive_queue_type               priority_queues
% 3.32/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.32/0.99  --inst_passive_queues_freq              [25;2]
% 3.32/0.99  --inst_dismatching                      true
% 3.32/0.99  --inst_eager_unprocessed_to_passive     true
% 3.32/0.99  --inst_prop_sim_given                   true
% 3.32/0.99  --inst_prop_sim_new                     false
% 3.32/0.99  --inst_subs_new                         false
% 3.32/0.99  --inst_eq_res_simp                      false
% 3.32/0.99  --inst_subs_given                       false
% 3.32/0.99  --inst_orphan_elimination               true
% 3.32/0.99  --inst_learning_loop_flag               true
% 3.32/0.99  --inst_learning_start                   3000
% 3.32/0.99  --inst_learning_factor                  2
% 3.32/0.99  --inst_start_prop_sim_after_learn       3
% 3.32/0.99  --inst_sel_renew                        solver
% 3.32/0.99  --inst_lit_activity_flag                true
% 3.32/0.99  --inst_restr_to_given                   false
% 3.32/0.99  --inst_activity_threshold               500
% 3.32/0.99  --inst_out_proof                        true
% 3.32/0.99  
% 3.32/0.99  ------ Resolution Options
% 3.32/0.99  
% 3.32/0.99  --resolution_flag                       false
% 3.32/0.99  --res_lit_sel                           adaptive
% 3.32/0.99  --res_lit_sel_side                      none
% 3.32/0.99  --res_ordering                          kbo
% 3.32/0.99  --res_to_prop_solver                    active
% 3.32/0.99  --res_prop_simpl_new                    false
% 3.32/0.99  --res_prop_simpl_given                  true
% 3.32/0.99  --res_passive_queue_type                priority_queues
% 3.32/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.32/0.99  --res_passive_queues_freq               [15;5]
% 3.32/0.99  --res_forward_subs                      full
% 3.32/0.99  --res_backward_subs                     full
% 3.32/0.99  --res_forward_subs_resolution           true
% 3.32/0.99  --res_backward_subs_resolution          true
% 3.32/0.99  --res_orphan_elimination                true
% 3.32/0.99  --res_time_limit                        2.
% 3.32/0.99  --res_out_proof                         true
% 3.32/0.99  
% 3.32/0.99  ------ Superposition Options
% 3.32/0.99  
% 3.32/0.99  --superposition_flag                    true
% 3.32/0.99  --sup_passive_queue_type                priority_queues
% 3.32/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.32/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.32/0.99  --demod_completeness_check              fast
% 3.32/0.99  --demod_use_ground                      true
% 3.32/0.99  --sup_to_prop_solver                    passive
% 3.32/0.99  --sup_prop_simpl_new                    true
% 3.32/0.99  --sup_prop_simpl_given                  true
% 3.32/0.99  --sup_fun_splitting                     false
% 3.32/0.99  --sup_smt_interval                      50000
% 3.32/0.99  
% 3.32/0.99  ------ Superposition Simplification Setup
% 3.32/0.99  
% 3.32/0.99  --sup_indices_passive                   []
% 3.32/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.32/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.99  --sup_full_bw                           [BwDemod]
% 3.32/0.99  --sup_immed_triv                        [TrivRules]
% 3.32/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.99  --sup_immed_bw_main                     []
% 3.32/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.32/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/0.99  
% 3.32/0.99  ------ Combination Options
% 3.32/0.99  
% 3.32/0.99  --comb_res_mult                         3
% 3.32/0.99  --comb_sup_mult                         2
% 3.32/0.99  --comb_inst_mult                        10
% 3.32/0.99  
% 3.32/0.99  ------ Debug Options
% 3.32/0.99  
% 3.32/0.99  --dbg_backtrace                         false
% 3.32/0.99  --dbg_dump_prop_clauses                 false
% 3.32/0.99  --dbg_dump_prop_clauses_file            -
% 3.32/0.99  --dbg_out_stat                          false
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  ------ Proving...
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  % SZS status Theorem for theBenchmark.p
% 3.32/0.99  
% 3.32/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.32/0.99  
% 3.32/0.99  fof(f12,conjecture,(
% 3.32/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f13,negated_conjecture,(
% 3.32/0.99    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 3.32/0.99    inference(negated_conjecture,[],[f12])).
% 3.32/0.99  
% 3.32/0.99  fof(f27,plain,(
% 3.32/0.99    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 3.32/0.99    inference(ennf_transformation,[],[f13])).
% 3.32/0.99  
% 3.32/0.99  fof(f28,plain,(
% 3.32/0.99    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 3.32/0.99    inference(flattening,[],[f27])).
% 3.32/0.99  
% 3.32/0.99  fof(f34,plain,(
% 3.32/0.99    ( ! [X2,X0,X1] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (~r1_tarski(k2_relset_1(X1,X2,sK4),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,sK4,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 3.32/0.99    introduced(choice_axiom,[])).
% 3.32/0.99  
% 3.32/0.99  fof(f33,plain,(
% 3.32/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (~r1_tarski(k2_relset_1(X1,sK3,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,sK3,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK3))) & v1_funct_2(X3,X1,sK3) & v1_funct_1(X3)) & ~v1_xboole_0(sK3))) )),
% 3.32/0.99    introduced(choice_axiom,[])).
% 3.32/0.99  
% 3.32/0.99  fof(f32,plain,(
% 3.32/0.99    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK2,X2,X3),sK1) & ! [X4] : (r2_hidden(k3_funct_2(sK2,X2,X3,X4),sK1) | ~m1_subset_1(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X2))) & v1_funct_2(X3,sK2,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK2))),
% 3.32/0.99    introduced(choice_axiom,[])).
% 3.32/0.99  
% 3.32/0.99  fof(f35,plain,(
% 3.32/0.99    ((~r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) & ! [X4] : (r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1) | ~m1_subset_1(X4,sK2)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 3.32/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f28,f34,f33,f32])).
% 3.32/0.99  
% 3.32/0.99  fof(f61,plain,(
% 3.32/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.32/0.99    inference(cnf_transformation,[],[f35])).
% 3.32/0.99  
% 3.32/0.99  fof(f9,axiom,(
% 3.32/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f21,plain,(
% 3.32/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/0.99    inference(ennf_transformation,[],[f9])).
% 3.32/0.99  
% 3.32/0.99  fof(f22,plain,(
% 3.32/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/0.99    inference(flattening,[],[f21])).
% 3.32/0.99  
% 3.32/0.99  fof(f29,plain,(
% 3.32/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/0.99    inference(nnf_transformation,[],[f22])).
% 3.32/0.99  
% 3.32/0.99  fof(f44,plain,(
% 3.32/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f29])).
% 3.32/0.99  
% 3.32/0.99  fof(f7,axiom,(
% 3.32/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f19,plain,(
% 3.32/0.99    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/0.99    inference(ennf_transformation,[],[f7])).
% 3.32/0.99  
% 3.32/0.99  fof(f42,plain,(
% 3.32/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f19])).
% 3.32/0.99  
% 3.32/0.99  fof(f60,plain,(
% 3.32/0.99    v1_funct_2(sK4,sK2,sK3)),
% 3.32/0.99    inference(cnf_transformation,[],[f35])).
% 3.32/0.99  
% 3.32/0.99  fof(f1,axiom,(
% 3.32/0.99    v1_xboole_0(k1_xboole_0)),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f36,plain,(
% 3.32/0.99    v1_xboole_0(k1_xboole_0)),
% 3.32/0.99    inference(cnf_transformation,[],[f1])).
% 3.32/0.99  
% 3.32/0.99  fof(f58,plain,(
% 3.32/0.99    ~v1_xboole_0(sK3)),
% 3.32/0.99    inference(cnf_transformation,[],[f35])).
% 3.32/0.99  
% 3.32/0.99  fof(f2,axiom,(
% 3.32/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f15,plain,(
% 3.32/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.32/0.99    inference(ennf_transformation,[],[f2])).
% 3.32/0.99  
% 3.32/0.99  fof(f37,plain,(
% 3.32/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f15])).
% 3.32/0.99  
% 3.32/0.99  fof(f11,axiom,(
% 3.32/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f25,plain,(
% 3.32/0.99    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.32/0.99    inference(ennf_transformation,[],[f11])).
% 3.32/0.99  
% 3.32/0.99  fof(f26,plain,(
% 3.32/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.32/0.99    inference(flattening,[],[f25])).
% 3.32/0.99  
% 3.32/0.99  fof(f30,plain,(
% 3.32/0.99    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),X0)))),
% 3.32/0.99    introduced(choice_axiom,[])).
% 3.32/0.99  
% 3.32/0.99  fof(f31,plain,(
% 3.32/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.32/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f30])).
% 3.32/0.99  
% 3.32/0.99  fof(f55,plain,(
% 3.32/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK0(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f31])).
% 3.32/0.99  
% 3.32/0.99  fof(f70,plain,(
% 3.32/0.99    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.32/0.99    inference(equality_resolution,[],[f55])).
% 3.32/0.99  
% 3.32/0.99  fof(f59,plain,(
% 3.32/0.99    v1_funct_1(sK4)),
% 3.32/0.99    inference(cnf_transformation,[],[f35])).
% 3.32/0.99  
% 3.32/0.99  fof(f4,axiom,(
% 3.32/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f17,plain,(
% 3.32/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.32/0.99    inference(ennf_transformation,[],[f4])).
% 3.32/0.99  
% 3.32/0.99  fof(f39,plain,(
% 3.32/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f17])).
% 3.32/0.99  
% 3.32/0.99  fof(f5,axiom,(
% 3.32/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f40,plain,(
% 3.32/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f5])).
% 3.32/0.99  
% 3.32/0.99  fof(f10,axiom,(
% 3.32/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f23,plain,(
% 3.32/0.99    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 3.32/0.99    inference(ennf_transformation,[],[f10])).
% 3.32/0.99  
% 3.32/0.99  fof(f24,plain,(
% 3.32/0.99    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 3.32/0.99    inference(flattening,[],[f23])).
% 3.32/0.99  
% 3.32/0.99  fof(f50,plain,(
% 3.32/0.99    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f24])).
% 3.32/0.99  
% 3.32/0.99  fof(f57,plain,(
% 3.32/0.99    ~v1_xboole_0(sK2)),
% 3.32/0.99    inference(cnf_transformation,[],[f35])).
% 3.32/0.99  
% 3.32/0.99  fof(f62,plain,(
% 3.32/0.99    ( ! [X4] : (r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1) | ~m1_subset_1(X4,sK2)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f35])).
% 3.32/0.99  
% 3.32/0.99  fof(f54,plain,(
% 3.32/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f31])).
% 3.32/0.99  
% 3.32/0.99  fof(f71,plain,(
% 3.32/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | ~r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.32/0.99    inference(equality_resolution,[],[f54])).
% 3.32/0.99  
% 3.32/0.99  fof(f56,plain,(
% 3.32/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f31])).
% 3.32/0.99  
% 3.32/0.99  fof(f69,plain,(
% 3.32/0.99    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.32/0.99    inference(equality_resolution,[],[f56])).
% 3.32/0.99  
% 3.32/0.99  fof(f46,plain,(
% 3.32/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f29])).
% 3.32/0.99  
% 3.32/0.99  fof(f8,axiom,(
% 3.32/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f20,plain,(
% 3.32/0.99    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/0.99    inference(ennf_transformation,[],[f8])).
% 3.32/0.99  
% 3.32/0.99  fof(f43,plain,(
% 3.32/0.99    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f20])).
% 3.32/0.99  
% 3.32/0.99  fof(f3,axiom,(
% 3.32/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f14,plain,(
% 3.32/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 3.32/0.99    inference(unused_predicate_definition_removal,[],[f3])).
% 3.32/0.99  
% 3.32/0.99  fof(f16,plain,(
% 3.32/0.99    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 3.32/0.99    inference(ennf_transformation,[],[f14])).
% 3.32/0.99  
% 3.32/0.99  fof(f38,plain,(
% 3.32/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f16])).
% 3.32/0.99  
% 3.32/0.99  fof(f63,plain,(
% 3.32/0.99    ~r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)),
% 3.32/0.99    inference(cnf_transformation,[],[f35])).
% 3.32/0.99  
% 3.32/0.99  fof(f6,axiom,(
% 3.32/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f18,plain,(
% 3.32/0.99    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/0.99    inference(ennf_transformation,[],[f6])).
% 3.32/0.99  
% 3.32/0.99  fof(f41,plain,(
% 3.32/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f18])).
% 3.32/0.99  
% 3.32/0.99  cnf(c_23,negated_conjecture,
% 3.32/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.32/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1364,plain,
% 3.32/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_13,plain,
% 3.32/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.32/0.99      | k1_xboole_0 = X2 ),
% 3.32/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1365,plain,
% 3.32/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 3.32/0.99      | k1_xboole_0 = X1
% 3.32/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.32/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2978,plain,
% 3.32/0.99      ( k1_relset_1(sK2,sK3,sK4) = sK2
% 3.32/0.99      | sK3 = k1_xboole_0
% 3.32/0.99      | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_1364,c_1365]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_6,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1372,plain,
% 3.32/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.32/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1759,plain,
% 3.32/0.99      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_1364,c_1372]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3005,plain,
% 3.32/0.99      ( k1_relat_1(sK4) = sK2
% 3.32/0.99      | sK3 = k1_xboole_0
% 3.32/0.99      | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_2978,c_1759]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_24,negated_conjecture,
% 3.32/0.99      ( v1_funct_2(sK4,sK2,sK3) ),
% 3.32/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_31,plain,
% 3.32/0.99      ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_0,plain,
% 3.32/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_26,negated_conjecture,
% 3.32/0.99      ( ~ v1_xboole_0(sK3) ),
% 3.32/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_310,plain,
% 3.32/0.99      ( sK3 != k1_xboole_0 ),
% 3.32/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_26]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3164,plain,
% 3.32/0.99      ( k1_relat_1(sK4) = sK2 ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_3005,c_31,c_310]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1,plain,
% 3.32/0.99      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 3.32/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_16,plain,
% 3.32/0.99      ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 3.32/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.32/0.99      | ~ v1_funct_1(X0)
% 3.32/0.99      | ~ v1_relat_1(X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_25,negated_conjecture,
% 3.32/0.99      ( v1_funct_1(sK4) ),
% 3.32/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_440,plain,
% 3.32/0.99      ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 3.32/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.32/0.99      | ~ v1_relat_1(X0)
% 3.32/0.99      | sK4 != X0 ),
% 3.32/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_441,plain,
% 3.32/0.99      ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
% 3.32/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 3.32/0.99      | ~ v1_relat_1(sK4) ),
% 3.32/0.99      inference(unflattening,[status(thm)],[c_440]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_508,plain,
% 3.32/0.99      ( m1_subset_1(X0,X1)
% 3.32/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X2)))
% 3.32/0.99      | ~ v1_relat_1(sK4)
% 3.32/0.99      | sK0(k1_relat_1(sK4),X2,sK4) != X0
% 3.32/0.99      | k1_relat_1(sK4) != X1 ),
% 3.32/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_441]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_509,plain,
% 3.32/0.99      ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
% 3.32/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 3.32/0.99      | ~ v1_relat_1(sK4) ),
% 3.32/0.99      inference(unflattening,[status(thm)],[c_508]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1358,plain,
% 3.32/0.99      ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 3.32/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 3.32/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_509]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_32,plain,
% 3.32/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_510,plain,
% 3.32/0.99      ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 3.32/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 3.32/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_509]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.32/0.99      | ~ v1_relat_1(X1)
% 3.32/0.99      | v1_relat_1(X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1599,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | v1_relat_1(X0)
% 3.32/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.32/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1696,plain,
% 3.32/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.32/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
% 3.32/0.99      | v1_relat_1(sK4) ),
% 3.32/0.99      inference(instantiation,[status(thm)],[c_1599]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1697,plain,
% 3.32/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.32/0.99      | v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
% 3.32/0.99      | v1_relat_1(sK4) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_1696]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4,plain,
% 3.32/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.32/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1724,plain,
% 3.32/0.99      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) ),
% 3.32/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1725,plain,
% 3.32/0.99      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_1724]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2683,plain,
% 3.32/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 3.32/0.99      | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_1358,c_32,c_510,c_1697,c_1725]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2684,plain,
% 3.32/0.99      ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 3.32/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
% 3.32/0.99      inference(renaming,[status(thm)],[c_2683]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3167,plain,
% 3.32/0.99      ( m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
% 3.32/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_3164,c_2684]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_14,plain,
% 3.32/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.32/0.99      | ~ m1_subset_1(X3,X1)
% 3.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | ~ v1_funct_1(X0)
% 3.32/0.99      | v1_xboole_0(X1)
% 3.32/0.99      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.32/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_27,negated_conjecture,
% 3.32/0.99      ( ~ v1_xboole_0(sK2) ),
% 3.32/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_339,plain,
% 3.32/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.32/0.99      | ~ m1_subset_1(X3,X1)
% 3.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | ~ v1_funct_1(X0)
% 3.32/0.99      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
% 3.32/0.99      | sK2 != X1 ),
% 3.32/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_27]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_340,plain,
% 3.32/0.99      ( ~ v1_funct_2(X0,sK2,X1)
% 3.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
% 3.32/0.99      | ~ m1_subset_1(X2,sK2)
% 3.32/0.99      | ~ v1_funct_1(X0)
% 3.32/0.99      | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2) ),
% 3.32/0.99      inference(unflattening,[status(thm)],[c_339]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_374,plain,
% 3.32/0.99      ( ~ v1_funct_2(X0,sK2,X1)
% 3.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
% 3.32/0.99      | ~ m1_subset_1(X2,sK2)
% 3.32/0.99      | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2)
% 3.32/0.99      | sK4 != X0 ),
% 3.32/0.99      inference(resolution_lifted,[status(thm)],[c_340,c_25]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_375,plain,
% 3.32/0.99      ( ~ v1_funct_2(sK4,sK2,X0)
% 3.32/0.99      | ~ m1_subset_1(X1,sK2)
% 3.32/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 3.32/0.99      | k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1) ),
% 3.32/0.99      inference(unflattening,[status(thm)],[c_374]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1361,plain,
% 3.32/0.99      ( k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1)
% 3.32/0.99      | v1_funct_2(sK4,sK2,X0) != iProver_top
% 3.32/0.99      | m1_subset_1(X1,sK2) != iProver_top
% 3.32/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_375]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2067,plain,
% 3.32/0.99      ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
% 3.32/0.99      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 3.32/0.99      | m1_subset_1(X0,sK2) != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_1364,c_1361]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2072,plain,
% 3.32/0.99      ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
% 3.32/0.99      | m1_subset_1(X0,sK2) != iProver_top ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_2067,c_31]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4534,plain,
% 3.32/0.99      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 3.32/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_3167,c_2072]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4574,plain,
% 3.32/0.99      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 3.32/0.99      | k1_relset_1(sK2,X0,sK4) = k1_relat_1(sK4) ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_4534,c_1372]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4617,plain,
% 3.32/0.99      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 3.32/0.99      | k1_relset_1(sK2,X0,sK4) = sK2 ),
% 3.32/0.99      inference(light_normalisation,[status(thm)],[c_4574,c_3164]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_22,negated_conjecture,
% 3.32/0.99      ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1)
% 3.32/0.99      | ~ m1_subset_1(X0,sK2) ),
% 3.32/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_17,plain,
% 3.32/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.32/0.99      | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 3.32/0.99      | ~ v1_funct_1(X0)
% 3.32/0.99      | ~ v1_relat_1(X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_425,plain,
% 3.32/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.32/0.99      | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 3.32/0.99      | ~ v1_relat_1(X0)
% 3.32/0.99      | sK4 != X0 ),
% 3.32/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_426,plain,
% 3.32/0.99      ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
% 3.32/0.99      | ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
% 3.32/0.99      | ~ v1_relat_1(sK4) ),
% 3.32/0.99      inference(unflattening,[status(thm)],[c_425]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_556,plain,
% 3.32/0.99      ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
% 3.32/0.99      | ~ m1_subset_1(X1,sK2)
% 3.32/0.99      | ~ v1_relat_1(sK4)
% 3.32/0.99      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)) != k3_funct_2(sK2,sK3,sK4,X1)
% 3.32/0.99      | sK1 != X0 ),
% 3.32/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_426]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_557,plain,
% 3.32/0.99      ( v1_funct_2(sK4,k1_relat_1(sK4),sK1)
% 3.32/0.99      | ~ m1_subset_1(X0,sK2)
% 3.32/0.99      | ~ v1_relat_1(sK4)
% 3.32/0.99      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
% 3.32/0.99      inference(unflattening,[status(thm)],[c_556]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_861,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,sK2)
% 3.32/0.99      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
% 3.32/0.99      | ~ sP2_iProver_split ),
% 3.32/0.99      inference(splitting,
% 3.32/0.99                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 3.32/0.99                [c_557]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1354,plain,
% 3.32/0.99      ( k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
% 3.32/0.99      | m1_subset_1(X0,sK2) != iProver_top
% 3.32/0.99      | sP2_iProver_split != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_861]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3180,plain,
% 3.32/0.99      ( k1_funct_1(sK4,sK0(sK2,sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
% 3.32/0.99      | m1_subset_1(X0,sK2) != iProver_top
% 3.32/0.99      | sP2_iProver_split != iProver_top ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_3164,c_1354]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4698,plain,
% 3.32/0.99      ( k1_relset_1(sK2,X0,sK4) = sK2
% 3.32/0.99      | k1_funct_1(sK4,sK0(sK2,X0,sK4)) != k1_funct_1(sK4,sK0(sK2,sK1,sK4))
% 3.32/0.99      | m1_subset_1(sK0(sK2,X0,sK4),sK2) != iProver_top
% 3.32/0.99      | sP2_iProver_split != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_4617,c_3180]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5060,plain,
% 3.32/0.99      ( k1_relset_1(sK2,sK1,sK4) = sK2
% 3.32/0.99      | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
% 3.32/0.99      | sP2_iProver_split != iProver_top ),
% 3.32/0.99      inference(equality_resolution,[status(thm)],[c_4698]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_15,plain,
% 3.32/0.99      ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 3.32/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.32/0.99      | ~ v1_funct_1(X0)
% 3.32/0.99      | ~ v1_relat_1(X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_455,plain,
% 3.32/0.99      ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 3.32/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.32/0.99      | ~ v1_relat_1(X0)
% 3.32/0.99      | sK4 != X0 ),
% 3.32/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_25]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_456,plain,
% 3.32/0.99      ( ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
% 3.32/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 3.32/0.99      | ~ v1_relat_1(sK4) ),
% 3.32/0.99      inference(unflattening,[status(thm)],[c_455]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_538,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,sK2)
% 3.32/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X1)))
% 3.32/0.99      | ~ v1_relat_1(sK4)
% 3.32/0.99      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),X1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
% 3.32/0.99      | sK1 != X1 ),
% 3.32/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_456]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_539,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,sK2)
% 3.32/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
% 3.32/0.99      | ~ v1_relat_1(sK4)
% 3.32/0.99      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
% 3.32/0.99      inference(unflattening,[status(thm)],[c_538]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_863,plain,
% 3.32/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
% 3.32/0.99      | ~ v1_relat_1(sK4)
% 3.32/0.99      | sP2_iProver_split ),
% 3.32/0.99      inference(splitting,
% 3.32/0.99                [splitting(split),new_symbols(definition,[])],
% 3.32/0.99                [c_539]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1355,plain,
% 3.32/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
% 3.32/0.99      | v1_relat_1(sK4) != iProver_top
% 3.32/0.99      | sP2_iProver_split = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_863]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_907,plain,
% 3.32/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
% 3.32/0.99      | v1_relat_1(sK4) != iProver_top
% 3.32/0.99      | sP2_iProver_split = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_863]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2153,plain,
% 3.32/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
% 3.32/0.99      | sP2_iProver_split = iProver_top ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_1355,c_32,c_907,c_1697,c_1725]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2160,plain,
% 3.32/0.99      ( k1_relset_1(k1_relat_1(sK4),sK1,sK4) = k1_relat_1(sK4)
% 3.32/0.99      | sP2_iProver_split = iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_2153,c_1372]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3173,plain,
% 3.32/0.99      ( k1_relset_1(sK2,sK1,sK4) = sK2
% 3.32/0.99      | sP2_iProver_split = iProver_top ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_3164,c_2160]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_8171,plain,
% 3.32/0.99      ( m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
% 3.32/0.99      | k1_relset_1(sK2,sK1,sK4) = sK2 ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_5060,c_3173]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_8172,plain,
% 3.32/0.99      ( k1_relset_1(sK2,sK1,sK4) = sK2
% 3.32/0.99      | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top ),
% 3.32/0.99      inference(renaming,[status(thm)],[c_8171]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_8177,plain,
% 3.32/0.99      ( k1_relset_1(sK2,sK1,sK4) = sK2
% 3.32/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_3167,c_8172]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_11385,plain,
% 3.32/0.99      ( k1_relset_1(sK2,sK1,sK4) = k1_relat_1(sK4)
% 3.32/0.99      | k1_relset_1(sK2,sK1,sK4) = sK2 ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_8177,c_1372]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_11409,plain,
% 3.32/0.99      ( k1_relset_1(sK2,sK1,sK4) = sK2 ),
% 3.32/0.99      inference(light_normalisation,[status(thm)],[c_11385,c_3164]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_11,plain,
% 3.32/0.99      ( v1_funct_2(X0,X1,X2)
% 3.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | k1_relset_1(X1,X2,X0) != X1
% 3.32/0.99      | k1_xboole_0 = X2 ),
% 3.32/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1367,plain,
% 3.32/0.99      ( k1_relset_1(X0,X1,X2) != X0
% 3.32/0.99      | k1_xboole_0 = X1
% 3.32/0.99      | v1_funct_2(X2,X0,X1) = iProver_top
% 3.32/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_12270,plain,
% 3.32/0.99      ( sK1 = k1_xboole_0
% 3.32/0.99      | v1_funct_2(sK4,sK2,sK1) = iProver_top
% 3.32/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_11409,c_1367]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_7,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1371,plain,
% 3.32/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.32/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1755,plain,
% 3.32/0.99      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_1364,c_1371]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2,plain,
% 3.32/0.99      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.32/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_21,negated_conjecture,
% 3.32/0.99      ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
% 3.32/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_301,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.32/0.99      | k2_relset_1(sK2,sK3,sK4) != X0
% 3.32/0.99      | sK1 != X1 ),
% 3.32/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_21]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_302,plain,
% 3.32/0.99      ( ~ m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK1)) ),
% 3.32/0.99      inference(unflattening,[status(thm)],[c_301]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1362,plain,
% 3.32/0.99      ( m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK1)) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_302]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1887,plain,
% 3.32/0.99      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) != iProver_top ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_1755,c_1362]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4575,plain,
% 3.32/0.99      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 3.32/0.99      | k2_relset_1(sK2,X0,sK4) = k2_relat_1(sK4) ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_4534,c_1371]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4730,plain,
% 3.32/0.99      ( k2_relset_1(sK2,X0,sK4) = k2_relat_1(sK4)
% 3.32/0.99      | k1_funct_1(sK4,sK0(sK2,X0,sK4)) != k1_funct_1(sK4,sK0(sK2,sK1,sK4))
% 3.32/0.99      | m1_subset_1(sK0(sK2,X0,sK4),sK2) != iProver_top
% 3.32/0.99      | sP2_iProver_split != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_4575,c_3180]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5067,plain,
% 3.32/0.99      ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4)
% 3.32/0.99      | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
% 3.32/0.99      | sP2_iProver_split != iProver_top ),
% 3.32/0.99      inference(equality_resolution,[status(thm)],[c_4730]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2161,plain,
% 3.32/0.99      ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4)
% 3.32/0.99      | sP2_iProver_split = iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_2153,c_1371]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3172,plain,
% 3.32/0.99      ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4)
% 3.32/0.99      | sP2_iProver_split = iProver_top ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_3164,c_2161]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_8930,plain,
% 3.32/0.99      ( m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
% 3.32/0.99      | k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_5067,c_3172]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_8931,plain,
% 3.32/0.99      ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4)
% 3.32/0.99      | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top ),
% 3.32/0.99      inference(renaming,[status(thm)],[c_8930]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_8936,plain,
% 3.32/0.99      ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4)
% 3.32/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_3167,c_8931]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_12438,plain,
% 3.32/0.99      ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
% 3.32/0.99      inference(forward_subsumption_resolution,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_8936,c_1371]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 3.32/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1373,plain,
% 3.32/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.32/0.99      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_12441,plain,
% 3.32/0.99      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) = iProver_top
% 3.32/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_12438,c_1373]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_12588,plain,
% 3.32/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_12270,c_1887,c_12441]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_12600,plain,
% 3.32/0.99      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,sK1,sK4)) = k1_funct_1(sK4,sK0(sK2,sK1,sK4)) ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_4534,c_12588]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_496,plain,
% 3.32/0.99      ( m1_subset_1(X0,X1)
% 3.32/0.99      | ~ m1_subset_1(X2,sK2)
% 3.32/0.99      | k3_funct_2(sK2,sK3,sK4,X2) != X0
% 3.32/0.99      | sK1 != X1 ),
% 3.32/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_22]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_497,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,sK2)
% 3.32/0.99      | m1_subset_1(k3_funct_2(sK2,sK3,sK4,X0),sK1) ),
% 3.32/0.99      inference(unflattening,[status(thm)],[c_496]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1359,plain,
% 3.32/0.99      ( m1_subset_1(X0,sK2) != iProver_top
% 3.32/0.99      | m1_subset_1(k3_funct_2(sK2,sK3,sK4,X0),sK1) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_497]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_12639,plain,
% 3.32/0.99      ( m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
% 3.32/0.99      | m1_subset_1(k1_funct_1(sK4,sK0(sK2,sK1,sK4)),sK1) = iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_12600,c_1359]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3176,plain,
% 3.32/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top
% 3.32/0.99      | sP2_iProver_split = iProver_top ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_3164,c_2153]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_12638,plain,
% 3.32/0.99      ( m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
% 3.32/0.99      | sP2_iProver_split != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_12600,c_3180]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_12726,plain,
% 3.32/0.99      ( m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_12639,c_1887,c_3176,c_12441,c_12638]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_12731,plain,
% 3.32/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_3167,c_12726]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(contradiction,plain,
% 3.32/0.99      ( $false ),
% 3.32/0.99      inference(minisat,[status(thm)],[c_12731,c_12441,c_1887]) ).
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.32/0.99  
% 3.32/0.99  ------                               Statistics
% 3.32/0.99  
% 3.32/0.99  ------ General
% 3.32/0.99  
% 3.32/0.99  abstr_ref_over_cycles:                  0
% 3.32/0.99  abstr_ref_under_cycles:                 0
% 3.32/0.99  gc_basic_clause_elim:                   0
% 3.32/0.99  forced_gc_time:                         0
% 3.32/0.99  parsing_time:                           0.01
% 3.32/0.99  unif_index_cands_time:                  0.
% 3.32/0.99  unif_index_add_time:                    0.
% 3.32/0.99  orderings_time:                         0.
% 3.32/0.99  out_proof_time:                         0.01
% 3.32/0.99  total_time:                             0.35
% 3.32/0.99  num_of_symbols:                         55
% 3.32/0.99  num_of_terms:                           9446
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing
% 3.32/0.99  
% 3.32/0.99  num_of_splits:                          6
% 3.32/0.99  num_of_split_atoms:                     3
% 3.32/0.99  num_of_reused_defs:                     3
% 3.32/0.99  num_eq_ax_congr_red:                    16
% 3.32/0.99  num_of_sem_filtered_clauses:            1
% 3.32/0.99  num_of_subtypes:                        0
% 3.32/0.99  monotx_restored_types:                  0
% 3.32/0.99  sat_num_of_epr_types:                   0
% 3.32/0.99  sat_num_of_non_cyclic_types:            0
% 3.32/0.99  sat_guarded_non_collapsed_types:        0
% 3.32/0.99  num_pure_diseq_elim:                    0
% 3.32/0.99  simp_replaced_by:                       0
% 3.32/0.99  res_preprocessed:                       140
% 3.32/0.99  prep_upred:                             0
% 3.32/0.99  prep_unflattend:                        22
% 3.32/0.99  smt_new_axioms:                         0
% 3.32/0.99  pred_elim_cands:                        3
% 3.32/0.99  pred_elim:                              4
% 3.32/0.99  pred_elim_cl:                           -1
% 3.32/0.99  pred_elim_cycles:                       6
% 3.32/0.99  merged_defs:                            0
% 3.32/0.99  merged_defs_ncl:                        0
% 3.32/0.99  bin_hyper_res:                          0
% 3.32/0.99  prep_cycles:                            4
% 3.32/0.99  pred_elim_time:                         0.01
% 3.32/0.99  splitting_time:                         0.
% 3.32/0.99  sem_filter_time:                        0.
% 3.32/0.99  monotx_time:                            0.001
% 3.32/0.99  subtype_inf_time:                       0.
% 3.32/0.99  
% 3.32/0.99  ------ Problem properties
% 3.32/0.99  
% 3.32/0.99  clauses:                                33
% 3.32/0.99  conjectures:                            2
% 3.32/0.99  epr:                                    3
% 3.32/0.99  horn:                                   21
% 3.32/0.99  ground:                                 11
% 3.32/0.99  unary:                                  6
% 3.32/0.99  binary:                                 4
% 3.32/0.99  lits:                                   88
% 3.32/0.99  lits_eq:                                21
% 3.32/0.99  fd_pure:                                0
% 3.32/0.99  fd_pseudo:                              0
% 3.32/0.99  fd_cond:                                3
% 3.32/0.99  fd_pseudo_cond:                         0
% 3.32/0.99  ac_symbols:                             0
% 3.32/0.99  
% 3.32/0.99  ------ Propositional Solver
% 3.32/0.99  
% 3.32/0.99  prop_solver_calls:                      32
% 3.32/0.99  prop_fast_solver_calls:                 1512
% 3.32/0.99  smt_solver_calls:                       0
% 3.32/0.99  smt_fast_solver_calls:                  0
% 3.32/0.99  prop_num_of_clauses:                    3811
% 3.32/0.99  prop_preprocess_simplified:             8333
% 3.32/0.99  prop_fo_subsumed:                       47
% 3.32/0.99  prop_solver_time:                       0.
% 3.32/0.99  smt_solver_time:                        0.
% 3.32/0.99  smt_fast_solver_time:                   0.
% 3.32/0.99  prop_fast_solver_time:                  0.
% 3.32/0.99  prop_unsat_core_time:                   0.
% 3.32/0.99  
% 3.32/0.99  ------ QBF
% 3.32/0.99  
% 3.32/0.99  qbf_q_res:                              0
% 3.32/0.99  qbf_num_tautologies:                    0
% 3.32/0.99  qbf_prep_cycles:                        0
% 3.32/0.99  
% 3.32/0.99  ------ BMC1
% 3.32/0.99  
% 3.32/0.99  bmc1_current_bound:                     -1
% 3.32/0.99  bmc1_last_solved_bound:                 -1
% 3.32/0.99  bmc1_unsat_core_size:                   -1
% 3.32/0.99  bmc1_unsat_core_parents_size:           -1
% 3.32/0.99  bmc1_merge_next_fun:                    0
% 3.32/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.32/0.99  
% 3.32/0.99  ------ Instantiation
% 3.32/0.99  
% 3.32/0.99  inst_num_of_clauses:                    1223
% 3.32/0.99  inst_num_in_passive:                    472
% 3.32/0.99  inst_num_in_active:                     745
% 3.32/0.99  inst_num_in_unprocessed:                6
% 3.32/0.99  inst_num_of_loops:                      870
% 3.32/0.99  inst_num_of_learning_restarts:          0
% 3.32/0.99  inst_num_moves_active_passive:          118
% 3.32/0.99  inst_lit_activity:                      0
% 3.32/0.99  inst_lit_activity_moves:                0
% 3.32/0.99  inst_num_tautologies:                   0
% 3.32/0.99  inst_num_prop_implied:                  0
% 3.32/0.99  inst_num_existing_simplified:           0
% 3.32/0.99  inst_num_eq_res_simplified:             0
% 3.32/0.99  inst_num_child_elim:                    0
% 3.32/0.99  inst_num_of_dismatching_blockings:      883
% 3.32/0.99  inst_num_of_non_proper_insts:           1294
% 3.32/0.99  inst_num_of_duplicates:                 0
% 3.32/0.99  inst_inst_num_from_inst_to_res:         0
% 3.32/0.99  inst_dismatching_checking_time:         0.
% 3.32/0.99  
% 3.32/0.99  ------ Resolution
% 3.32/0.99  
% 3.32/0.99  res_num_of_clauses:                     0
% 3.32/0.99  res_num_in_passive:                     0
% 3.32/0.99  res_num_in_active:                      0
% 3.32/0.99  res_num_of_loops:                       144
% 3.32/0.99  res_forward_subset_subsumed:            100
% 3.32/0.99  res_backward_subset_subsumed:           2
% 3.32/0.99  res_forward_subsumed:                   0
% 3.32/0.99  res_backward_subsumed:                  0
% 3.32/0.99  res_forward_subsumption_resolution:     0
% 3.32/0.99  res_backward_subsumption_resolution:    0
% 3.32/0.99  res_clause_to_clause_subsumption:       753
% 3.32/0.99  res_orphan_elimination:                 0
% 3.32/0.99  res_tautology_del:                      144
% 3.32/0.99  res_num_eq_res_simplified:              0
% 3.32/0.99  res_num_sel_changes:                    0
% 3.32/0.99  res_moves_from_active_to_pass:          0
% 3.32/0.99  
% 3.32/0.99  ------ Superposition
% 3.32/0.99  
% 3.32/0.99  sup_time_total:                         0.
% 3.32/0.99  sup_time_generating:                    0.
% 3.32/0.99  sup_time_sim_full:                      0.
% 3.32/0.99  sup_time_sim_immed:                     0.
% 3.32/0.99  
% 3.32/0.99  sup_num_of_clauses:                     286
% 3.32/0.99  sup_num_in_active:                      149
% 3.32/0.99  sup_num_in_passive:                     137
% 3.32/0.99  sup_num_of_loops:                       172
% 3.32/0.99  sup_fw_superposition:                   78
% 3.32/0.99  sup_bw_superposition:                   236
% 3.32/0.99  sup_immediate_simplified:               58
% 3.32/0.99  sup_given_eliminated:                   0
% 3.32/0.99  comparisons_done:                       0
% 3.32/0.99  comparisons_avoided:                    288
% 3.32/0.99  
% 3.32/0.99  ------ Simplifications
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  sim_fw_subset_subsumed:                 29
% 3.32/0.99  sim_bw_subset_subsumed:                 13
% 3.32/0.99  sim_fw_subsumed:                        11
% 3.32/0.99  sim_bw_subsumed:                        1
% 3.32/0.99  sim_fw_subsumption_res:                 11
% 3.32/0.99  sim_bw_subsumption_res:                 0
% 3.32/0.99  sim_tautology_del:                      0
% 3.32/0.99  sim_eq_tautology_del:                   0
% 3.32/0.99  sim_eq_res_simp:                        2
% 3.32/0.99  sim_fw_demodulated:                     1
% 3.32/0.99  sim_bw_demodulated:                     16
% 3.32/0.99  sim_light_normalised:                   17
% 3.32/0.99  sim_joinable_taut:                      0
% 3.32/0.99  sim_joinable_simp:                      0
% 3.32/0.99  sim_ac_normalised:                      0
% 3.32/0.99  sim_smt_subsumption:                    0
% 3.32/0.99  
%------------------------------------------------------------------------------
