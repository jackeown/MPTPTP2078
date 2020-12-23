%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:13 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 786 expanded)
%              Number of clauses        :   99 ( 269 expanded)
%              Number of leaves         :   19 ( 213 expanded)
%              Depth                    :   21
%              Number of atoms          :  542 (4367 expanded)
%              Number of equality atoms :  172 ( 414 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   1 average)

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

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,
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

fof(f38,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1)
        | ~ m1_subset_1(X4,sK2) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f30,f37,f36,f35])).

fof(f65,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f38])).

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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f23])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f67,plain,(
    ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

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

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
        & r2_hidden(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
        & r2_hidden(sK0(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f33])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK0(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f74,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f59])).

fof(f63,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f73,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f60])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1893,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1895,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3269,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1893,c_1895])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1902,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2361,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1893,c_1902])).

cnf(c_3283,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3269,c_2361])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_32,plain,
    ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_22,negated_conjecture,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1363,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1390,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1363])).

cnf(c_6,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_4,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_313,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_6,c_4])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_317,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_313,c_5])).

cnf(c_318,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_317])).

cnf(c_2138,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | r1_tarski(k2_relat_1(sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_318])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2141,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),X0)
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2143,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_2141])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2149,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2234,plain,
    ( r1_tarski(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1364,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2493,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_1364])).

cnf(c_2494,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2493])).

cnf(c_1365,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2350,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),X2)
    | X2 != X1
    | k2_relset_1(sK2,sK3,sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_1365])).

cnf(c_2537,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),X0)
    | ~ r1_tarski(k2_relat_1(sK4),X1)
    | X0 != X1
    | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2350])).

cnf(c_2645,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),X0)
    | ~ r1_tarski(k2_relat_1(sK4),sK3)
    | X0 != sK3
    | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2537])).

cnf(c_2647,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(sK4),sK3)
    | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2645])).

cnf(c_3636,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3283,c_32,c_24,c_22,c_1390,c_2138,c_2143,c_2149,c_2234,c_2494,c_2647])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_17,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_538,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_539,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_678,plain,
    ( m1_subset_1(X0,X1)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X2)))
    | ~ v1_relat_1(sK4)
    | sK0(k1_relat_1(sK4),X2,sK4) != X0
    | k1_relat_1(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_539])).

cnf(c_679,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_678])).

cnf(c_1887,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_679])).

cnf(c_33,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_680,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_679])).

cnf(c_2130,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2131,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2130])).

cnf(c_3017,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1887,c_33,c_680,c_2131])).

cnf(c_3018,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3017])).

cnf(c_3643,plain,
    ( m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3636,c_3018])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_28,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_355,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_28])).

cnf(c_356,plain,
    ( ~ v1_funct_2(X0,sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | ~ m1_subset_1(X2,sK2)
    | ~ v1_funct_1(X0)
    | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_472,plain,
    ( ~ v1_funct_2(X0,sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | ~ m1_subset_1(X2,sK2)
    | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_356,c_26])).

cnf(c_473,plain,
    ( ~ v1_funct_2(sK4,sK2,X0)
    | ~ m1_subset_1(X1,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1) ),
    inference(unflattening,[status(thm)],[c_472])).

cnf(c_1890,plain,
    ( k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1)
    | v1_funct_2(sK4,sK2,X0) != iProver_top
    | m1_subset_1(X1,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_473])).

cnf(c_2181,plain,
    ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1893,c_1890])).

cnf(c_2186,plain,
    ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2181,c_32])).

cnf(c_4507,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3643,c_2186])).

cnf(c_1891,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_318])).

cnf(c_4790,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | r1_tarski(k2_relat_1(sK4),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4507,c_1891])).

cnf(c_1901,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2339,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1893,c_1901])).

cnf(c_1894,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2422,plain,
    ( r1_tarski(k2_relat_1(sK4),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2339,c_1894])).

cnf(c_5155,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,sK1,sK4)) = k1_funct_1(sK4,sK0(sK2,sK1,sK4)) ),
    inference(superposition,[status(thm)],[c_4790,c_2422])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1)
    | ~ m1_subset_1(X0,sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_18,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_523,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_26])).

cnf(c_524,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
    | ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_726,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
    | ~ m1_subset_1(X1,sK2)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)) != k3_funct_2(sK2,sK3,sK4,X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_524])).

cnf(c_727,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),sK1)
    | ~ m1_subset_1(X0,sK2)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
    inference(unflattening,[status(thm)],[c_726])).

cnf(c_1359,plain,
    ( ~ m1_subset_1(X0,sK2)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_727])).

cnf(c_1883,plain,
    ( k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
    | m1_subset_1(X0,sK2) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1359])).

cnf(c_3652,plain,
    ( k1_funct_1(sK4,sK0(sK2,sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
    | m1_subset_1(X0,sK2) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_3636,c_1883])).

cnf(c_37,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_16,plain,
    ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_553,plain,
    ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_554,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_553])).

cnf(c_708,plain,
    ( ~ m1_subset_1(X0,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X1)))
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),X1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_554])).

cnf(c_709,plain,
    ( ~ m1_subset_1(X0,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
    inference(unflattening,[status(thm)],[c_708])).

cnf(c_1361,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
    | ~ v1_relat_1(sK4)
    | sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_709])).

cnf(c_1407,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1361])).

cnf(c_2206,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
    | r1_tarski(k2_relat_1(sK4),sK1) ),
    inference(instantiation,[status(thm)],[c_318])).

cnf(c_2210,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) != iProver_top
    | r1_tarski(k2_relat_1(sK4),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2206])).

cnf(c_2243,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1363])).

cnf(c_2161,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
    | k2_relset_1(sK2,sK3,sK4) != X0
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_1365])).

cnf(c_2242,plain,
    ( ~ r1_tarski(X0,sK1)
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
    | k2_relset_1(sK2,sK3,sK4) != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2161])).

cnf(c_2413,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
    | ~ r1_tarski(k2_relat_1(sK4),sK1)
    | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2242])).

cnf(c_2414,plain,
    ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
    | sK1 != sK1
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) = iProver_top
    | r1_tarski(k2_relat_1(sK4),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2413])).

cnf(c_3755,plain,
    ( m1_subset_1(X0,sK2) != iProver_top
    | k1_funct_1(sK4,sK0(sK2,sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3652,c_24,c_33,c_37,c_1407,c_2131,c_2149,c_2210,c_2243,c_2414])).

cnf(c_3756,plain,
    ( k1_funct_1(sK4,sK0(sK2,sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3755])).

cnf(c_5263,plain,
    ( m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5155,c_3756])).

cnf(c_5274,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3643,c_5263])).

cnf(c_6825,plain,
    ( r1_tarski(k2_relat_1(sK4),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5274,c_1891])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6825,c_2414,c_2243,c_2149,c_37,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:23:59 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.72/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.03  
% 1.72/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.72/1.03  
% 1.72/1.03  ------  iProver source info
% 1.72/1.03  
% 1.72/1.03  git: date: 2020-06-30 10:37:57 +0100
% 1.72/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.72/1.03  git: non_committed_changes: false
% 1.72/1.03  git: last_make_outside_of_git: false
% 1.72/1.03  
% 1.72/1.03  ------ 
% 1.72/1.03  
% 1.72/1.03  ------ Input Options
% 1.72/1.03  
% 1.72/1.03  --out_options                           all
% 1.72/1.03  --tptp_safe_out                         true
% 1.72/1.03  --problem_path                          ""
% 1.72/1.03  --include_path                          ""
% 1.72/1.03  --clausifier                            res/vclausify_rel
% 1.72/1.03  --clausifier_options                    --mode clausify
% 1.72/1.03  --stdin                                 false
% 1.72/1.03  --stats_out                             all
% 1.72/1.03  
% 1.72/1.03  ------ General Options
% 1.72/1.03  
% 1.72/1.03  --fof                                   false
% 1.72/1.03  --time_out_real                         305.
% 1.72/1.03  --time_out_virtual                      -1.
% 1.72/1.03  --symbol_type_check                     false
% 1.72/1.03  --clausify_out                          false
% 1.72/1.03  --sig_cnt_out                           false
% 1.72/1.03  --trig_cnt_out                          false
% 1.72/1.03  --trig_cnt_out_tolerance                1.
% 1.72/1.03  --trig_cnt_out_sk_spl                   false
% 1.72/1.03  --abstr_cl_out                          false
% 1.72/1.03  
% 1.72/1.03  ------ Global Options
% 1.72/1.03  
% 1.72/1.03  --schedule                              default
% 1.72/1.03  --add_important_lit                     false
% 1.72/1.03  --prop_solver_per_cl                    1000
% 1.72/1.03  --min_unsat_core                        false
% 1.72/1.03  --soft_assumptions                      false
% 1.72/1.03  --soft_lemma_size                       3
% 1.72/1.03  --prop_impl_unit_size                   0
% 1.72/1.03  --prop_impl_unit                        []
% 1.72/1.03  --share_sel_clauses                     true
% 1.72/1.03  --reset_solvers                         false
% 1.72/1.03  --bc_imp_inh                            [conj_cone]
% 1.72/1.03  --conj_cone_tolerance                   3.
% 1.72/1.03  --extra_neg_conj                        none
% 1.72/1.03  --large_theory_mode                     true
% 1.72/1.03  --prolific_symb_bound                   200
% 1.72/1.03  --lt_threshold                          2000
% 1.72/1.03  --clause_weak_htbl                      true
% 1.72/1.03  --gc_record_bc_elim                     false
% 1.72/1.03  
% 1.72/1.03  ------ Preprocessing Options
% 1.72/1.03  
% 1.72/1.03  --preprocessing_flag                    true
% 1.72/1.03  --time_out_prep_mult                    0.1
% 1.72/1.03  --splitting_mode                        input
% 1.72/1.03  --splitting_grd                         true
% 1.72/1.03  --splitting_cvd                         false
% 1.72/1.03  --splitting_cvd_svl                     false
% 1.72/1.03  --splitting_nvd                         32
% 1.72/1.03  --sub_typing                            true
% 1.72/1.03  --prep_gs_sim                           true
% 1.72/1.03  --prep_unflatten                        true
% 1.72/1.03  --prep_res_sim                          true
% 1.72/1.03  --prep_upred                            true
% 1.72/1.03  --prep_sem_filter                       exhaustive
% 1.72/1.03  --prep_sem_filter_out                   false
% 1.72/1.03  --pred_elim                             true
% 1.72/1.03  --res_sim_input                         true
% 1.72/1.03  --eq_ax_congr_red                       true
% 1.72/1.03  --pure_diseq_elim                       true
% 1.72/1.03  --brand_transform                       false
% 1.72/1.03  --non_eq_to_eq                          false
% 1.72/1.03  --prep_def_merge                        true
% 1.72/1.03  --prep_def_merge_prop_impl              false
% 1.72/1.03  --prep_def_merge_mbd                    true
% 1.72/1.03  --prep_def_merge_tr_red                 false
% 1.72/1.03  --prep_def_merge_tr_cl                  false
% 1.72/1.03  --smt_preprocessing                     true
% 1.72/1.03  --smt_ac_axioms                         fast
% 1.72/1.03  --preprocessed_out                      false
% 1.72/1.03  --preprocessed_stats                    false
% 1.72/1.03  
% 1.72/1.03  ------ Abstraction refinement Options
% 1.72/1.03  
% 1.72/1.03  --abstr_ref                             []
% 1.72/1.03  --abstr_ref_prep                        false
% 1.72/1.03  --abstr_ref_until_sat                   false
% 1.72/1.03  --abstr_ref_sig_restrict                funpre
% 1.72/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.72/1.03  --abstr_ref_under                       []
% 1.72/1.03  
% 1.72/1.03  ------ SAT Options
% 1.72/1.03  
% 1.72/1.03  --sat_mode                              false
% 1.72/1.03  --sat_fm_restart_options                ""
% 1.72/1.03  --sat_gr_def                            false
% 1.72/1.03  --sat_epr_types                         true
% 1.72/1.03  --sat_non_cyclic_types                  false
% 1.72/1.03  --sat_finite_models                     false
% 1.72/1.03  --sat_fm_lemmas                         false
% 1.72/1.03  --sat_fm_prep                           false
% 1.72/1.03  --sat_fm_uc_incr                        true
% 1.72/1.03  --sat_out_model                         small
% 1.72/1.03  --sat_out_clauses                       false
% 1.72/1.03  
% 1.72/1.03  ------ QBF Options
% 1.72/1.03  
% 1.72/1.03  --qbf_mode                              false
% 1.72/1.03  --qbf_elim_univ                         false
% 1.72/1.03  --qbf_dom_inst                          none
% 1.72/1.03  --qbf_dom_pre_inst                      false
% 1.72/1.03  --qbf_sk_in                             false
% 1.72/1.03  --qbf_pred_elim                         true
% 1.72/1.03  --qbf_split                             512
% 1.72/1.03  
% 1.72/1.03  ------ BMC1 Options
% 1.72/1.03  
% 1.72/1.03  --bmc1_incremental                      false
% 1.72/1.03  --bmc1_axioms                           reachable_all
% 1.72/1.03  --bmc1_min_bound                        0
% 1.72/1.03  --bmc1_max_bound                        -1
% 1.72/1.03  --bmc1_max_bound_default                -1
% 1.72/1.03  --bmc1_symbol_reachability              true
% 1.72/1.03  --bmc1_property_lemmas                  false
% 1.72/1.03  --bmc1_k_induction                      false
% 1.72/1.03  --bmc1_non_equiv_states                 false
% 1.72/1.03  --bmc1_deadlock                         false
% 1.72/1.03  --bmc1_ucm                              false
% 1.72/1.03  --bmc1_add_unsat_core                   none
% 1.72/1.03  --bmc1_unsat_core_children              false
% 1.72/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.72/1.03  --bmc1_out_stat                         full
% 1.72/1.03  --bmc1_ground_init                      false
% 1.72/1.03  --bmc1_pre_inst_next_state              false
% 1.72/1.03  --bmc1_pre_inst_state                   false
% 1.72/1.03  --bmc1_pre_inst_reach_state             false
% 1.72/1.03  --bmc1_out_unsat_core                   false
% 1.72/1.03  --bmc1_aig_witness_out                  false
% 1.72/1.03  --bmc1_verbose                          false
% 1.72/1.03  --bmc1_dump_clauses_tptp                false
% 1.72/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.72/1.03  --bmc1_dump_file                        -
% 1.72/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.72/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.72/1.03  --bmc1_ucm_extend_mode                  1
% 1.72/1.03  --bmc1_ucm_init_mode                    2
% 1.72/1.03  --bmc1_ucm_cone_mode                    none
% 1.72/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.72/1.03  --bmc1_ucm_relax_model                  4
% 1.72/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.72/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.72/1.03  --bmc1_ucm_layered_model                none
% 1.72/1.03  --bmc1_ucm_max_lemma_size               10
% 1.72/1.03  
% 1.72/1.03  ------ AIG Options
% 1.72/1.03  
% 1.72/1.03  --aig_mode                              false
% 1.72/1.03  
% 1.72/1.03  ------ Instantiation Options
% 1.72/1.03  
% 1.72/1.03  --instantiation_flag                    true
% 1.72/1.03  --inst_sos_flag                         false
% 1.72/1.03  --inst_sos_phase                        true
% 1.72/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.72/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.72/1.03  --inst_lit_sel_side                     num_symb
% 1.72/1.03  --inst_solver_per_active                1400
% 1.72/1.03  --inst_solver_calls_frac                1.
% 1.72/1.03  --inst_passive_queue_type               priority_queues
% 1.72/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.72/1.03  --inst_passive_queues_freq              [25;2]
% 1.72/1.03  --inst_dismatching                      true
% 1.72/1.03  --inst_eager_unprocessed_to_passive     true
% 1.72/1.03  --inst_prop_sim_given                   true
% 1.72/1.03  --inst_prop_sim_new                     false
% 1.72/1.03  --inst_subs_new                         false
% 1.72/1.03  --inst_eq_res_simp                      false
% 1.72/1.03  --inst_subs_given                       false
% 1.72/1.03  --inst_orphan_elimination               true
% 1.72/1.03  --inst_learning_loop_flag               true
% 1.72/1.03  --inst_learning_start                   3000
% 1.72/1.03  --inst_learning_factor                  2
% 1.72/1.03  --inst_start_prop_sim_after_learn       3
% 1.72/1.03  --inst_sel_renew                        solver
% 1.72/1.03  --inst_lit_activity_flag                true
% 1.72/1.03  --inst_restr_to_given                   false
% 1.72/1.03  --inst_activity_threshold               500
% 1.72/1.03  --inst_out_proof                        true
% 1.72/1.03  
% 1.72/1.03  ------ Resolution Options
% 1.72/1.03  
% 1.72/1.03  --resolution_flag                       true
% 1.72/1.03  --res_lit_sel                           adaptive
% 1.72/1.03  --res_lit_sel_side                      none
% 1.72/1.03  --res_ordering                          kbo
% 1.72/1.03  --res_to_prop_solver                    active
% 1.72/1.03  --res_prop_simpl_new                    false
% 1.72/1.03  --res_prop_simpl_given                  true
% 1.72/1.03  --res_passive_queue_type                priority_queues
% 1.72/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.72/1.03  --res_passive_queues_freq               [15;5]
% 1.72/1.03  --res_forward_subs                      full
% 1.72/1.03  --res_backward_subs                     full
% 1.72/1.03  --res_forward_subs_resolution           true
% 1.72/1.03  --res_backward_subs_resolution          true
% 1.72/1.03  --res_orphan_elimination                true
% 1.72/1.03  --res_time_limit                        2.
% 1.72/1.03  --res_out_proof                         true
% 1.72/1.03  
% 1.72/1.03  ------ Superposition Options
% 1.72/1.03  
% 1.72/1.03  --superposition_flag                    true
% 1.72/1.03  --sup_passive_queue_type                priority_queues
% 1.72/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.72/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.72/1.03  --demod_completeness_check              fast
% 1.72/1.03  --demod_use_ground                      true
% 1.72/1.03  --sup_to_prop_solver                    passive
% 1.72/1.03  --sup_prop_simpl_new                    true
% 1.72/1.03  --sup_prop_simpl_given                  true
% 1.72/1.03  --sup_fun_splitting                     false
% 1.72/1.03  --sup_smt_interval                      50000
% 1.72/1.03  
% 1.72/1.03  ------ Superposition Simplification Setup
% 1.72/1.03  
% 1.72/1.03  --sup_indices_passive                   []
% 1.72/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.72/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/1.03  --sup_full_bw                           [BwDemod]
% 1.72/1.03  --sup_immed_triv                        [TrivRules]
% 1.72/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.72/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/1.03  --sup_immed_bw_main                     []
% 1.72/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.72/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.72/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.72/1.03  
% 1.72/1.03  ------ Combination Options
% 1.72/1.03  
% 1.72/1.03  --comb_res_mult                         3
% 1.72/1.03  --comb_sup_mult                         2
% 1.72/1.03  --comb_inst_mult                        10
% 1.72/1.03  
% 1.72/1.03  ------ Debug Options
% 1.72/1.03  
% 1.72/1.03  --dbg_backtrace                         false
% 1.72/1.03  --dbg_dump_prop_clauses                 false
% 1.72/1.03  --dbg_dump_prop_clauses_file            -
% 1.72/1.03  --dbg_out_stat                          false
% 1.72/1.03  ------ Parsing...
% 1.72/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.72/1.03  
% 1.72/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.72/1.03  
% 1.72/1.03  ------ Preprocessing... gs_s  sp: 6 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.72/1.03  
% 1.72/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.72/1.03  ------ Proving...
% 1.72/1.03  ------ Problem Properties 
% 1.72/1.03  
% 1.72/1.03  
% 1.72/1.03  clauses                                 32
% 1.72/1.03  conjectures                             3
% 1.72/1.03  EPR                                     3
% 1.72/1.03  Horn                                    20
% 1.72/1.03  unary                                   4
% 1.72/1.03  binary                                  5
% 1.72/1.03  lits                                    88
% 1.72/1.03  lits eq                                 19
% 1.72/1.03  fd_pure                                 0
% 1.72/1.03  fd_pseudo                               0
% 1.72/1.03  fd_cond                                 3
% 1.72/1.03  fd_pseudo_cond                          0
% 1.72/1.03  AC symbols                              0
% 1.72/1.03  
% 1.72/1.03  ------ Schedule dynamic 5 is on 
% 1.72/1.03  
% 1.72/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.72/1.03  
% 1.72/1.03  
% 1.72/1.03  ------ 
% 1.72/1.03  Current options:
% 1.72/1.03  ------ 
% 1.72/1.03  
% 1.72/1.03  ------ Input Options
% 1.72/1.03  
% 1.72/1.03  --out_options                           all
% 1.72/1.03  --tptp_safe_out                         true
% 1.72/1.03  --problem_path                          ""
% 1.72/1.03  --include_path                          ""
% 1.72/1.03  --clausifier                            res/vclausify_rel
% 1.72/1.03  --clausifier_options                    --mode clausify
% 1.72/1.03  --stdin                                 false
% 1.72/1.03  --stats_out                             all
% 1.72/1.03  
% 1.72/1.03  ------ General Options
% 1.72/1.03  
% 1.72/1.03  --fof                                   false
% 1.72/1.03  --time_out_real                         305.
% 1.72/1.03  --time_out_virtual                      -1.
% 1.72/1.03  --symbol_type_check                     false
% 1.72/1.03  --clausify_out                          false
% 1.72/1.03  --sig_cnt_out                           false
% 1.72/1.03  --trig_cnt_out                          false
% 1.72/1.03  --trig_cnt_out_tolerance                1.
% 1.72/1.03  --trig_cnt_out_sk_spl                   false
% 1.72/1.03  --abstr_cl_out                          false
% 1.72/1.03  
% 1.72/1.03  ------ Global Options
% 1.72/1.03  
% 1.72/1.03  --schedule                              default
% 1.72/1.03  --add_important_lit                     false
% 1.72/1.03  --prop_solver_per_cl                    1000
% 1.72/1.03  --min_unsat_core                        false
% 1.72/1.03  --soft_assumptions                      false
% 1.72/1.03  --soft_lemma_size                       3
% 1.72/1.03  --prop_impl_unit_size                   0
% 1.72/1.03  --prop_impl_unit                        []
% 1.72/1.03  --share_sel_clauses                     true
% 1.72/1.03  --reset_solvers                         false
% 1.72/1.03  --bc_imp_inh                            [conj_cone]
% 1.72/1.03  --conj_cone_tolerance                   3.
% 1.72/1.03  --extra_neg_conj                        none
% 1.72/1.03  --large_theory_mode                     true
% 1.72/1.03  --prolific_symb_bound                   200
% 1.72/1.03  --lt_threshold                          2000
% 1.72/1.03  --clause_weak_htbl                      true
% 1.72/1.03  --gc_record_bc_elim                     false
% 1.72/1.03  
% 1.72/1.03  ------ Preprocessing Options
% 1.72/1.03  
% 1.72/1.03  --preprocessing_flag                    true
% 1.72/1.03  --time_out_prep_mult                    0.1
% 1.72/1.03  --splitting_mode                        input
% 1.72/1.03  --splitting_grd                         true
% 1.72/1.03  --splitting_cvd                         false
% 1.72/1.03  --splitting_cvd_svl                     false
% 1.72/1.03  --splitting_nvd                         32
% 1.72/1.03  --sub_typing                            true
% 1.72/1.03  --prep_gs_sim                           true
% 1.72/1.03  --prep_unflatten                        true
% 1.72/1.03  --prep_res_sim                          true
% 1.72/1.03  --prep_upred                            true
% 1.72/1.03  --prep_sem_filter                       exhaustive
% 1.72/1.03  --prep_sem_filter_out                   false
% 1.72/1.03  --pred_elim                             true
% 1.72/1.03  --res_sim_input                         true
% 1.72/1.03  --eq_ax_congr_red                       true
% 1.72/1.03  --pure_diseq_elim                       true
% 1.72/1.03  --brand_transform                       false
% 1.72/1.03  --non_eq_to_eq                          false
% 1.72/1.03  --prep_def_merge                        true
% 1.72/1.03  --prep_def_merge_prop_impl              false
% 1.72/1.03  --prep_def_merge_mbd                    true
% 1.72/1.03  --prep_def_merge_tr_red                 false
% 1.72/1.03  --prep_def_merge_tr_cl                  false
% 1.72/1.03  --smt_preprocessing                     true
% 1.72/1.03  --smt_ac_axioms                         fast
% 1.72/1.03  --preprocessed_out                      false
% 1.72/1.03  --preprocessed_stats                    false
% 1.72/1.03  
% 1.72/1.03  ------ Abstraction refinement Options
% 1.72/1.03  
% 1.72/1.03  --abstr_ref                             []
% 1.72/1.03  --abstr_ref_prep                        false
% 1.72/1.03  --abstr_ref_until_sat                   false
% 1.72/1.03  --abstr_ref_sig_restrict                funpre
% 1.72/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.72/1.03  --abstr_ref_under                       []
% 1.72/1.03  
% 1.72/1.03  ------ SAT Options
% 1.72/1.03  
% 1.72/1.03  --sat_mode                              false
% 1.72/1.03  --sat_fm_restart_options                ""
% 1.72/1.03  --sat_gr_def                            false
% 1.72/1.03  --sat_epr_types                         true
% 1.72/1.03  --sat_non_cyclic_types                  false
% 1.72/1.03  --sat_finite_models                     false
% 1.72/1.03  --sat_fm_lemmas                         false
% 1.72/1.03  --sat_fm_prep                           false
% 1.72/1.03  --sat_fm_uc_incr                        true
% 1.72/1.03  --sat_out_model                         small
% 1.72/1.03  --sat_out_clauses                       false
% 1.72/1.03  
% 1.72/1.03  ------ QBF Options
% 1.72/1.03  
% 1.72/1.03  --qbf_mode                              false
% 1.72/1.03  --qbf_elim_univ                         false
% 1.72/1.03  --qbf_dom_inst                          none
% 1.72/1.03  --qbf_dom_pre_inst                      false
% 1.72/1.03  --qbf_sk_in                             false
% 1.72/1.03  --qbf_pred_elim                         true
% 1.72/1.03  --qbf_split                             512
% 1.72/1.03  
% 1.72/1.03  ------ BMC1 Options
% 1.72/1.03  
% 1.72/1.03  --bmc1_incremental                      false
% 1.72/1.03  --bmc1_axioms                           reachable_all
% 1.72/1.03  --bmc1_min_bound                        0
% 1.72/1.03  --bmc1_max_bound                        -1
% 1.72/1.03  --bmc1_max_bound_default                -1
% 1.72/1.03  --bmc1_symbol_reachability              true
% 1.72/1.03  --bmc1_property_lemmas                  false
% 1.72/1.03  --bmc1_k_induction                      false
% 1.72/1.03  --bmc1_non_equiv_states                 false
% 1.72/1.03  --bmc1_deadlock                         false
% 1.72/1.03  --bmc1_ucm                              false
% 1.72/1.03  --bmc1_add_unsat_core                   none
% 1.72/1.03  --bmc1_unsat_core_children              false
% 1.72/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.72/1.03  --bmc1_out_stat                         full
% 1.72/1.03  --bmc1_ground_init                      false
% 1.72/1.03  --bmc1_pre_inst_next_state              false
% 1.72/1.03  --bmc1_pre_inst_state                   false
% 1.72/1.03  --bmc1_pre_inst_reach_state             false
% 1.72/1.03  --bmc1_out_unsat_core                   false
% 1.72/1.03  --bmc1_aig_witness_out                  false
% 1.72/1.03  --bmc1_verbose                          false
% 1.72/1.03  --bmc1_dump_clauses_tptp                false
% 1.72/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.72/1.03  --bmc1_dump_file                        -
% 1.72/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.72/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.72/1.03  --bmc1_ucm_extend_mode                  1
% 1.72/1.03  --bmc1_ucm_init_mode                    2
% 1.72/1.03  --bmc1_ucm_cone_mode                    none
% 1.72/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.72/1.03  --bmc1_ucm_relax_model                  4
% 1.72/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.72/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.72/1.03  --bmc1_ucm_layered_model                none
% 1.72/1.03  --bmc1_ucm_max_lemma_size               10
% 1.72/1.03  
% 1.72/1.03  ------ AIG Options
% 1.72/1.03  
% 1.72/1.03  --aig_mode                              false
% 1.72/1.03  
% 1.72/1.03  ------ Instantiation Options
% 1.72/1.03  
% 1.72/1.03  --instantiation_flag                    true
% 1.72/1.03  --inst_sos_flag                         false
% 1.72/1.03  --inst_sos_phase                        true
% 1.72/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.72/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.72/1.03  --inst_lit_sel_side                     none
% 1.72/1.03  --inst_solver_per_active                1400
% 1.72/1.03  --inst_solver_calls_frac                1.
% 1.72/1.03  --inst_passive_queue_type               priority_queues
% 1.72/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.72/1.03  --inst_passive_queues_freq              [25;2]
% 1.72/1.03  --inst_dismatching                      true
% 1.72/1.03  --inst_eager_unprocessed_to_passive     true
% 1.72/1.03  --inst_prop_sim_given                   true
% 1.72/1.03  --inst_prop_sim_new                     false
% 1.72/1.03  --inst_subs_new                         false
% 1.72/1.03  --inst_eq_res_simp                      false
% 1.72/1.03  --inst_subs_given                       false
% 1.72/1.03  --inst_orphan_elimination               true
% 1.72/1.03  --inst_learning_loop_flag               true
% 1.72/1.03  --inst_learning_start                   3000
% 1.72/1.03  --inst_learning_factor                  2
% 1.72/1.03  --inst_start_prop_sim_after_learn       3
% 1.72/1.03  --inst_sel_renew                        solver
% 1.72/1.03  --inst_lit_activity_flag                true
% 1.72/1.03  --inst_restr_to_given                   false
% 1.72/1.03  --inst_activity_threshold               500
% 1.72/1.03  --inst_out_proof                        true
% 1.72/1.03  
% 1.72/1.03  ------ Resolution Options
% 1.72/1.03  
% 1.72/1.03  --resolution_flag                       false
% 1.72/1.03  --res_lit_sel                           adaptive
% 1.72/1.03  --res_lit_sel_side                      none
% 1.72/1.03  --res_ordering                          kbo
% 1.72/1.03  --res_to_prop_solver                    active
% 1.72/1.03  --res_prop_simpl_new                    false
% 1.72/1.03  --res_prop_simpl_given                  true
% 1.72/1.03  --res_passive_queue_type                priority_queues
% 1.72/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.72/1.03  --res_passive_queues_freq               [15;5]
% 1.72/1.03  --res_forward_subs                      full
% 1.72/1.03  --res_backward_subs                     full
% 1.72/1.03  --res_forward_subs_resolution           true
% 1.72/1.03  --res_backward_subs_resolution          true
% 1.72/1.03  --res_orphan_elimination                true
% 1.72/1.03  --res_time_limit                        2.
% 1.72/1.03  --res_out_proof                         true
% 1.72/1.03  
% 1.72/1.03  ------ Superposition Options
% 1.72/1.03  
% 1.72/1.03  --superposition_flag                    true
% 1.72/1.03  --sup_passive_queue_type                priority_queues
% 1.72/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.72/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.72/1.03  --demod_completeness_check              fast
% 1.72/1.03  --demod_use_ground                      true
% 1.72/1.03  --sup_to_prop_solver                    passive
% 1.72/1.03  --sup_prop_simpl_new                    true
% 1.72/1.03  --sup_prop_simpl_given                  true
% 1.72/1.03  --sup_fun_splitting                     false
% 1.72/1.03  --sup_smt_interval                      50000
% 1.72/1.03  
% 1.72/1.03  ------ Superposition Simplification Setup
% 1.72/1.03  
% 1.72/1.03  --sup_indices_passive                   []
% 1.72/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.72/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/1.03  --sup_full_bw                           [BwDemod]
% 1.72/1.03  --sup_immed_triv                        [TrivRules]
% 1.72/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.72/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/1.03  --sup_immed_bw_main                     []
% 1.72/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.72/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.72/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.72/1.03  
% 1.72/1.03  ------ Combination Options
% 1.72/1.03  
% 1.72/1.03  --comb_res_mult                         3
% 1.72/1.03  --comb_sup_mult                         2
% 1.72/1.03  --comb_inst_mult                        10
% 1.72/1.03  
% 1.72/1.03  ------ Debug Options
% 1.72/1.03  
% 1.72/1.03  --dbg_backtrace                         false
% 1.72/1.03  --dbg_dump_prop_clauses                 false
% 1.72/1.03  --dbg_dump_prop_clauses_file            -
% 1.72/1.03  --dbg_out_stat                          false
% 1.72/1.03  
% 1.72/1.03  
% 1.72/1.03  
% 1.72/1.03  
% 1.72/1.03  ------ Proving...
% 1.72/1.03  
% 1.72/1.03  
% 1.72/1.03  % SZS status Theorem for theBenchmark.p
% 1.72/1.03  
% 1.72/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 1.72/1.03  
% 1.72/1.03  fof(f12,conjecture,(
% 1.72/1.03    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 1.72/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.72/1.03  
% 1.72/1.03  fof(f13,negated_conjecture,(
% 1.72/1.03    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 1.72/1.03    inference(negated_conjecture,[],[f12])).
% 1.72/1.03  
% 1.72/1.03  fof(f29,plain,(
% 1.72/1.03    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 1.72/1.03    inference(ennf_transformation,[],[f13])).
% 1.72/1.03  
% 1.72/1.03  fof(f30,plain,(
% 1.72/1.03    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 1.72/1.03    inference(flattening,[],[f29])).
% 1.72/1.03  
% 1.72/1.03  fof(f37,plain,(
% 1.72/1.03    ( ! [X2,X0,X1] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (~r1_tarski(k2_relset_1(X1,X2,sK4),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,sK4,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 1.72/1.03    introduced(choice_axiom,[])).
% 1.72/1.03  
% 1.72/1.03  fof(f36,plain,(
% 1.72/1.03    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (~r1_tarski(k2_relset_1(X1,sK3,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,sK3,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK3))) & v1_funct_2(X3,X1,sK3) & v1_funct_1(X3)) & ~v1_xboole_0(sK3))) )),
% 1.72/1.03    introduced(choice_axiom,[])).
% 1.72/1.03  
% 1.72/1.03  fof(f35,plain,(
% 1.72/1.03    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK2,X2,X3),sK1) & ! [X4] : (r2_hidden(k3_funct_2(sK2,X2,X3,X4),sK1) | ~m1_subset_1(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X2))) & v1_funct_2(X3,sK2,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK2))),
% 1.72/1.03    introduced(choice_axiom,[])).
% 1.72/1.03  
% 1.72/1.03  fof(f38,plain,(
% 1.72/1.03    ((~r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) & ! [X4] : (r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1) | ~m1_subset_1(X4,sK2)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 1.72/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f30,f37,f36,f35])).
% 1.72/1.03  
% 1.72/1.03  fof(f65,plain,(
% 1.72/1.03    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 1.72/1.03    inference(cnf_transformation,[],[f38])).
% 1.72/1.03  
% 1.72/1.03  fof(f9,axiom,(
% 1.72/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.72/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.72/1.03  
% 1.72/1.03  fof(f23,plain,(
% 1.72/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.72/1.03    inference(ennf_transformation,[],[f9])).
% 1.72/1.03  
% 1.72/1.03  fof(f24,plain,(
% 1.72/1.03    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.72/1.03    inference(flattening,[],[f23])).
% 1.72/1.03  
% 1.72/1.03  fof(f32,plain,(
% 1.72/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.72/1.03    inference(nnf_transformation,[],[f24])).
% 1.72/1.03  
% 1.72/1.03  fof(f48,plain,(
% 1.72/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.72/1.03    inference(cnf_transformation,[],[f32])).
% 1.72/1.03  
% 1.72/1.03  fof(f7,axiom,(
% 1.72/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.72/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.72/1.03  
% 1.72/1.03  fof(f21,plain,(
% 1.72/1.03    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.72/1.03    inference(ennf_transformation,[],[f7])).
% 1.72/1.03  
% 1.72/1.03  fof(f46,plain,(
% 1.72/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.72/1.03    inference(cnf_transformation,[],[f21])).
% 1.72/1.03  
% 1.72/1.03  fof(f64,plain,(
% 1.72/1.03    v1_funct_2(sK4,sK2,sK3)),
% 1.72/1.03    inference(cnf_transformation,[],[f38])).
% 1.72/1.03  
% 1.72/1.03  fof(f67,plain,(
% 1.72/1.03    ~r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)),
% 1.72/1.03    inference(cnf_transformation,[],[f38])).
% 1.72/1.03  
% 1.72/1.03  fof(f6,axiom,(
% 1.72/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.72/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.72/1.03  
% 1.72/1.03  fof(f14,plain,(
% 1.72/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.72/1.03    inference(pure_predicate_removal,[],[f6])).
% 1.72/1.03  
% 1.72/1.03  fof(f20,plain,(
% 1.72/1.03    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.72/1.03    inference(ennf_transformation,[],[f14])).
% 1.72/1.03  
% 1.72/1.03  fof(f45,plain,(
% 1.72/1.03    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.72/1.03    inference(cnf_transformation,[],[f20])).
% 1.72/1.03  
% 1.72/1.03  fof(f4,axiom,(
% 1.72/1.03    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.72/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.72/1.03  
% 1.72/1.03  fof(f18,plain,(
% 1.72/1.03    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.72/1.03    inference(ennf_transformation,[],[f4])).
% 1.72/1.03  
% 1.72/1.03  fof(f31,plain,(
% 1.72/1.03    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.72/1.03    inference(nnf_transformation,[],[f18])).
% 1.72/1.03  
% 1.72/1.03  fof(f42,plain,(
% 1.72/1.03    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.72/1.03    inference(cnf_transformation,[],[f31])).
% 1.72/1.03  
% 1.72/1.03  fof(f5,axiom,(
% 1.72/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.72/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.72/1.03  
% 1.72/1.03  fof(f19,plain,(
% 1.72/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.72/1.03    inference(ennf_transformation,[],[f5])).
% 1.72/1.03  
% 1.72/1.03  fof(f44,plain,(
% 1.72/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.72/1.03    inference(cnf_transformation,[],[f19])).
% 1.72/1.03  
% 1.72/1.03  fof(f1,axiom,(
% 1.72/1.03    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.72/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.72/1.03  
% 1.72/1.03  fof(f15,plain,(
% 1.72/1.03    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.72/1.03    inference(ennf_transformation,[],[f1])).
% 1.72/1.03  
% 1.72/1.03  fof(f16,plain,(
% 1.72/1.03    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.72/1.03    inference(flattening,[],[f15])).
% 1.72/1.03  
% 1.72/1.03  fof(f39,plain,(
% 1.72/1.03    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.72/1.03    inference(cnf_transformation,[],[f16])).
% 1.72/1.03  
% 1.72/1.03  fof(f8,axiom,(
% 1.72/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.72/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.72/1.03  
% 1.72/1.03  fof(f22,plain,(
% 1.72/1.03    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.72/1.03    inference(ennf_transformation,[],[f8])).
% 1.72/1.03  
% 1.72/1.03  fof(f47,plain,(
% 1.72/1.03    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.72/1.03    inference(cnf_transformation,[],[f22])).
% 1.72/1.03  
% 1.72/1.03  fof(f2,axiom,(
% 1.72/1.03    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.72/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.72/1.03  
% 1.72/1.03  fof(f40,plain,(
% 1.72/1.03    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.72/1.03    inference(cnf_transformation,[],[f2])).
% 1.72/1.03  
% 1.72/1.03  fof(f3,axiom,(
% 1.72/1.03    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.72/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.72/1.03  
% 1.72/1.03  fof(f17,plain,(
% 1.72/1.03    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.72/1.03    inference(ennf_transformation,[],[f3])).
% 1.72/1.03  
% 1.72/1.03  fof(f41,plain,(
% 1.72/1.03    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.72/1.03    inference(cnf_transformation,[],[f17])).
% 1.72/1.03  
% 1.72/1.03  fof(f11,axiom,(
% 1.72/1.03    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.72/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.72/1.03  
% 1.72/1.03  fof(f27,plain,(
% 1.72/1.03    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.72/1.03    inference(ennf_transformation,[],[f11])).
% 1.72/1.03  
% 1.72/1.03  fof(f28,plain,(
% 1.72/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.72/1.03    inference(flattening,[],[f27])).
% 1.72/1.03  
% 1.72/1.03  fof(f33,plain,(
% 1.72/1.03    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),X0)))),
% 1.72/1.03    introduced(choice_axiom,[])).
% 1.72/1.03  
% 1.72/1.03  fof(f34,plain,(
% 1.72/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.72/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f33])).
% 1.72/1.03  
% 1.72/1.03  fof(f59,plain,(
% 1.72/1.03    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK0(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.72/1.03    inference(cnf_transformation,[],[f34])).
% 1.72/1.03  
% 1.72/1.03  fof(f74,plain,(
% 1.72/1.03    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.72/1.03    inference(equality_resolution,[],[f59])).
% 1.72/1.03  
% 1.72/1.03  fof(f63,plain,(
% 1.72/1.03    v1_funct_1(sK4)),
% 1.72/1.03    inference(cnf_transformation,[],[f38])).
% 1.72/1.03  
% 1.72/1.03  fof(f10,axiom,(
% 1.72/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 1.72/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.72/1.03  
% 1.72/1.03  fof(f25,plain,(
% 1.72/1.03    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 1.72/1.03    inference(ennf_transformation,[],[f10])).
% 1.72/1.03  
% 1.72/1.03  fof(f26,plain,(
% 1.72/1.03    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 1.72/1.03    inference(flattening,[],[f25])).
% 1.72/1.03  
% 1.72/1.03  fof(f54,plain,(
% 1.72/1.03    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 1.72/1.03    inference(cnf_transformation,[],[f26])).
% 1.72/1.03  
% 1.72/1.03  fof(f61,plain,(
% 1.72/1.03    ~v1_xboole_0(sK2)),
% 1.72/1.03    inference(cnf_transformation,[],[f38])).
% 1.72/1.03  
% 1.72/1.03  fof(f66,plain,(
% 1.72/1.03    ( ! [X4] : (r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1) | ~m1_subset_1(X4,sK2)) )),
% 1.72/1.03    inference(cnf_transformation,[],[f38])).
% 1.72/1.03  
% 1.72/1.03  fof(f58,plain,(
% 1.72/1.03    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.72/1.03    inference(cnf_transformation,[],[f34])).
% 1.72/1.03  
% 1.72/1.03  fof(f75,plain,(
% 1.72/1.03    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | ~r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.72/1.03    inference(equality_resolution,[],[f58])).
% 1.72/1.03  
% 1.72/1.03  fof(f60,plain,(
% 1.72/1.03    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.72/1.03    inference(cnf_transformation,[],[f34])).
% 1.72/1.03  
% 1.72/1.03  fof(f73,plain,(
% 1.72/1.03    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.72/1.03    inference(equality_resolution,[],[f60])).
% 1.72/1.03  
% 1.72/1.03  cnf(c_24,negated_conjecture,
% 1.72/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 1.72/1.03      inference(cnf_transformation,[],[f65]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1893,plain,
% 1.72/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 1.72/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_14,plain,
% 1.72/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 1.72/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.72/1.03      | k1_relset_1(X1,X2,X0) = X1
% 1.72/1.03      | k1_xboole_0 = X2 ),
% 1.72/1.03      inference(cnf_transformation,[],[f48]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1895,plain,
% 1.72/1.03      ( k1_relset_1(X0,X1,X2) = X0
% 1.72/1.03      | k1_xboole_0 = X1
% 1.72/1.03      | v1_funct_2(X2,X0,X1) != iProver_top
% 1.72/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.72/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_3269,plain,
% 1.72/1.03      ( k1_relset_1(sK2,sK3,sK4) = sK2
% 1.72/1.03      | sK3 = k1_xboole_0
% 1.72/1.03      | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
% 1.72/1.03      inference(superposition,[status(thm)],[c_1893,c_1895]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_7,plain,
% 1.72/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.72/1.03      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.72/1.03      inference(cnf_transformation,[],[f46]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1902,plain,
% 1.72/1.03      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.72/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.72/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2361,plain,
% 1.72/1.03      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 1.72/1.03      inference(superposition,[status(thm)],[c_1893,c_1902]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_3283,plain,
% 1.72/1.03      ( k1_relat_1(sK4) = sK2
% 1.72/1.03      | sK3 = k1_xboole_0
% 1.72/1.03      | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
% 1.72/1.03      inference(demodulation,[status(thm)],[c_3269,c_2361]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_25,negated_conjecture,
% 1.72/1.03      ( v1_funct_2(sK4,sK2,sK3) ),
% 1.72/1.03      inference(cnf_transformation,[],[f64]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_32,plain,
% 1.72/1.03      ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
% 1.72/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_22,negated_conjecture,
% 1.72/1.03      ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
% 1.72/1.03      inference(cnf_transformation,[],[f67]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1363,plain,( X0 = X0 ),theory(equality) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1390,plain,
% 1.72/1.03      ( k1_xboole_0 = k1_xboole_0 ),
% 1.72/1.03      inference(instantiation,[status(thm)],[c_1363]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_6,plain,
% 1.72/1.03      ( v5_relat_1(X0,X1)
% 1.72/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 1.72/1.03      inference(cnf_transformation,[],[f45]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_4,plain,
% 1.72/1.03      ( ~ v5_relat_1(X0,X1)
% 1.72/1.03      | r1_tarski(k2_relat_1(X0),X1)
% 1.72/1.03      | ~ v1_relat_1(X0) ),
% 1.72/1.03      inference(cnf_transformation,[],[f42]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_313,plain,
% 1.72/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.72/1.03      | r1_tarski(k2_relat_1(X0),X2)
% 1.72/1.03      | ~ v1_relat_1(X0) ),
% 1.72/1.03      inference(resolution,[status(thm)],[c_6,c_4]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_5,plain,
% 1.72/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.72/1.03      | v1_relat_1(X0) ),
% 1.72/1.03      inference(cnf_transformation,[],[f44]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_317,plain,
% 1.72/1.03      ( r1_tarski(k2_relat_1(X0),X2)
% 1.72/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.72/1.03      inference(global_propositional_subsumption,
% 1.72/1.03                [status(thm)],
% 1.72/1.03                [c_313,c_5]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_318,plain,
% 1.72/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.72/1.03      | r1_tarski(k2_relat_1(X0),X2) ),
% 1.72/1.03      inference(renaming,[status(thm)],[c_317]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2138,plain,
% 1.72/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 1.72/1.03      | r1_tarski(k2_relat_1(sK4),sK3) ),
% 1.72/1.03      inference(instantiation,[status(thm)],[c_318]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_0,plain,
% 1.72/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 1.72/1.03      inference(cnf_transformation,[],[f39]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2141,plain,
% 1.72/1.03      ( ~ r1_tarski(X0,sK1)
% 1.72/1.03      | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),X0)
% 1.72/1.03      | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
% 1.72/1.03      inference(instantiation,[status(thm)],[c_0]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2143,plain,
% 1.72/1.03      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
% 1.72/1.03      | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_xboole_0)
% 1.72/1.03      | ~ r1_tarski(k1_xboole_0,sK1) ),
% 1.72/1.03      inference(instantiation,[status(thm)],[c_2141]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_8,plain,
% 1.72/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.72/1.03      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.72/1.03      inference(cnf_transformation,[],[f47]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2149,plain,
% 1.72/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 1.72/1.03      | k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 1.72/1.03      inference(instantiation,[status(thm)],[c_8]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1,plain,
% 1.72/1.03      ( r1_tarski(k1_xboole_0,X0) ),
% 1.72/1.03      inference(cnf_transformation,[],[f40]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2234,plain,
% 1.72/1.03      ( r1_tarski(k1_xboole_0,sK1) ),
% 1.72/1.03      inference(instantiation,[status(thm)],[c_1]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1364,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2493,plain,
% 1.72/1.03      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 1.72/1.03      inference(instantiation,[status(thm)],[c_1364]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2494,plain,
% 1.72/1.03      ( sK3 != k1_xboole_0
% 1.72/1.03      | k1_xboole_0 = sK3
% 1.72/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 1.72/1.03      inference(instantiation,[status(thm)],[c_2493]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1365,plain,
% 1.72/1.03      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.72/1.03      theory(equality) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2350,plain,
% 1.72/1.03      ( ~ r1_tarski(X0,X1)
% 1.72/1.03      | r1_tarski(k2_relset_1(sK2,sK3,sK4),X2)
% 1.72/1.03      | X2 != X1
% 1.72/1.03      | k2_relset_1(sK2,sK3,sK4) != X0 ),
% 1.72/1.03      inference(instantiation,[status(thm)],[c_1365]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2537,plain,
% 1.72/1.03      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),X0)
% 1.72/1.03      | ~ r1_tarski(k2_relat_1(sK4),X1)
% 1.72/1.03      | X0 != X1
% 1.72/1.03      | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4) ),
% 1.72/1.03      inference(instantiation,[status(thm)],[c_2350]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2645,plain,
% 1.72/1.03      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),X0)
% 1.72/1.03      | ~ r1_tarski(k2_relat_1(sK4),sK3)
% 1.72/1.03      | X0 != sK3
% 1.72/1.03      | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4) ),
% 1.72/1.03      inference(instantiation,[status(thm)],[c_2537]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2647,plain,
% 1.72/1.03      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_xboole_0)
% 1.72/1.03      | ~ r1_tarski(k2_relat_1(sK4),sK3)
% 1.72/1.03      | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
% 1.72/1.03      | k1_xboole_0 != sK3 ),
% 1.72/1.03      inference(instantiation,[status(thm)],[c_2645]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_3636,plain,
% 1.72/1.03      ( k1_relat_1(sK4) = sK2 ),
% 1.72/1.03      inference(global_propositional_subsumption,
% 1.72/1.03                [status(thm)],
% 1.72/1.03                [c_3283,c_32,c_24,c_22,c_1390,c_2138,c_2143,c_2149,
% 1.72/1.03                 c_2234,c_2494,c_2647]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2,plain,
% 1.72/1.03      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 1.72/1.03      inference(cnf_transformation,[],[f41]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_17,plain,
% 1.72/1.03      ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 1.72/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 1.72/1.03      | ~ v1_funct_1(X0)
% 1.72/1.03      | ~ v1_relat_1(X0) ),
% 1.72/1.03      inference(cnf_transformation,[],[f74]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_26,negated_conjecture,
% 1.72/1.03      ( v1_funct_1(sK4) ),
% 1.72/1.03      inference(cnf_transformation,[],[f63]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_538,plain,
% 1.72/1.03      ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 1.72/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 1.72/1.03      | ~ v1_relat_1(X0)
% 1.72/1.03      | sK4 != X0 ),
% 1.72/1.03      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_539,plain,
% 1.72/1.03      ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
% 1.72/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 1.72/1.03      | ~ v1_relat_1(sK4) ),
% 1.72/1.03      inference(unflattening,[status(thm)],[c_538]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_678,plain,
% 1.72/1.03      ( m1_subset_1(X0,X1)
% 1.72/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X2)))
% 1.72/1.03      | ~ v1_relat_1(sK4)
% 1.72/1.03      | sK0(k1_relat_1(sK4),X2,sK4) != X0
% 1.72/1.03      | k1_relat_1(sK4) != X1 ),
% 1.72/1.03      inference(resolution_lifted,[status(thm)],[c_2,c_539]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_679,plain,
% 1.72/1.03      ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
% 1.72/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 1.72/1.03      | ~ v1_relat_1(sK4) ),
% 1.72/1.03      inference(unflattening,[status(thm)],[c_678]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1887,plain,
% 1.72/1.03      ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 1.72/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 1.72/1.03      | v1_relat_1(sK4) != iProver_top ),
% 1.72/1.03      inference(predicate_to_equality,[status(thm)],[c_679]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_33,plain,
% 1.72/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 1.72/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_680,plain,
% 1.72/1.03      ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 1.72/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 1.72/1.03      | v1_relat_1(sK4) != iProver_top ),
% 1.72/1.03      inference(predicate_to_equality,[status(thm)],[c_679]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2130,plain,
% 1.72/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 1.72/1.03      | v1_relat_1(sK4) ),
% 1.72/1.03      inference(instantiation,[status(thm)],[c_5]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2131,plain,
% 1.72/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 1.72/1.03      | v1_relat_1(sK4) = iProver_top ),
% 1.72/1.03      inference(predicate_to_equality,[status(thm)],[c_2130]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_3017,plain,
% 1.72/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 1.72/1.03      | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top ),
% 1.72/1.03      inference(global_propositional_subsumption,
% 1.72/1.03                [status(thm)],
% 1.72/1.03                [c_1887,c_33,c_680,c_2131]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_3018,plain,
% 1.72/1.03      ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 1.72/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
% 1.72/1.03      inference(renaming,[status(thm)],[c_3017]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_3643,plain,
% 1.72/1.03      ( m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
% 1.72/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
% 1.72/1.03      inference(demodulation,[status(thm)],[c_3636,c_3018]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_15,plain,
% 1.72/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 1.72/1.03      | ~ m1_subset_1(X3,X1)
% 1.72/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.72/1.03      | v1_xboole_0(X1)
% 1.72/1.03      | ~ v1_funct_1(X0)
% 1.72/1.03      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 1.72/1.03      inference(cnf_transformation,[],[f54]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_28,negated_conjecture,
% 1.72/1.03      ( ~ v1_xboole_0(sK2) ),
% 1.72/1.03      inference(cnf_transformation,[],[f61]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_355,plain,
% 1.72/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 1.72/1.03      | ~ m1_subset_1(X3,X1)
% 1.72/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.72/1.03      | ~ v1_funct_1(X0)
% 1.72/1.03      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
% 1.72/1.03      | sK2 != X1 ),
% 1.72/1.03      inference(resolution_lifted,[status(thm)],[c_15,c_28]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_356,plain,
% 1.72/1.03      ( ~ v1_funct_2(X0,sK2,X1)
% 1.72/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
% 1.72/1.03      | ~ m1_subset_1(X2,sK2)
% 1.72/1.03      | ~ v1_funct_1(X0)
% 1.72/1.03      | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2) ),
% 1.72/1.03      inference(unflattening,[status(thm)],[c_355]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_472,plain,
% 1.72/1.03      ( ~ v1_funct_2(X0,sK2,X1)
% 1.72/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
% 1.72/1.03      | ~ m1_subset_1(X2,sK2)
% 1.72/1.03      | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2)
% 1.72/1.03      | sK4 != X0 ),
% 1.72/1.03      inference(resolution_lifted,[status(thm)],[c_356,c_26]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_473,plain,
% 1.72/1.03      ( ~ v1_funct_2(sK4,sK2,X0)
% 1.72/1.03      | ~ m1_subset_1(X1,sK2)
% 1.72/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 1.72/1.03      | k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1) ),
% 1.72/1.03      inference(unflattening,[status(thm)],[c_472]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1890,plain,
% 1.72/1.03      ( k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1)
% 1.72/1.03      | v1_funct_2(sK4,sK2,X0) != iProver_top
% 1.72/1.03      | m1_subset_1(X1,sK2) != iProver_top
% 1.72/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
% 1.72/1.03      inference(predicate_to_equality,[status(thm)],[c_473]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2181,plain,
% 1.72/1.03      ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
% 1.72/1.03      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 1.72/1.03      | m1_subset_1(X0,sK2) != iProver_top ),
% 1.72/1.03      inference(superposition,[status(thm)],[c_1893,c_1890]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2186,plain,
% 1.72/1.03      ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
% 1.72/1.03      | m1_subset_1(X0,sK2) != iProver_top ),
% 1.72/1.03      inference(global_propositional_subsumption,
% 1.72/1.03                [status(thm)],
% 1.72/1.03                [c_2181,c_32]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_4507,plain,
% 1.72/1.03      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 1.72/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
% 1.72/1.03      inference(superposition,[status(thm)],[c_3643,c_2186]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1891,plain,
% 1.72/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 1.72/1.03      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 1.72/1.03      inference(predicate_to_equality,[status(thm)],[c_318]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_4790,plain,
% 1.72/1.03      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 1.72/1.03      | r1_tarski(k2_relat_1(sK4),X0) = iProver_top ),
% 1.72/1.03      inference(superposition,[status(thm)],[c_4507,c_1891]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1901,plain,
% 1.72/1.03      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 1.72/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.72/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2339,plain,
% 1.72/1.03      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 1.72/1.03      inference(superposition,[status(thm)],[c_1893,c_1901]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1894,plain,
% 1.72/1.03      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) != iProver_top ),
% 1.72/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2422,plain,
% 1.72/1.03      ( r1_tarski(k2_relat_1(sK4),sK1) != iProver_top ),
% 1.72/1.03      inference(demodulation,[status(thm)],[c_2339,c_1894]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_5155,plain,
% 1.72/1.03      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,sK1,sK4)) = k1_funct_1(sK4,sK0(sK2,sK1,sK4)) ),
% 1.72/1.03      inference(superposition,[status(thm)],[c_4790,c_2422]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_23,negated_conjecture,
% 1.72/1.03      ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1)
% 1.72/1.03      | ~ m1_subset_1(X0,sK2) ),
% 1.72/1.03      inference(cnf_transformation,[],[f66]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_18,plain,
% 1.72/1.03      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 1.72/1.03      | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 1.72/1.03      | ~ v1_funct_1(X0)
% 1.72/1.03      | ~ v1_relat_1(X0) ),
% 1.72/1.03      inference(cnf_transformation,[],[f75]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_523,plain,
% 1.72/1.03      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 1.72/1.03      | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 1.72/1.03      | ~ v1_relat_1(X0)
% 1.72/1.03      | sK4 != X0 ),
% 1.72/1.03      inference(resolution_lifted,[status(thm)],[c_18,c_26]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_524,plain,
% 1.72/1.03      ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
% 1.72/1.03      | ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
% 1.72/1.03      | ~ v1_relat_1(sK4) ),
% 1.72/1.03      inference(unflattening,[status(thm)],[c_523]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_726,plain,
% 1.72/1.03      ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
% 1.72/1.03      | ~ m1_subset_1(X1,sK2)
% 1.72/1.03      | ~ v1_relat_1(sK4)
% 1.72/1.03      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)) != k3_funct_2(sK2,sK3,sK4,X1)
% 1.72/1.03      | sK1 != X0 ),
% 1.72/1.03      inference(resolution_lifted,[status(thm)],[c_23,c_524]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_727,plain,
% 1.72/1.03      ( v1_funct_2(sK4,k1_relat_1(sK4),sK1)
% 1.72/1.03      | ~ m1_subset_1(X0,sK2)
% 1.72/1.03      | ~ v1_relat_1(sK4)
% 1.72/1.03      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
% 1.72/1.03      inference(unflattening,[status(thm)],[c_726]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1359,plain,
% 1.72/1.03      ( ~ m1_subset_1(X0,sK2)
% 1.72/1.03      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
% 1.72/1.03      | ~ sP2_iProver_split ),
% 1.72/1.03      inference(splitting,
% 1.72/1.03                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 1.72/1.03                [c_727]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1883,plain,
% 1.72/1.03      ( k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
% 1.72/1.03      | m1_subset_1(X0,sK2) != iProver_top
% 1.72/1.03      | sP2_iProver_split != iProver_top ),
% 1.72/1.03      inference(predicate_to_equality,[status(thm)],[c_1359]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_3652,plain,
% 1.72/1.03      ( k1_funct_1(sK4,sK0(sK2,sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
% 1.72/1.03      | m1_subset_1(X0,sK2) != iProver_top
% 1.72/1.03      | sP2_iProver_split != iProver_top ),
% 1.72/1.03      inference(demodulation,[status(thm)],[c_3636,c_1883]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_37,plain,
% 1.72/1.03      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) != iProver_top ),
% 1.72/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_16,plain,
% 1.72/1.03      ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 1.72/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 1.72/1.03      | ~ v1_funct_1(X0)
% 1.72/1.03      | ~ v1_relat_1(X0) ),
% 1.72/1.03      inference(cnf_transformation,[],[f73]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_553,plain,
% 1.72/1.03      ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 1.72/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 1.72/1.03      | ~ v1_relat_1(X0)
% 1.72/1.03      | sK4 != X0 ),
% 1.72/1.03      inference(resolution_lifted,[status(thm)],[c_16,c_26]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_554,plain,
% 1.72/1.03      ( ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
% 1.72/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 1.72/1.03      | ~ v1_relat_1(sK4) ),
% 1.72/1.03      inference(unflattening,[status(thm)],[c_553]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_708,plain,
% 1.72/1.03      ( ~ m1_subset_1(X0,sK2)
% 1.72/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X1)))
% 1.72/1.03      | ~ v1_relat_1(sK4)
% 1.72/1.03      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),X1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
% 1.72/1.03      | sK1 != X1 ),
% 1.72/1.03      inference(resolution_lifted,[status(thm)],[c_23,c_554]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_709,plain,
% 1.72/1.03      ( ~ m1_subset_1(X0,sK2)
% 1.72/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
% 1.72/1.03      | ~ v1_relat_1(sK4)
% 1.72/1.03      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
% 1.72/1.03      inference(unflattening,[status(thm)],[c_708]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1361,plain,
% 1.72/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
% 1.72/1.03      | ~ v1_relat_1(sK4)
% 1.72/1.03      | sP2_iProver_split ),
% 1.72/1.03      inference(splitting,
% 1.72/1.03                [splitting(split),new_symbols(definition,[])],
% 1.72/1.03                [c_709]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_1407,plain,
% 1.72/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
% 1.72/1.03      | v1_relat_1(sK4) != iProver_top
% 1.72/1.03      | sP2_iProver_split = iProver_top ),
% 1.72/1.03      inference(predicate_to_equality,[status(thm)],[c_1361]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2206,plain,
% 1.72/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
% 1.72/1.03      | r1_tarski(k2_relat_1(sK4),sK1) ),
% 1.72/1.03      inference(instantiation,[status(thm)],[c_318]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2210,plain,
% 1.72/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) != iProver_top
% 1.72/1.03      | r1_tarski(k2_relat_1(sK4),sK1) = iProver_top ),
% 1.72/1.03      inference(predicate_to_equality,[status(thm)],[c_2206]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2243,plain,
% 1.72/1.03      ( sK1 = sK1 ),
% 1.72/1.03      inference(instantiation,[status(thm)],[c_1363]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2161,plain,
% 1.72/1.03      ( ~ r1_tarski(X0,X1)
% 1.72/1.03      | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
% 1.72/1.03      | k2_relset_1(sK2,sK3,sK4) != X0
% 1.72/1.03      | sK1 != X1 ),
% 1.72/1.03      inference(instantiation,[status(thm)],[c_1365]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2242,plain,
% 1.72/1.03      ( ~ r1_tarski(X0,sK1)
% 1.72/1.03      | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
% 1.72/1.03      | k2_relset_1(sK2,sK3,sK4) != X0
% 1.72/1.03      | sK1 != sK1 ),
% 1.72/1.03      inference(instantiation,[status(thm)],[c_2161]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2413,plain,
% 1.72/1.03      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
% 1.72/1.03      | ~ r1_tarski(k2_relat_1(sK4),sK1)
% 1.72/1.03      | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
% 1.72/1.03      | sK1 != sK1 ),
% 1.72/1.03      inference(instantiation,[status(thm)],[c_2242]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_2414,plain,
% 1.72/1.03      ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
% 1.72/1.03      | sK1 != sK1
% 1.72/1.03      | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) = iProver_top
% 1.72/1.03      | r1_tarski(k2_relat_1(sK4),sK1) != iProver_top ),
% 1.72/1.03      inference(predicate_to_equality,[status(thm)],[c_2413]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_3755,plain,
% 1.72/1.03      ( m1_subset_1(X0,sK2) != iProver_top
% 1.72/1.03      | k1_funct_1(sK4,sK0(sK2,sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
% 1.72/1.03      inference(global_propositional_subsumption,
% 1.72/1.03                [status(thm)],
% 1.72/1.03                [c_3652,c_24,c_33,c_37,c_1407,c_2131,c_2149,c_2210,
% 1.72/1.03                 c_2243,c_2414]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_3756,plain,
% 1.72/1.03      ( k1_funct_1(sK4,sK0(sK2,sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
% 1.72/1.03      | m1_subset_1(X0,sK2) != iProver_top ),
% 1.72/1.03      inference(renaming,[status(thm)],[c_3755]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_5263,plain,
% 1.72/1.03      ( m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top ),
% 1.72/1.03      inference(superposition,[status(thm)],[c_5155,c_3756]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_5274,plain,
% 1.72/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 1.72/1.03      inference(superposition,[status(thm)],[c_3643,c_5263]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(c_6825,plain,
% 1.72/1.03      ( r1_tarski(k2_relat_1(sK4),sK1) = iProver_top ),
% 1.72/1.03      inference(superposition,[status(thm)],[c_5274,c_1891]) ).
% 1.72/1.03  
% 1.72/1.03  cnf(contradiction,plain,
% 1.72/1.03      ( $false ),
% 1.72/1.03      inference(minisat,
% 1.72/1.03                [status(thm)],
% 1.72/1.03                [c_6825,c_2414,c_2243,c_2149,c_37,c_24]) ).
% 1.72/1.03  
% 1.72/1.03  
% 1.72/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 1.72/1.03  
% 1.72/1.03  ------                               Statistics
% 1.72/1.03  
% 1.72/1.03  ------ General
% 1.72/1.03  
% 1.72/1.03  abstr_ref_over_cycles:                  0
% 1.72/1.03  abstr_ref_under_cycles:                 0
% 1.72/1.03  gc_basic_clause_elim:                   0
% 1.72/1.03  forced_gc_time:                         0
% 1.72/1.03  parsing_time:                           0.016
% 1.72/1.03  unif_index_cands_time:                  0.
% 1.72/1.03  unif_index_add_time:                    0.
% 1.72/1.03  orderings_time:                         0.
% 1.72/1.03  out_proof_time:                         0.009
% 1.72/1.03  total_time:                             0.235
% 1.72/1.03  num_of_symbols:                         56
% 1.72/1.03  num_of_terms:                           4771
% 1.72/1.03  
% 1.72/1.03  ------ Preprocessing
% 1.72/1.03  
% 1.72/1.03  num_of_splits:                          6
% 1.72/1.03  num_of_split_atoms:                     3
% 1.72/1.03  num_of_reused_defs:                     3
% 1.72/1.03  num_eq_ax_congr_red:                    19
% 1.72/1.03  num_of_sem_filtered_clauses:            1
% 1.72/1.03  num_of_subtypes:                        0
% 1.72/1.03  monotx_restored_types:                  0
% 1.72/1.03  sat_num_of_epr_types:                   0
% 1.72/1.03  sat_num_of_non_cyclic_types:            0
% 1.72/1.03  sat_guarded_non_collapsed_types:        0
% 1.72/1.03  num_pure_diseq_elim:                    0
% 1.72/1.03  simp_replaced_by:                       0
% 1.72/1.03  res_preprocessed:                       140
% 1.72/1.03  prep_upred:                             0
% 1.72/1.03  prep_unflattend:                        40
% 1.72/1.03  smt_new_axioms:                         0
% 1.72/1.03  pred_elim_cands:                        4
% 1.72/1.03  pred_elim:                              4
% 1.72/1.03  pred_elim_cl:                           1
% 1.72/1.03  pred_elim_cycles:                       8
% 1.72/1.03  merged_defs:                            0
% 1.72/1.03  merged_defs_ncl:                        0
% 1.72/1.03  bin_hyper_res:                          0
% 1.72/1.03  prep_cycles:                            4
% 1.72/1.03  pred_elim_time:                         0.028
% 1.72/1.03  splitting_time:                         0.
% 1.72/1.03  sem_filter_time:                        0.
% 1.72/1.03  monotx_time:                            0.001
% 1.72/1.03  subtype_inf_time:                       0.
% 1.72/1.03  
% 1.72/1.03  ------ Problem properties
% 1.72/1.03  
% 1.72/1.03  clauses:                                32
% 1.72/1.03  conjectures:                            3
% 1.72/1.03  epr:                                    3
% 1.72/1.03  horn:                                   20
% 1.72/1.03  ground:                                 9
% 1.72/1.03  unary:                                  4
% 1.72/1.03  binary:                                 5
% 1.72/1.03  lits:                                   88
% 1.72/1.03  lits_eq:                                19
% 1.72/1.03  fd_pure:                                0
% 1.72/1.03  fd_pseudo:                              0
% 1.72/1.03  fd_cond:                                3
% 1.72/1.03  fd_pseudo_cond:                         0
% 1.72/1.03  ac_symbols:                             0
% 1.72/1.03  
% 1.72/1.03  ------ Propositional Solver
% 1.72/1.03  
% 1.72/1.03  prop_solver_calls:                      30
% 1.72/1.03  prop_fast_solver_calls:                 1260
% 1.72/1.03  smt_solver_calls:                       0
% 1.72/1.03  smt_fast_solver_calls:                  0
% 1.72/1.03  prop_num_of_clauses:                    1918
% 1.72/1.03  prop_preprocess_simplified:             6197
% 1.72/1.03  prop_fo_subsumed:                       30
% 1.72/1.03  prop_solver_time:                       0.
% 1.72/1.03  smt_solver_time:                        0.
% 1.72/1.03  smt_fast_solver_time:                   0.
% 1.72/1.03  prop_fast_solver_time:                  0.
% 1.72/1.03  prop_unsat_core_time:                   0.
% 1.72/1.03  
% 1.72/1.03  ------ QBF
% 1.72/1.03  
% 1.72/1.03  qbf_q_res:                              0
% 1.72/1.03  qbf_num_tautologies:                    0
% 1.72/1.03  qbf_prep_cycles:                        0
% 1.72/1.03  
% 1.72/1.03  ------ BMC1
% 1.72/1.03  
% 1.72/1.03  bmc1_current_bound:                     -1
% 1.72/1.03  bmc1_last_solved_bound:                 -1
% 1.72/1.03  bmc1_unsat_core_size:                   -1
% 1.72/1.03  bmc1_unsat_core_parents_size:           -1
% 1.72/1.03  bmc1_merge_next_fun:                    0
% 1.72/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.72/1.03  
% 1.72/1.03  ------ Instantiation
% 1.72/1.03  
% 1.72/1.03  inst_num_of_clauses:                    615
% 1.72/1.03  inst_num_in_passive:                    162
% 1.72/1.03  inst_num_in_active:                     421
% 1.72/1.03  inst_num_in_unprocessed:                32
% 1.72/1.03  inst_num_of_loops:                      490
% 1.72/1.03  inst_num_of_learning_restarts:          0
% 1.72/1.03  inst_num_moves_active_passive:          64
% 1.72/1.03  inst_lit_activity:                      0
% 1.72/1.03  inst_lit_activity_moves:                0
% 1.72/1.03  inst_num_tautologies:                   0
% 1.72/1.03  inst_num_prop_implied:                  0
% 1.72/1.03  inst_num_existing_simplified:           0
% 1.72/1.03  inst_num_eq_res_simplified:             0
% 1.72/1.03  inst_num_child_elim:                    0
% 1.72/1.03  inst_num_of_dismatching_blockings:      89
% 1.72/1.03  inst_num_of_non_proper_insts:           589
% 1.72/1.03  inst_num_of_duplicates:                 0
% 1.72/1.03  inst_inst_num_from_inst_to_res:         0
% 1.72/1.03  inst_dismatching_checking_time:         0.
% 1.72/1.03  
% 1.72/1.03  ------ Resolution
% 1.72/1.03  
% 1.72/1.03  res_num_of_clauses:                     0
% 1.72/1.03  res_num_in_passive:                     0
% 1.72/1.03  res_num_in_active:                      0
% 1.72/1.03  res_num_of_loops:                       144
% 1.72/1.03  res_forward_subset_subsumed:            71
% 1.72/1.03  res_backward_subset_subsumed:           0
% 1.72/1.03  res_forward_subsumed:                   0
% 1.72/1.03  res_backward_subsumed:                  0
% 1.72/1.03  res_forward_subsumption_resolution:     0
% 1.72/1.03  res_backward_subsumption_resolution:    0
% 1.72/1.03  res_clause_to_clause_subsumption:       253
% 1.72/1.03  res_orphan_elimination:                 0
% 1.72/1.03  res_tautology_del:                      68
% 1.72/1.03  res_num_eq_res_simplified:              0
% 1.72/1.03  res_num_sel_changes:                    0
% 1.72/1.03  res_moves_from_active_to_pass:          0
% 1.72/1.03  
% 1.72/1.03  ------ Superposition
% 1.72/1.03  
% 1.72/1.03  sup_time_total:                         0.
% 1.72/1.03  sup_time_generating:                    0.
% 1.72/1.03  sup_time_sim_full:                      0.
% 1.72/1.03  sup_time_sim_immed:                     0.
% 1.72/1.03  
% 1.72/1.03  sup_num_of_clauses:                     95
% 1.72/1.03  sup_num_in_active:                      82
% 1.72/1.03  sup_num_in_passive:                     13
% 1.72/1.03  sup_num_of_loops:                       96
% 1.72/1.03  sup_fw_superposition:                   32
% 1.72/1.03  sup_bw_superposition:                   83
% 1.72/1.03  sup_immediate_simplified:               42
% 1.72/1.03  sup_given_eliminated:                   0
% 1.72/1.03  comparisons_done:                       0
% 1.72/1.03  comparisons_avoided:                    60
% 1.72/1.03  
% 1.72/1.03  ------ Simplifications
% 1.72/1.03  
% 1.72/1.03  
% 1.72/1.03  sim_fw_subset_subsumed:                 19
% 1.72/1.03  sim_bw_subset_subsumed:                 2
% 1.72/1.03  sim_fw_subsumed:                        16
% 1.72/1.03  sim_bw_subsumed:                        0
% 1.72/1.03  sim_fw_subsumption_res:                 0
% 1.72/1.03  sim_bw_subsumption_res:                 0
% 1.72/1.03  sim_tautology_del:                      0
% 1.72/1.03  sim_eq_tautology_del:                   0
% 1.72/1.03  sim_eq_res_simp:                        1
% 1.72/1.03  sim_fw_demodulated:                     1
% 1.72/1.03  sim_bw_demodulated:                     15
% 1.72/1.03  sim_light_normalised:                   9
% 1.72/1.03  sim_joinable_taut:                      0
% 1.72/1.03  sim_joinable_simp:                      0
% 1.72/1.03  sim_ac_normalised:                      0
% 1.72/1.03  sim_smt_subsumption:                    0
% 1.72/1.03  
%------------------------------------------------------------------------------
